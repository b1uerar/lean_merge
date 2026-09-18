"""Local, kernel-checked replacement of a Lean theorem's unfinished proof."""

from __future__ import annotations

import argparse
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time


WORKER = Path(__file__).resolve().with_name("LeanMerge.lean")


class MergeError(Exception):
    """The inputs could not be merged and verified."""


def find_project(source: Path) -> Path | None:
    for directory in (source.parent, *source.parent.parents):
        if any((directory / file).is_file() for file in ("lakefile.lean", "lakefile.toml")):
            return directory
    return None


class Runner:
    def __init__(self, timeout: float, cwd: Path):
        if not math.isfinite(timeout) or timeout <= 0:
            raise MergeError("timeout must be finite and positive")
        self.deadline = time.monotonic() + timeout
        self.cwd = cwd
        self.env = dict(os.environ)

    def run(self, argv: list[str]) -> str:
        remaining = self.deadline - time.monotonic()
        if remaining <= 0:
            raise MergeError("Lean operation timed out")
        with subprocess.Popen(
            argv, cwd=self.cwd, env=self.env, text=True, encoding="utf-8",
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True,
        ) as process:
            try:
                stdout, stderr = process.communicate(timeout=remaining)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.communicate()
                raise MergeError("Lean operation timed out") from None
        if process.returncode:
            raise MergeError((stderr + stdout).strip() or f"Command failed: {argv[0]}")
        return stdout


def _execute(
    mode: str, base: str, donor: str = "", *, target: str | None = None,
    proof: str | None = None, project: str | Path | None = None,
    lean: str = "lean", timeout: float = 120, use_def_eq: bool = True,
    source_path: Path | None = None,
) -> dict:
    origin = source_path or Path.cwd() / "Input.lean"
    project_path = Path(project).expanduser().resolve() if project else find_project(origin)
    if project_path and not any((project_path / name).is_file() for name in ("lakefile.lean", "lakefile.toml")):
        raise MergeError(f"No Lake project at {project_path}")
    runner = Runner(timeout, project_path or origin.parent)
    executable = shutil.which(lean)
    if executable is None:
        raise MergeError(f"Lean executable not found: {lean}")
    prefix = Path(runner.run([executable, "--print-prefix"]).strip())
    executable = str(prefix / "bin" / "lean")
    version = runner.run([executable, "--version"]).strip()
    runner.env["PATH"] = str(prefix / "bin") + os.pathsep + runner.env.get("PATH", "")
    runner.env["LEAN_SYSROOT"] = str(prefix)
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="lean-merge-") as directory:
        work = Path(directory)
        setup = None
        if project_path:
            lake = str(prefix / "bin" / "lake")
            # setup-file resolves module artifacts and plugins for the actual imports.
            for index, content in enumerate([base] + ([donor] if donor else [])):
                setup_source = work / f"Input{index}.lean"
                setup_source.write_text(content, encoding="utf-8")
                current = json.loads(runner.run([lake, "setup-file", str(setup_source)]))
                if setup is None:
                    setup = current
                else:
                    setup.setdefault("importArts", {}).update(current.get("importArts", {}))
                    for key in ("dynlibs", "plugins"):
                        setup[key] = list(dict.fromkeys(setup.get(key, []) + current.get(key, [])))
            runner.env = json.loads(runner.run([
                lake, "env", sys.executable, "-c",
                "import json, os; print(json.dumps(dict(os.environ)))",
            ]))
        request_path = work / "request.json"
        result_path = work / "result.json"
        request = {
            "mode": mode, "base": base.replace("\r\n", "\n"),
            "donor": donor.replace("\r\n", "\n"), "target": target or "",
            "proof": proof or "", "useDefEq": use_def_eq,
            "result": str(result_path), "setup": setup,
        }
        request_path.write_text(json.dumps(request, ensure_ascii=False), encoding="utf-8")
        runner.run([executable, "--run", str(WORKER), str(request_path)])
        result = json.loads(result_path.read_text(encoding="utf-8"))
    if not result.get("okay") or not result.get("verified"):
        raise MergeError("Lean worker did not confirm verification")
    result["lean_version"] = version
    result["timings"] = {"total_ms": round((time.monotonic() - started) * 1000)}
    return result


def merge(base: str, donor: str, **options) -> dict:
    """Replace one unfinished theorem, returning verified Lean source and metadata."""
    return _execute("merge", base, donor, **options)


def normalize(content: str, **options) -> dict:
    """Export closed theorem terms and their dependencies, then re-elaborate them."""
    return _execute("normalize", content, **options)


def publish(path: Path, content: str, force: bool) -> None:
    if path.is_symlink():
        raise MergeError("Output must not be a symbolic link")
    with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".lean-merge-", delete=False) as file:
        staged = Path(file.name)
        file.write(content.encode("utf-8"))
    try:
        if force:
            os.replace(staged, path)
        else:
            os.link(staged, path)
    finally:
        staged.unlink(missing_ok=True)


def read_source(name: str) -> str:
    return sys.stdin.read() if name == "-" else Path(name).read_bytes().decode("utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="mode", required=True)
    for mode in ("merge", "normalize"):
        command = subparsers.add_parser(mode)
        command.add_argument("base", help="Lean source file, or - for stdin")
        if mode == "merge":
            command.add_argument("donor", help="Lean file containing the proof, or - for stdin")
            command.add_argument("--proof", help="donor theorem name; inferred by type if omitted")
        command.add_argument("--target", help="target theorem name; fully qualified if ambiguous")
        command.add_argument("-o", "--output", type=Path, help="write Lean source here; defaults to stdout")
        command.add_argument("--project", type=Path, help="Lake project, including built Mathlib dependencies")
        command.add_argument("--lean", default="lean", help="Lean executable; defaults to the project's toolchain")
        command.add_argument("--timeout", type=float, default=120, help="total timeout in seconds")
        command.add_argument("--no-def-eq", action="store_true", help="require structural type equality")
        command.add_argument("--json", action="store_true", help="print structured result instead of Lean source")
        command.add_argument("--force", action="store_true", help="replace an existing output after verification")
    args = parser.parse_args(argv)
    try:
        inputs = [args.base] + ([args.donor] if args.mode == "merge" else [])
        if inputs.count("-") > 1:
            raise MergeError("Only one input may read stdin")
        output = args.output.expanduser().absolute() if args.output else None
        if output:
            for name in inputs:
                if name != "-" and (output.resolve() == Path(name).resolve() or
                    (output.exists() and os.path.samefile(output, name))):
                    raise MergeError("Output must differ from both input files, including with --force")
            if output.is_symlink():
                raise MergeError("Output must not be a symbolic link")
            if output.exists() and not args.force:
                raise MergeError(f"Output exists: {output}; use --force to replace it")
        result = _execute(
            args.mode, read_source(args.base),
            read_source(args.donor) if args.mode == "merge" else "",
            target=args.target, proof=getattr(args, "proof", None),
            project=args.project, lean=args.lean, timeout=args.timeout,
            use_def_eq=not args.no_def_eq,
            source_path=Path(args.base).resolve() if args.base != "-" else None,
        )
        if output:
            publish(output, result["content"], args.force)
        if args.json:
            print(json.dumps(result, ensure_ascii=False, indent=2))
        elif not output:
            print(result["content"], end="")
        else:
            print(f"Verified: {output}", file=sys.stderr)
        return 0
    except (MergeError, OSError, ValueError) as error:
        if args.json:
            print(json.dumps({"okay": False, "errors": [str(error)]}, ensure_ascii=False))
        else:
            print(f"lean-merge: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
