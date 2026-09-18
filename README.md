# lean-merge

本地合并两份 Lean 代码：第一份包含尚未完成的定理，第二份提供该定理的完整证明，可带辅助定义和引理。工具替换指定定理，补入证明需要的依赖，并用 Lean 重新检查输出。

实现参考 AXLE 公开的 [merge 文档](https://github.com/AxiomMath/axiom-lean-engine/blob/main/docs/tools/merge.md) 和 [normalize 文档](https://github.com/AxiomMath/axiom-lean-engine/blob/main/docs/tools/normalize.md)。这是独立实现，不调用 AXLE 服务，不需要 API key，也不声称与闭源后端完全兼容。

## 使用

需要 Python 3.10+ 和 Lean。仓库默认使用 Lean 4.26.0；另已在 Lean 4.30.0-rc2 的 Mathlib 项目中验证 `ring` 证明。Python 无第三方依赖。输入依赖 Mathlib 时，指定已经安装并构建相应依赖的 Lake 项目。

```bash
python3 lean_merge.py merge examples/Base.lean examples/Proof.lean \
  --target Demo.target --proof solution -o Merged.lean
lean Merged.lean
```

处理自己的文件：

```bash
python3 lean_merge.py merge Base.lean Proof.lean \
  --target MyNamespace.my_theorem \
  --project /path/to/your/lake/project -o Merged.lean
```

`--target` 接受完整名字或无歧义的短名。不指定时，第一份文件必须只有一个传递依赖含 `sorry` 的定理。`--proof` 指定第二份文件中的证明；省略时比较候选定理的类型，优先同名候选，遇到多个匹配则要求明确选择。

第二份文件需要能独立通过 Lean 检查，可以只有 theorem 声明，也可以带 imports、namespace、section、辅助声明。仅有 `by ...` 的证明体需要先包成 theorem。两份文件使用同一套 Lean 和依赖版本。

```bash
# 输出 JSON，包含 content、target、proof、inserted、reused、axioms、verified。
python3 lean_merge.py merge Base.lean Proof.lean --target foo --json

# 标准输入；至多一个输入为 -。
python3 lean_merge.py merge Base.lean - --target foo < Proof.lean

# 单独导出规范化的定理及其依赖。
python3 lean_merge.py normalize Proof.lean --target solution -o Normalized.lean
```

合并内部已经做了规范化，不需要先执行 `normalize`。`-o` 指定的文件只在验证成功后写入；已有文件需要 `--force`，输入文件不可用作输出。默认总超时为 120 秒，可用 `--timeout` 调整。`--lean` 可指定 Lean 可执行文件。

## Python API

```python
from lean_merge import merge, normalize, MergeError

result = merge(
    "theorem target (n : Nat) : n = n := sorry",
    "theorem solution (m : Nat) : m = m := rfl",
    target="target",
    proof="solution",
    timeout=120,
)
print(result["content"])
assert result["verified"]
```

函数参数为代码字符串。可传 `project="/path/to/project"`、`lean="/path/to/lean"` 和 `use_def_eq=False`。失败抛出 `MergeError`；CLI 失败返回非零退出码。

## 合并过程

1. 使用 Lean parser 和 elaborator 分别分析输入，获取声明对应的源码范围、内核类型和证明表达式。
2. 在目标声明之前的环境中迁移候选证明。按表达式中的常量引用递归处理依赖，先处理依赖再处理使用它的声明。
3. 同名定理类型相等且第一份已有完整证明时复用。定义必须同时具有相等的类型和定义值；其余依赖分配无冲突的新名字。默认用 Lean 的 definitional equality 比较类型，`--no-def-eq` 改用结构比较。
4. 将展开后的闭合表达式打印成 Lean 声明。参数和 universe 显式化，局部变量、namespace、notation 和 tactics 不需要随证明搬运。目标之外的原始源码保留，缺少的 imports 补到文件头；如果新增 imports 改变了原有声明的类型或定义值，则拒绝合并。输入的 CRLF 换行统一为 LF。
5. 重新展开整个结果，确认目标类型不变，并递归收集证明公理。目标不可依赖 `sorryAx` 或自定义公理，仅允许 `propext`、`Classical.choice`、`Quot.sound`。

`verified` 表示本次指定的目标证明通过上述检查，不表示文件里其他所有 `sorry` 都已解决。未选中的 `sorry` 会保留。Lean 源码可执行宏和编译期代码，本工具应处理可信代码，不提供执行沙箱。

## 当前边界

- 一次合并一个目标，支持 theorem/lemma、不同证明名、不同参数名、namespace/section、universe，以及 def/abbrev/instance/opaque 和私有辅助引理依赖。
- 输入允许显式 `sorry`，但不接受语法或 elaboration 错误。
- 不迁移文件内新声明的 structure/inductive 及其生成声明，也不迁移本地 axiom、unsafe/partial 定义。公共结构和实例可放进两份文件共同导入的模块。私有目标定理和新版 `module` 语法暂不支持。
- 不重排第一份文件已有声明。位于目标之后的声明不能直接作为目标的依赖；第二份文件提供其完整定义时可以迁移副本。
- Lean delaborator 不能保证所有表达式都往返成功。不能重新展开或不能确认类型一致时，命令失败，不输出未经验证的结果。
- Lean 内部 API 随版本变化；遇到后端编译错误，应使用已验证的工具链，或为对应版本调整后端。不会把不同 Lean 版本的 `.olean` 混用。

## 测试

```bash
python3 -m unittest discover -s tests -v

# 在已经构建 Mathlib 的项目里验证 ring 证明。
LEAN_MERGE_TEST_PROJECT=/path/to/project \
  python3 -m unittest discover -s tests -k mathlib_project -v
```

测试覆盖参数和命名空间处理、定义复用与冲突、辅助证明依赖、间接 sorry、自定义公理拒绝、类型比较、候选歧义、规范化后再合并，以及失败时输出文件不变。
