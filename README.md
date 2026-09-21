# lean-merge

合并两份 Lean 源码。默认用第二份的证明补完第一份中的一个定理。也可仅合入声明，第二份无需提供与第一份 `sorry` 对应的证明。工具按依赖安排已有命令的顺序，保留原来的 tactic、定义体、notation 和注释，不展开或重新打印证明表达式，不生成 `LeanMergeAux` 声明。

## 使用

需要 Python 3.10+ 和 Lean，默认工具链为 Lean 4.26.0。使用 Mathlib 时指定已构建依赖的 Lake 项目。

```bash
python3 lean_merge.py merge examples/Base.lean examples/Proof.lean \
  --target Demo.target --proof solution -o Merged.lean

python3 lean_merge.py merge Base.lean Proof.lean \
  --target MyNamespace.my_theorem --project /path/to/project --json

# 只合入声明，保留第一份的证明和 sorry，不要求存在匹配的目标。
python3 lean_merge.py merge Base.lean Helpers.lean --declarations-only -o Merged.lean

# 保留兼容命令名，实际提取原始源码及依赖，不再规范化表达式。
python3 lean_merge.py normalize Proof.lean --target solution -o Extracted.lean
```

默认模式下，`--target` 接受完整名字或无歧义的短名。省略时，主文件必须只有一个自身证明含 `sorry` 的定理。`--proof` 指定候选证明；省略时优先使用同名证明，其余候选中有多个可用证明则报错。

`--declarations-only` 合入第二份的全部声明，不选择或替换目标，也可用于第一份没有 `sorry` 或有多个 `sorry` 的情况。它不能与 `--target` 或 `--proof` 同时使用。同名声明通过等价性检查后复用第一份的版本，包括已有的未完成定理；即使第二份已证明该定理，此模式也保留第一份的占位。两份代码各自放在 `section` 内，隔离局部变量、notation、选项和 `open`。

输入必须能独立通过 Lean 检查，可以含未完成的声明。两份输入使用相同工具链和依赖版本。至多一个输入可以用 `-` 从标准输入读取。

输出只在验证成功后写入。覆盖已有文件需要 `--force`，不能覆盖输入文件。默认总超时为 120 秒，可用 `--timeout` 调整，`--lean` 可指定 Lean 可执行文件。

## 证明合并规则

1. Lean parser 提供原始命令的范围。内核表达式、elaboration 引用和 tactic trace 用于识别依赖与检查等价性，不用于生成源码。
2. 从选中证明收集依赖，同时保留所需的作用域、变量、notation、宏和属性命令。未使用的声明不搬入。对无法追踪的环境修改，保守保留前置命令。
3. 同名且等价的声明复用主文件版本。定义必须类型和值均相等，归纳类型还检查构造器和 recursor。已完成的主文件定理可以替代提交文件中的同名占位证明。依赖中的名字冲突会报错，需要在提交源码中修正。
4. 用提交文件的原始定理声明替换目标，保留目标的文档和属性。证明名字不同时只调整声明名，参数名、语句和证明体沿用提交源码。依赖按源文件中的顺序搬入，通过 `section` 隔离提交文件的局部设置。主文件中需要的已有声明连同原始作用域移到证明之前，作用域边界按需重用；`mutual` 依赖作为整条命令处理。
5. 完整输出重新通过 Lean 检查。目标类型、其他原有声明的类型和定义值必须保持等价；已完成的原有定理不能退化。目标及新增声明不得依赖 `sorryAx` 或自定义公理，只允许 `propext`、`Classical.choice`、`Quot.sound`。

`verified` 只表示本次指定目标和新增内容通过检查，不表示主文件中其他 `sorry` 已解决。源码保留主文件的 CRLF 换行约定。

仅合入声明时，同样检查 imports、名字冲突、原有声明的类型和定义值，并重新验证完整输出。所有新增声明都必须通过公理检查，不允许新增未完成声明或依赖原有 `sorry` 的声明。此模式的 `verified` 表示合并及新增声明通过检查，不表示原有待证明目标已完成。

若依赖与目标形成循环，或原始命令无法在合并环境中重新通过检查，工具返回错误。不会回退到证明表达式展开。不同名字的递归定理、共享隐式 universe 的 `mutual` 定理，以及含混合新旧声明的单个命令可能需要调用方先调整源码。指定的证明本身必须有完整源码，只有辅助依赖允许使用主文件的已完成证明替代占位。新版 `module` 语法暂不支持。

## Python API

```python
from lean_merge import merge, normalize, MergeError

result = merge(
    "theorem target (n : Nat) : n = n := sorry",
    "theorem solution (m : Nat) : m = m := by rfl",
    target="target",
    proof="solution",
    timeout=120,
)
print(result["content"])
assert result["verified"]
assert result["strategy"] == "source"

# 第二份只有辅助定义，没有与 target 匹配的证明。
result = merge(
    "theorem target : False := sorry",
    "def twice (n : Nat) := n + n",
    declarations_only=True,
)
assert result["target"] is None
assert "twice" in result["inserted"]
```

参数为源码字符串。可传 `project`、`lean`、`timeout` 和 `use_def_eq=False`，最后一项要求结构类型相等。失败抛出 `MergeError`，CLI 返回非零退出码。

合并结果含 `source`、`content`、`target`、`proof`、`inserted`、`reused`、`axioms`、`verified` 和 `strategy="source"`。`added_commands` 记录新增命令的原文及其产生的声明，包括构造器和 recursor，供调用方清理依赖。

仅合入声明时，结果还包含 `declarations_only=true`，`target` 和 `proof` 均为 `null`，`axioms` 记录新增声明的公理依赖。

## 测试

```bash
python3 -m unittest discover -s tests -v

LEAN_MERGE_TEST_PROJECT=/path/to/project \
  python3 -m unittest discover -s tests -p test_real_cases.py -v
```

真实案例包含 Brualdi、EGMO 的三份证明及连续合并，检查输出规模、完整源码编译和公理依赖。

## 失败记录

Python 命令行或 API 执行失败时，会在本工具目录的 `failures/` 下新建一个带 UTC 时间和随机后缀的目录，保存输入 Lean 代码、已有的临时请求和结果文件，以及 `failure.json` 和 `error.txt`。提取工具还会保存已生成的 `candidate.lean`；合并工具会分别保存 `base.lean` 和 `donor.lean`。`failure.json` 包含调用参数、原始路径和错误信息，归档路径打印到 stderr。

成功时不创建记录。失败记录不会覆盖输入或已有输出，已加入 Git 忽略规则，可在修复后手动删除。归档写入失败时只打印提示，仍返回原始错误。AgentProver 的沙箱调用由宿主进程在同一位置保存记录；直接使用 `lean --run` 运行内部 Lean 文件不经过 Python 归档入口。

设置 `LEAN_TOOL_FAILURE_ARCHIVE=0` 可关闭失败归档。测试套件自动设置此开关，避免预期失败写入工具目录；归档功能的专用测试仅在临时目录中启用归档。
