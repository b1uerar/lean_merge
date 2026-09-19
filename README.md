# lean-merge

本地合并两份 Lean 代码：第一份包含尚未完成的定理，第二份提供该定理的完整证明，可带辅助定义和引理。工具替换指定定理，补入证明需要的依赖，并用 Lean 重新检查输出。

参考了AXLE公开的部分信息。

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

`--target` 接受完整名字或无歧义的短名。不指定时，第一份文件必须只有一个自身证明含 `sorry` 的定理。`--proof` 指定第二份文件中的证明；省略时比较候选定理的类型，优先同名候选，遇到多个匹配则要求明确选择。同名比较保留 namespace，私有声明忽略 Lean 添加的内部模块前缀。

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

后端从候选目标的内核表达式递归迁移依赖，复用等价声明，为冲突依赖分配新名字。局部 notation、section、参数改名和 `where` 通过 elaboration 后的表达式处理，提交的 tactic 源码和无关新增命令不会搬入。返回 `source`、`content`、`added_commands`、`strategy="expression"` 和 `verified`。`added_commands` 记录实际插入命令产生的全部声明，包括构造器和 recursor，供调用方清理生成内容。

输出保留当前文件其他源码和 CRLF 换行约定。整个结果经 Lean 重新检查，原有声明的类型和定义值必须保持不变，目标不能依赖 `sorry` 或非白名单公理。原有已完成定理也不能因新增 imports 或辅助声明而变成依赖 `sorry` 或非白名单公理。无法可靠重打印或不能通过检查时返回错误。

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
3. 同名定理类型相等且第一份已有完整证明时复用。定义必须同时具有相等的类型和定义值；其余依赖分配无冲突的新名字。私有依赖可按完整的用户可见名字匹配，但只在候选唯一且上述检查通过时复用。默认用 Lean 的 definitional equality 比较类型，`--no-def-eq` 改用结构比较。
4. 将较大的子表达式提取成辅助声明，闭包化局部变量和 universe，并复用相同的辅助声明，避免打印时反复展开共享表达式。证明使用 theorem，数据使用可归约的 def；含 sorry 的证明保留在原声明中。打印保留完整证明和显式参数，省略可由上下文恢复的 lambda、let 类型标注。启用 `pp.beta` 化简匿名函数应用，避免带隐式参数的 `(@fun ...) args` 打印结果无法重新编译。目标之外的原始源码保留，缺少的 imports 补到文件头；如果新增 imports 改变了原有声明的类型或定义值，则拒绝合并。保留主文件的 CRLF 换行约定。
5. 重新展开整个结果，确认目标及其他原有声明的类型、定义值不变，并递归收集证明公理。目标和全部新增声明共用已访问集合，避免重复遍历依赖。检查原有定理时，合并前后各维护一个已访问集合，仅复用通过公理检查的遍历结果，避免连续合并后反复检查数千个辅助定理的共享依赖。目标不可依赖 `sorryAx` 或自定义公理，仅允许 `propext`、`Classical.choice`、`Quot.sound`。

`verified` 表示本次指定的目标证明通过上述检查，不表示文件里其他所有 `sorry` 都已解决。未选中的 `sorry` 会保留。Lean 源码可执行宏和编译期代码，本工具应处理可信代码，不提供执行沙箱。

## 当前边界

- 一次合并一个目标，支持 theorem/lemma、不同证明名、不同参数名、namespace/section、universe，以及 def/abbrev/instance/opaque 和私有辅助引理依赖。
- `mutual` 块按具体定理定位，保留并检查块内其他声明。带显式 `include` 参数的多定理块会保留目标的原声明头，并引用规范化的证明辅助声明。`normalize` 未指定目标时导出所有显式声明的非私有定理，包括 `mutual` 块内的定理。
- 输入允许显式 `sorry`，但不接受语法或 elaboration 错误。
- 支持迁移 structure/inductive、互递归类型及其构造器和 recursor，也支持私有目标。不支持迁移本地 axiom、unsafe/partial 定义和新版 `module` 语法。
- 不重排第一份文件已有声明。位于目标之后的声明不能直接作为目标的依赖；第二份文件提供其完整定义时可以迁移副本。
- Lean delaborator 不能保证所有表达式都往返成功。不能重新展开或不能确认类型一致时，命令失败，不输出未经验证的结果。
- Lean 内部 API 随版本变化；遇到后端编译错误，应使用已验证的工具链，或为对应版本调整后端。不会把不同 Lean 版本的 `.olean` 混用。

## 测试

```bash
python3 -m unittest discover -s tests -v

# 在已经构建 Mathlib 的项目里验证 ring 证明。
LEAN_MERGE_TEST_PROJECT=/path/to/project \
  python3 -m unittest discover -s tests -k mathlib_project -v

# 真实超时案例：Brualdi、EGMO 的三份候选及连续合并。
LEAN_MERGE_TEST_PROJECT=/path/to/project \
  python3 -m unittest discover -s tests -p test_real_cases.py -v
```

测试覆盖参数和命名空间处理、私有依赖复用与冲突、辅助证明依赖、间接 sorry、自定义公理拒绝、已有证明退化检查、类型比较、私有候选选择、mutual 定位与作用域、规范化后再合并，以及失败时输出文件不变。
