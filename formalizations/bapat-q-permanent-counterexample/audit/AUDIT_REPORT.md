# Bapat 原猜想 Lean 证据包独立审核

日期：2026-10-08 UTC。

## 结论

**PASS，范围为完整静态语义、证据包完整性与映射、全部导出依赖图和独立整数证书复算。没有发现阻断最终原猜想否定的数学语义错误或证据内部矛盾。**

本审核没有安装或调用 Lean，也没有再次 fresh 编译或内核重放。原执行环境于 2026-10-08 12:47:17 至 12:55:42 UTC 完成的 fresh 编译和 trust-level-0 回放，是本次核对的既有执行证据；本次独立产生的是 Python 标准库机械核验、全部 201 个 checkpoint 的逐系数整数复算和源码语义审查。不能把两者写成审核者自己完成了第二次 Lean 内核验证。

审核对象的最终定理是 `BapatRankTwo.N200.originalBapatConjecture_false`。其数学范围是复 Hermitian 正定、非对角矩阵的 q-permanent 在原区间 `[-1,1]` 严格递增的普遍断言。具体反例命题给出 200 阶 Gram 矩阵的某个正实数对角扰动，以及两个严格位于 `(-1,1)` 且 `q₁<q₂` 的点，其函数值严格下降。

## 输入和不可混淆的版本

本次独立核对了两个实际本地档案的全部字节并安全解包。拒绝绝对路径、越界路径、符号链接、硬链接与设备成员；两个档案没有这类成员。

| 档案 | 字节数 | SHA-256 |
|---|---:|---|
| `bapat_n200_lean_evidence_20261008_compact.tar.gz` | 8022381 | `499d5391a0989f68a2cbc49acebd3af92911bf967b0769f60c0fbc7c5099928e` |
| `bapat_n200_lean_evidence_20261008_public.tar.gz` | 74240483 | `2d2092431af5ceb155b6483ae8323e25d4b9defc2a81a67c05e71fcbdfafd91d` |

精简包是可复现的机械投影，不是原全包的原字节副本，也不是重新执行内核后产生的新运行。

- 原公共包有 196 个文件，共 297753838 个未压缩字节。
- 精简包有 141 个文件；140 个非校验表文件全部在其 SHA256SUMS 中。
- 196 个原文件的映射为：87 个保留、43 个元数据替换、22 份重复源码去重、44 个可重建 `.olean`/`.ilean` 省略。
- 省略产物共 250393677 字节；原产物仍在全包中，本次实际核过其哈希。
- 每个保留或去重文件逐字节一致；压缩图解压后逐字节一致。
- 对每个元数据替换文件，从原全包恢复并核验全部 10 个原文字串的 SHA-256，按声明顺序作字面替换，再执行声明的 JSON pid 行删除，结果与精简包逐字节一致。每条替换的次数也完全吻合。
- 原公共包 SHA256SUMS、原 fresh 运行的 SHA256SUMS、精简包 SHA256SUMS 均全覆盖且匹配。本次共校验了原 fresh 运行的 128 个受表覆盖文件。

`archive_checks.json`、`audit_results.json` 中 `provenance` 给出机器结果。该对应仅建立原公共包到精简包的关系；未取得另一个 execution 档案并重新核对其全部原始字节，不能把它的标注哈希升级为本次已独立检查的第三个档案。

## 数学语义

详见 `semantic_audit.md`，其中逐桥给出 22 模块的源码行号。核心核查如下。

1. `qPermanent` 真正对 `Equiv.Perm (Fin n)` 的全部置换求和，权重是原索引顺序的真实逆序数，乘积是 `A i (σ i)`。不存在替代函数、抽样和、任意权函数或重排后改变的逆序数。
2. 对 Hermitian 矩阵和实 q，另有逆排列配对证明 q-permanent 为实数，并与实多项式取值一致。因此原猜想使用实部的表达是准确的。
3. 标记逆序、两行固定像纤维、真实补集双射 permanent、一般及混合 Fischer 配对全部由源码内证明连接。关键恒等式不是额外公理或未证明接口。
4. 有序 `S` 是 `∑_{i<j}(a_i b_j-b_i a_j)∏_{r≠i,j}(a_r+b_r X)`。先证明真实有序和的追加递推，再连接整数列表；没有把有序对象悄悄当成无序对象。
5. 原始矩阵是全部 200 行输入的真实 `V V*`，是 PSD。`A[0,1]=398−i` 给出非对角证据。随后连续性产生严格正的 δ，`A+δI` 真正 PD，并保留非对角性。
6. 下降点严格处于开区间 `(-1,1)`，且严格有序。因此并非只在端点右侧、区间外、或仅 PSD 类中失败。

另从固定上游 commit 只读取回并保存了以下定义，核对 Git blob SHA 与实际返回字节：

- Lean commit `5045d0056413266e57c625dcd7c365b10e377c52` 的 `Environment.lean`、`Replay.lean`、`Util/FoldConsts.lean`。
- mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612` 的 `Matrix/PosDef.lean`、`Matrix/IsDiag.lean`、`Matrix/Hermitian.lean`、`Order/Monotone/Defs.lean`。

`Matrix.PosDef` 是 Hermitian 与每个非零向量二次型严格正的合取；`IsHermitian` 是共轭转置等于原矩阵；`IsDiag` 要求异索引项为零；`StrictMonoOn` 要求区间内任意严格有序点对应严格增大的函数值。来源固定链接、Git SHA、字节数及 SHA-256 均见 `upstream/UPSTREAM_MANIFEST.json`。

## 整数证书的独立复算

没有运行或信任包方整数脚本的计算结果作为前提。`audit_bundle.py` 使用独立实现的高斯整数运算和逐系数递推，从 CSV 重新计算。

- CSV 200 行逐坐标、逐顺序等于 Lean `vectors` 的 200 行。
- CSV 原字节 SHA-256 为 `9d16617d6eb287535a752cf5ef6f3d4672a133812bf0fbd908738a10c223fc25`。
- 初始 checkpoint 和后续全部 200 步共 201 个 checkpoint，每一个 F 与 S 高斯整数系数都与 Lean 源码完全相同。
- 200 个 `state_eq` 后继证明编号和前驱连接全部连续，使用 `decide +kernel`，没有 `native_decide`。
- 最终 F 有 201 项，S 列表有 200 项，最后一项为零。论文 S 的 199 项与前 199 项完全一致，因此 n−2 次 Fischer 权与尾零处理吻合。
- 直接计算 `P=||F||²`、`H=||S||²`、`D=H−19900P`。三者与论文 `independent_certificate.json` 的独立 pair-deletion 证书和 `expected_values.json` 全部相等。
- `P>0`、`D>0`；D 有 816 位十进制数字。精确整数比较验证 `23/1000 < D/(19900P) < 24/1000`。
- 另对前 n 行、n=2,…,7，枚举全部置换，独立计算 permanent、逆序加权导数，并验证 `2P′₁=binom(n,2)||F||²−||S||²`。这只是辅助小维测试，不替代一般恒等式的证明。

完整 P、H、D 及 200 步系数的规范 JSON SHA-256 记录在 `audit_results.json`。独立复算支持并检查了此实例的计算事实；Lean 内核证明并不调用这个 Python 脚本。

## 论文数据与固定 Git commit

论文数据固定于 `mxym/math` commit `c5d7f68e78b6c80912041c6cf1fd4d3cd950beb6`。本次检查 17 个 reference 下载文件的字节数、SHA-256、Git blob SHA-1，并与包中固定树记录一致。

此外，本次实际通过 GitHub 只读工具重新取得该 commit 的两个关键文件，原字节与证据包完全一致：

- [CSV](https://github.com/mxym/math/blob/c5d7f68e78b6c80912041c6cf1fd4d3cd950beb6/notes/bapat-q-permanent-counterexample/counterexample_vectors_n200.csv)，Git blob `a5e72ad89a659ef25db77abed17a0437676be683`。
- [证明原稿](https://github.com/mxym/math/blob/c5d7f68e78b6c80912041c6cf1fd4d3cd950beb6/notes/bapat-q-permanent-counterexample/proof.md)，Git blob `4e4a354dc3f4dd2f70e787604c9658f6702a18e5`。

## 所有声明及闭包

本次从导出图的 type、value 和 structural 三类直接边重新遍历，不仅相信 summary 中的总数。

| 项目 | 重算数量 |
|---|---:|
| 自有模块 | 22 |
| 自有声明 | 928 |
| 自有 theorem / definition | 639 / 289 |
| 全部自有声明的传递闭包 | 22371 |
| 六个指定根的闭包并集 | 21986 |
| 标准公理节点 | 3 |

所有节点名唯一，所有依赖端点存在，闭包没有游离多余节点；928 个自有声明的导出节点与 inventory 逐字段相同。分别重新计算每个自有声明的传递公理集合，与 inventory 全部吻合。

闭包中唯一公理是 `propext`、`Classical.choice`、`Quot.sound`。没有自有公理；没有 `sorryAx`、`Lean.ofReduceBool` 或其他额外公理。全部 22371 节点的 `unsafe` 和 `partial` 均为 false。源码中也没有 `sorry`、`admit`、`axiom`、`unsafe`、`partial`、`native_decide`、`implemented_by`、`extern` 的声明或执行入口。源码扫描只是辅助，不是用它代替依赖检查。

六根各自的闭包数：

| 根 | 闭包数 |
|---|---:|
| `BapatRankTwo.N200.originalBapatConjecture_false` | 21963 |
| `BapatRankTwo.N200.explicit_counterexample` | 21962 |
| `BapatRankTwo.N200.matrix_derivative_negative` | 13345 |
| `BapatRankTwo.rankTwo_fischer_inversion_identity` | 11748 |
| `BapatRankTwo.qPermanent_eq_ofReal_eval` | 9759 |
| `BapatRankTwo.N200.norm_gap_positive` | 1775 |

## 检查器是否真的要求空环境和 trust 0

本次对 `verifier/checks/OwnedAudit.template.lean` 与实际执行副本逐字节核对，并从模板和输入机械生成副本再次比较。三个控制源码哈希与运行清单吻合。

检查器：

- 由全部 22 个自有模块筛出 928 个声明，检查所有自有声明及全部闭包的安全标志和公理。
- 遍历声明类型和证明值的常量依赖，并补入归纳类型、构造子、递归器及互相递归定义的结构依赖。
- 在第 114 行执行 `mkEmptyEnvironment 0`；第 115–116 行确认基础环境中常量数为零。
- 第 117 行将全部闭包交给 `base.toKernelEnv.replay`。
- 第 118–121 行核对回放环境中每个声明存在，且类型和 universe parameters 与原声明相同。
- 所有这些步骤成功后才写 PASS summary。

固定 Lean 上游源码对应：`mkEmptyEnvironment` 建立空常量表并保留传入的 trust level；`Replay.addDecl` 将定义、定理、opaque 等送入 `addDeclCore`；归纳构造子和递归器与内核重建产物作一致性检查；`ConstantInfo.getUsedConstantsAsSet` 遍历类型以及包括 opaque 在内的值。

上游 replay 本身会跳过 unsafe/partial，但本检查器在调用前已拒绝任何此类闭包节点，并在调用后核对所有节点存在，所以这里没有利用该跳过行为漏验声明。检查器的 `partial def gather` 是审计遍历程序，不属于数学声明闭包中的不安全证明。

既有日志确有 `REPLAY_BEGIN all_owned=928 closure=22371; empty kernel trust=0` 和 `ALL_OWNED_EMPTY_KERNEL_REPLAY_PASS 22371`。负控真的构造了一个类型声称为 False、值却为 True.intro 的伪定理，并要求同一个空 trust-zero 内核以 type mismatch 拒绝。日志记录了所要求的具体错误。

以上是检查器源码意图、固定上游实现和记录之间的一致性审计，不等于本次亲自执行了回放，也不是对 Lean 内核实现本身进行形式验证。

## 既有执行日志及缓存界限

46 条命令按顺序对应 22 次编译、22 次依赖检查、1 次 owned audit/replay 和 1 次负控；全部记录 exit code 0，时间前后顺序一致，所指日志全部存在。所有自有依赖的路径指向本轮 fresh build，自有源码 hash 与冻结输入、正式源码及原全包中的运行快照一致。search path 以 fresh build 为首项；审核模块没有排除项。

**缓存检查的准确含义：** `shared_metadata` 对共享包目录中的相对路径、大小和 mtime_ns 做指纹，并跳过 `.git`。记录 before=after；这支持运行期间未见这些元数据改变。它不是逐文件内容哈希，不能表述为“整个共享缓存的字节内容已重验”。`doctor` 核对工具链提交号、包 HEAD 和 tracked dirty 状态，记录 Lean 二进制和共享运行库哈希；本次没有取得或重建这些二进制，也没有重建全部 mathlib。

公理 allowlist 核对的是三个名称；导出图给出它们的依赖常量名称，未单独导出和比较三个实际载入公理的完整类型。因此本次能直接断言的是唯一公理名称集合相符，不能把名称检查说成已逐表达式验证公理签名。

图中存的是常量依赖边，不是完整 imported proof-term AST；完整包中的自有 `.olean` 也不是全部上游构建产物。固定上游定义的源语义已核查，历史缓存的完整字节到该源提交的可重建对应关系未被本次独立建立。若要求完全脱离既有执行记录的第三方再验证，应使用固定工具链/依赖重新运行随包复现流程。

## 负控与复现

`audit_bundle.py` 在普通 Python 和 `python -O` 下均全部 PASS，两个 JSON 结果按结构完全相同。所有检查使用显式异常，不会被优化模式移除。

`test_audit_negative.py` 在 `python -O` 下通过 10 项拒绝测试：缺失闭包节点、unsafe 节点、partial 节点、额外公理、重复节点、截断根闭包、伪造 inventory 公理集合、CSV 坐标改动、checkpoint 系数改动、预期范数改动。每项都被实际拒绝，详情见 `negative_tests.json`。

在已安全解包的两个包旁运行：

```sh
python audit_bundle.py bapat_n200_20261008_compact bapat_n200_20261008_public --output audit_results.json
python -O audit_bundle.py bapat_n200_20261008_compact bapat_n200_20261008_public --output audit_results_optimized.json
python -O test_audit_negative.py bapat_n200_20261008_compact --output negative_tests.json
python bapat_n200_20261008_compact/reproduce.py --check-only
```

最后一条只是包方复现入口的完整性检查，本次也实际运行，输出 140 个文件、22 个源码、图压缩无损。没有调用该入口的 Lean 执行模式。

## 不能扩大成的结论

- 最终 δ 是存在的正实数，未形式化论文指定的有理 epsilon、具体 q₀ 或定量负导数界。
- 不保证形式化的最终正定矩阵具有有理复数条目；Gram 本身是高斯整数，但所选 δ 的有理性没有在此证明。
- 两个内部点的具体值、正性及距 1 的定量界没有被这一 Lean 结论给出。
- 这不是实对称后续新稿的 Lean，也不形式化 CP1 渐近路线。
- 三个标准 Lean 公理明确存在，不能宣传成完全无公理证明。
- 本次 PASS 是已明示范围内的独立审核，不是期刊审稿或历史优先权证明。
