# 002 round5：原全二次阶 Main 独立核验报告

日期：2026-10-07 UTC。**数学核验结论：PASS。** 本报告针对下列确切冻结归档和本次独立构建的对象集合；未发布到公共网站或仓库。

- 输入：`entry002-v3-lean-round5-20261007.zip`，16,044,443 bytes。
- 输入 SHA-256：`c0fa4d986a4de3700f68deb4d4cead1a6a51713c144bc62d75ae5d4b90592dda`。
- 端点：`Entry002.arithmeticSupply_mainTarget_proved : Entry002.MainTarget`。
- 精确入口模块：`ArithmeticSupplyWeakMain`，源文件为 `lean/references/upstream/arithmetic-audit/ArithmeticSupplyWeakMain.lean`。
- `Targets.lean` SHA-256：`f4cbd00f1853dc53b955a2b05e7d07223a6a7fe5e0fc762d87e8ed397fe64671`。与 round3 原目标逐字相同；并未以新的 weak target 替代 Main。

## 1. 已证主定理的可读表述

设 K 是任意二次数域，可以是实二次或虚二次。对每个正整数导子 f，取实际的阶

O_f = ℤ + f 𝓞_K。

任取 O_f 的一个二元整基 b，以及一个固定的、可逆的实线性坐标变换 e，从实系数空间 ℝ² 到欧氏平面。元素 x 的平面位置，是把 b 的两个整坐标转为实数后应用 e。

对任意实数步长界 D ≥ 0，以 **O_f 中真正的不可约元素** 为顶点；两个不同顶点相邻，当且仅当它们上述平面位置之差的欧氏范数不超过 D。则存在自然数 B，使：

1. 每个实际连通分支都有限，并且至多有 B 个顶点。
2. 每条顶点互异的有限 D-步长路径，顶点数不超过 B。
3. 不存在无限的单射（自避）D-步长路径。

B 可以依赖 K、f、b、e、D，但不依赖起点或路径。结论包括非极大阶；顶点没有按单位相伴取商，也没有截为有限样本。第三项不排除重复经过顶点的无限游走。

这里的 e 是完整的平面线性同构，不能换成实二次数域的单个实嵌入。该正式目标使用上述欧氏范数；不另外声称已形式化任意范数版本或有效算法。

## 2. 实际完成的编译与来源链

### 本轮直接 fresh

- 129 个主编译单元，含 128 个数学模块及 umbrella，全部从冻结源码重新编译。
- 113 个当时缺失的同 pin 官方模块从源补编。
- 没有复用旧轮或作者的 `Entry002` 对象。
- 在新的主对象上另行 fresh 编译 5 个生产桥：RayBridge、RayConductor、WeakFromDirichlet、WeakMainReduction、WeakMain，全部 exit0。

### 严格认证后共享的独立 fresh

另一份独立 source build 于 22:57:19 UTC 完成 **995 CFT + 457 官方模块 + 4 旧桥**，全部 exit0。本次没有重复编译995个CFT模块，而是先逐字确认本包的995源、原patch、pins及来源与该独立构建一致，再逐项重算其 source/output SHA-256。

- 共享了995个已独立 fresh 的 CFT 对象；没有使用作者历史 CFT 缓存。
- 457个官方补编对象也重新核对 source/output hash。
- 该共享目录里的4个旧桥不是本轮桥接证据；本轮上列5桥重新编译，实际加载路径另经检查。
- CFT模块不导入 `Entry002`，因此没有通过旧主库对象把旧假设带回本轮。

完整命令、退出码、输入/输出hash分别在 `replay/build_ledger.json`、`external_replay/build_ledger.json`、`external_replay/VERIFIED_INDEPENDENT_CFT_REUSE.json`、`external_replay/VERIFIED_INDEPENDENT_OFFICIAL_457.json`。先前独立构建的封存结果随证据包放在 `shared_cft_evidence/`。

固定工具链是 Lean 4.34.1，commit `5045d0056413266e57c625dcd7c365b10e377c52`；本次 Linux二进制 SHA-256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`。Mathlib pin为 `d13f23b723b8a846827a245b89c10fc7d3f11612`。其他包、CFT与兼容patch pins见原 manifests 和独立 preflight。

已有官方缓存是只读输入，没有重建全部 Mathlib/Lean。最终实际加载对象的路径及hash另行封存；没有使用已清理的 lean101/projection 私有缓存。

## 3. 全声明清单、存储证明闭包与精确类型

主库按 **module index** 枚举2926条声明，其中2880个安全逻辑根；5桥枚举26条声明，全部是安全逻辑根。私有、生成及非 `Entry002` namespace 的声明均在相应模块清单中，没有按 namespace 漏扫。

在 Main-first 的合并环境中再次观测：

- 134 owned模块；2952个唯一声明。
- 2906安全逻辑根 = 2501 theorem + 405 definition。这个数包含编译器生成声明，不是2906个独立数学大定理。
- 39条结构性声明 = 13 inductive + 13 constructor + 13 recursor。
- 另有7条编译器生成的 partial运行辅助，完整列在 §7；它们不属于安全逻辑根，并且不在任何安全根或 literal Main 的证明闭包中。
- 对2945条非partial声明的合并存储闭包，实际走访126,696常量；公理只有标准三项，unsafe/partial依赖和missing均为零。

两份逐根审计分别覆盖主库和五桥；显式stored type/body边与官方visitor比较无差异。Main端点另要求 theorem种类及 **存储类型表达式精确等于 `mkConst Entry002.MainTarget`**，没有额外binder或隐式PNT前提。

生成的 `.eq_1`/`.congr_simp`可能随导入顺序归属不同module。本次观察到5项ownership变化，全部名称、kind与安全标记保持一致，逐项记录在 `combined-inventory-context-comparison.json`。未把一个环境的module index当成另一个环境的结果。

主库与作者记录比较时15项pretty-print类型只有 `_root_.Module`/`Module`以及换行差异。严格初检失败记录未删除；逐项旧/新文本和机械比较结果保留，并新编 `rfl` qualification smoke确认该限定名一致。其余记录字段一致。此处理没有改动数学源码或目标。

两个安全生成投影 `TimeLaw.ctorIdx`、`TimeLaw.last` 的缓存公理统计仍少计；实际stored closure检查了完整类型/构造器依赖。故本报告从不以单独 `#print axioms` 作为最终依据。

## 4. 真正空 kernel 的 literal Main 重放

本次在 `mkEmptyEnvironment 0` 创建的 **初始零常量、trust level 0** 环境中，使用官方 `Lean.Kernel.Environment.replay` 检查 literal Main 的完整实际存储依赖闭包：

- 精确根：`Entry002.arithmeticSupply_mainTarget_proved`。
- 闭包：125,368个不同常量，完整名称表已保存。
- 进程 exit0；kernel阶段实际968,502 ms，完整进程972.141 s；终态23:17:05 UTC。
- 没有把已经导入的 Lean、Mathlib、CFT或Entry002常量预装进目标环境。
- 送入kernel前拒绝任意unsafe/partial常量或三标准公理以外的axiom；重建互递归归纳定义，并核对kernel生成的constructor/recursor。
- 重放后全部所选常量存在，根类型保持完全一致。
- 公理为 `propext`、`Classical.choice`、`Quot.sound`；随后另以只导入 stock Lean生成的基线，精确比较这三项的类型与宇宙参数。

Literal Main闭包不含旧 `arithmeticSupply_principalSupply_of_primeIdealPNT`、`arithmeticSupply_mainTarget_of_primeIdealPNT`，也不含旧强供给/PNT target常量。不存在用未闭合的旧PNT供给端点冒充新证明的情况。

此前六个弱/解析根的合并79,389常量也已从空trust0环境重放成功，145,559 ms；它是独立的中间层证据，未被拿来代替上述完整Main重放。

这是**同一官方Lean kernel实现**的独立空环境检查，不是第二套独立kernel实现。

## 5. 数学语义与新路线

传统证明referee PASS没有被当作Lean实现。实际新增源另做了逐行审查：

1. 真实prime Dirichlet sum，先证明summability，再得到固定正δ、β的实际good-bin harmonic-log供给。
2. 原整数m、原窄窗口及196-block有限覆盖；按实际正权作全局mod K thinning。允许空窗口，没有假定每个窗口都有密集批次。
3. ArithmeticCore确为原A1–A4四字段；相关本地几何/熵链已推广，未填入假A5。
4. W先固定，随后取m/J，再形成实际有限pool S，然后才量化所有walk。全部charge与telescope接回同一个实际common law。
5. 真正ideal-norm fibers与卷积、复LSeries收敛、实轴正residue及实log桥都已连接；高惯性次数、高幂、分歧余项实际受控。没有把自然prime-counting极限作为新前提。
6. 实际ray field、normal closure、conductor generator及无密度代数部分，接到全导子弱供给；最终通过真实irreducible和无限单位恢复回原Main。

详见 `WEAK_WINDOW_SEMANTIC_REVIEW.md`、`EULER_ARITHMETIC_SEMANTIC_REVIEW.md`、`RAY_CONDUCTOR_SEMANTIC_REVIEW.md`。十个WeakCore port做了规范化逐文比较；source hashes和准确数值certificate也单独保存。

非空性方面，本轮fresh smoke给出任意正f的实际二元basis、专门f=2的basis以及完整平面e的存在。另给出ℚ(√2)、f=2中的数学实例：单位3+2√2及其逆、范数绝对值7的不可约元1+2√2，其单位相伴产生无限真实顶点。这个具体Pell field实例未另做新的Lean形式化；通用basis/e smoke与源码恢复定理则有实际编译证据。

## 6. 负对照与过程中的修正

实际运行并按预期拒绝：

- 省去weak供给，把尚有供给前提的函数直接作为Main。
- 只保留f=1的目标，直接充当全正导子目标。
- 删去component的Finite合取项，只保留该处ncard断言，直接充当原目标。
- 把weak供给直接充当旧natural-density强供给。
- 私有非标准axiom经private theorem和opaque传到public theorem，完整module/stored审计仍追出并拒绝。
- 将Nat.add_comm的存储证明换成Nat.zero，空kernel实际报类型不匹配。

前四项是精确接口/类型负控，不是关于两命题逻辑不可能互推的另一个数学定理。

额外合并检查的第一次尝试错误地以全部2952条清单项为根，连7条partial代码生成辅助也纳入，因而被安全guard拒绝。失败log和当时根范围保留。修正只改变审计工具的种子范围：**仍枚举全部2952条，只以2945条非partial声明为逻辑/结构根；若依赖再触及任何partial，仍失败。** 重跑已PASS，且7辅助与Main闭包、合并非partial闭包均无交集。这不是数学源修复，不影响先已成功的literal Main重放。

另一处早期audit wrapper换行语法错误也保留了失败记录，随后仅修正wrapper并成功重跑。中途执行服务断连发生于等待外部依赖时；已完成的242个主/官方产物全部重新hash确认后恢复。没有把中断或pending记录计算成PASS。

## 7. 七个非逻辑代码生成辅助

以下均已在原始完整inventory中标 `partial=true, unsafe=false, safe_root=false`，并非被namespace过滤掉：

- `Entry002.SignSeparation.cubeEquiv._unsafe_rec`
- `Entry002.WeakA5.SignSeparation.cubeEquiv._unsafe_rec`
- `OAI.GaussianMoat.Cube._unsafe_rec`
- `OAI.GaussianMoat.cubeDecidableEq._unsafe_rec`
- `OAI.GaussianMoat.cubeDist._unsafe_rec`
- `OAI.GaussianMoat.cubeExpandIter._unsafe_rec`
- `OAI.GaussianMoat.cubeFintype._unsafe_rec`

## 8. 完成范围、未完成项与工具边界

已完成：上述确切冻结输入的无条件原Main，以及其新弱供给/finite-sieve/解析桥实际实现、fresh构建、完整存储闭包、语义核查和Main空kernel重放。

本报告**不声称**：

- 旧natural-density强供给及数域prime-ideal PNT形式化端点已完成。
- 论文secondary算法、有效bound、certificate/search、monogenic输入程序已经形式化。
- 全部Mathlib/Lean源码都fresh重建；只对缺失的同pin模块补编，其他官方缓存为只读可信输入。
- 2906安全根的合并闭包全部又做了一次空kernel重放；合并闭包做的是stored检查，真正重放的完整终点闭包是125,368常量。
- 七个partial运行辅助被kernel当作数学证明检查，或已独立验证Lean代码生成器的运行正确性。
- 旧round3 conditional端点的大重放属于本次计数；其121,903常量重放已在另一份独立报告中完成，不是本轮Main的前提，也不能替代本轮Main重放。

作者离线工具曾有清单/kind/type等硬化余项，历次实测及最终修复已另存报告。最后版本明确只复验作者历史证据与其原固定object hashes；本次fresh CFT对象虽然源SHA一致，但不等于旧历史object bytes。已比较的904份都不匹配原pins，差异原因没有证明，未归因于“只是路径”。没有改expectedhash或把fresh对象冒作旧缓存。缺原历史objects时，旧工具完整positive不能标为本机复现。作者的fresh认证规范只是文档，不是本次结果的实现依据。

数学PASS来自本报告的独立source→command/log→object→stored declaration→empty-kernel链，不依赖作者历史工具positive。

原归档1835项在结束时逐字未变；安全解包、完整hash、unique inventory、来源Git/blob/patch与69个reuse span核查均有记录。`SOURCE-HASHES.sha256`是历史4行记录，不是本包完整清单；本包实际1833项`SHA256SUMS`全部通过，另两项为清单自身与已通过正文的START-HERE副本。

## 9. 可复核证据索引

- `FINAL_MATH_RESULT.json`、`FINAL_CHECK_RUNS.json`：最终结论及实际进程。
- `BUNDLE_RECEIPT.json`、`FROZEN_TREE_SHA256.json`：输入身份和全源冻结。
- `INDEPENDENT_PREFLIGHT.json`、`IMPORT_PARSER_CROSSCHECK.json`：版本、源与递归imports。
- `replay/build_ledger.json`、`external_replay/build_ledger.json`：直接fresh记录。
- `external_replay/VERIFIED_INDEPENDENT_CFT_REUSE.json`、`VERIFIED_INDEPENDENT_OFFICIAL_457.json`：共享独立fresh身份。
- `replay/audit/main-raw.log`、`main-validation.json`、`external-raw.log`、`external-validation.json`：逐根实际记录。
- `replay/audit/combined-owned-inventory.json`、`combined-owned-closure.json`：合并全清单及非partial闭包。
- `replay/audit/literal-main-empty-kernel.json`、同名前缀的log及完整closure JSON：真正Main重放。
- `replay/audit/stock-standard-axioms.json`、`literal-standard-axioms.json`：标准公理精确类型一致。
- 各语义review、negative control及historical-tool增量报告：独立层次和未执行项。

本次直接audit目录在最后数学检查时新增分配448,733,184 bytes；后续小型报告/封存仍受500MiB上限。共享CFT大缓存没有复制进本目录或交付archive。最终交付包不含任何编译缓存，文件清单与SHA另附。
