# Bapat 原区间猜想：Lean 源码独立静态语义审核

日期：2026-10-08（UTC）  
审核对象：`bapat_n200_20261008_compact/formalization/sources/` 的 22 个 Lean 模块，以及同包 `formalization/reference/proof.md` 和 `counterexample_vectors_n200.csv`。  
审核性质：独立的数学语义阅读和只读文本核对；不是独立 fresh Lean 编译或内核重放。

## 1. 结论与证据边界

**静态语义结论：未发现阻断原猜想反例结论的定义替换、数学桥缺失、条件偷换或最终量词缺口。** 源码所陈述并连接到最终定理的对象，确实是全部置换按原索引顺序逆序数加权的 q-permanent；数据确实定义了 CSV 原顺序的 200×200 复 Gram 矩阵；负导数经严格正的对角扰动得到非对角复 Hermitian 正定矩阵，并在两个严格位于 `(-1,1)` 的有序实数点发生严格下降。

最终的 `BapatRankTwo.N200.originalBapatConjecture_false` 所否定的 `OriginalBapatConjecture`，在语义上对应 Mitchell 2020 第 915 页陈述的原区间猜想。审核时直接读取了该期刊原文，核对了全置换逆序权定义及非对角 Hermitian 正定、`[-1,1]`、严格递增条件。[Mitchell, *A note on Bapat's q-permanent conjecture*, pp. 915–919](https://files.ele-math.com/articles/oam-14-56.pdf)。这里仅用它核对问题表述，不把文献中的任何待证结论作为 Lean 证明前提。

**本审核没有安装或运行 Lean，没有执行 fresh 编译、内核重放或大整数证书复算，也没有进行 Git 写入。** 阅读了所有非巨大数值 trace 模块的正文；对四个巨大 trace 模块审核了声明/连接结构及若干初始和边界处正文，没有人工逐位复算所有大整数。使用标准库脚本做了文本解析、逐行数据比较、SHA-256 和后继声明结构检查，这些不是 Lean 实测。

随包 `RESULT.json` 声明了 22 模块、928 个 owned declarations、22371 个 all-owned closure declarations 的 trust-level-0 PASS。该记录属于包方提供的执行证据；本报告不把它改写为审核者自己的执行结果。本报告的结论是数学语义审核；编译成立、全部证书算术成立、依赖环境可信等机器层结论仍应以可复现的独立内核证据为准。

本文后续源码行号均相对于审核对象下 `formalization/sources/`，采用 `文件:行号` 形式。

## 2. 最终命题是否真是目标问题

### 2.1 原猜想量词没有弱化

`BapatOriginalStatement.lean:14–16`：

- 对任意自然数 `n` 和 `Matrix (Fin n) (Fin n) ℂ`；
- 假设 `A.PosDef`；
- 假设 `¬ A.IsDiag`；
- 结论是 `StrictMonoOn (fun q : ℝ => (qPermanent A (q : ℂ)).re) (Icc (-1) 1)`。

`StrictMonoOn` 对区间中任意 `q₁ < q₂` 要求函数值严格增大。索引从数学常用的 `1,…,n` 换成 `Fin n` 的 `0,…,n−1` 保持全序，未改变逆序关系。

`BapatDefs.lean:78–80` 还另定义了只要求非严格单调的 `BapatConjecture`。审核并未混淆这两个命题；最终原猜想否定使用的是前述严格、含非对角条件的 `OriginalBapatConjecture`。

### 2.2 复数取实部不是弱化目标的漏洞

`BapatReality.lean:9–23` 用 `(i,j) ↦ (σ j, σ i)` 建立逆序对与逆排列逆序对的双射，证明 `inversions σ = inversions σ.symm`。`25–31` 证明 Hermitian 条件下排列乘积的共轭等于逆排列乘积；`35–52` 由 `σ ↦ σ⁻¹` 对整个置换和重新索引，证明实数 q 时 q-permanent 固定于共轭。

因此 `BapatReality.lean:54–58` 的 `qPermanent_eq_ofReal_eval` 确认：对 Hermitian A，真实复 q-permanent 等于实多项式取值嵌入 ℂ。以实部承载实数序关系是准确的，不是在忽略一个可能非零的虚部。此实值性结果是单独的语义桥；最终否定定理本身的证明项不必显式调用它才能与目标表述对应。

## 3. q-permanent、导数与原顺序

### 3.1 全部置换与真实逆序数

- `BapatDefs.lean:16–17`：`inversions σ` 是满足 `i<j` 且 `σ j<σ i` 的所有索引对的基数。
- `BapatDefs.lean:20–23`：`qPermanent A q = ∑ σ : Equiv.Perm (Fin n), q ^ inversions σ * ∏ i, A i (σ i)`。
- 它既没有限制置换种类，也没有自由权重参数、特殊子群、抽样或重新排列后的逆序数。
- `BapatDefs.lean:26–28` 逐排列定义真实实系数多项式；`30–37` 证明其取值正好是 q-permanent 的实部；`39–44` 证明在 1 的导数等于真实 `weightedInversionSum` 的实部。

`BapatMarkedInversions.lean:141–145` 中 `originalPairs` 与 `originalInversions` 保留原线性序；`161–162` 的加权和使用上述逆序基数。`BapatDefs.lean:42–44` 通过展开同时匹配两处逆序定义，而非假设它们相同。

### 3.2 标记逆序对到二行余子 permanent

证明从任意交换环上的任意矩阵开始，并非只对特殊数值矩阵假设公式成立：

1. `BapatMarkedInversions.lean:47–75` 将排列乘积拆出两行，并计算交换这两行像之后的差，得到真实 2×2 行列式乘剩余行乘积。
2. `93–138` 用显式双射 `σ ↦ σ ∘ swap i j` 把下降像与上升像配对，得到每个行对的 `permanentSum − 2 * inversionPairSum` 公式。
3. `147–158` 证明原有序对个数为 `choose(card ι,2)`，并将逆序数展开为所有原有序对的指示函数和。
4. `164–175` 证明加权逆序和等于逐标记对之和；`179–195` 汇总为 determinant 公式。
5. `199–201` 的 `twoRowCofactor` 是固定 `σ i=k, σ j=l` 的真实置换纤维上剩余乘积的和。
6. `204–230` 按实际两个列像分组；`233–243` 得到完整有序两行 cofactor 恒等式。

这里没有宣称 q-permanent 在任意同步重排下保持不变。唯一相关的重排是全置换求和上的显式双射；原索引序中的 `i<j` 和 `k<l` 均被保留。

## 4. Fischer 桥并非未证明接口

### 4.1 permanent 到阶乘权系数范数

- `BapatColorExpansion.lean:17–21` 定义颜色选择权和真实因子积 `∏(a_i+b_i X)`；`23–47` 从乘法分配律证明系数展开。
- `BapatColorTransport.lean:30–60` 构造颜色保持置换与两组互补子集双射的等价；`71–106` 因而证明基数是 `k!(n−k)!`，不是手写的未证计数常量。
- `BapatPermanentFischer.lean:30–37` 将该计数识别为实际置换纤维的基数；`45–101` 从全 permanent 展开得到双线性系数配对公式。
- `BapatPermanentFischer.lean:122–124` 定义 `fischerNormSq n p = ∑_{k=0}^n (n−k)!k! |p_k|²`。
- `127–138` 用系数共轭性质把真实复 Gram permanent 识别为此范数平方。

阶乘次序没有错位：`k` 计数所选 X 因子的个数，权为 `k!(n−k)!`，等于二元齐次形式 `x^(n-k)y^k` 的 Fischer 权。

### 4.2 删除行列的互补 permanent

`BapatTwoRowCofactor.lean:14` 的补集保留原标签。`17–59` 构造补集双射的唯一两点扩张，`62–90` 构造逆向限制；`94–115` 证明它们互逆。由此 `147–158` 将纤维式 `twoRowCofactor` 识别成真实补集之间所有双射的乘积和，**没有额外阶乘或漏掉的多重性**。

`BapatMixedFischer.lean:15–16` 的 `mixedPermanent` 的行列可为不同有限类型；`20–50` 证明选任意等势重标记均对应标准 permanent，并且最终系数式不依赖重标记选择。`53–75` 定义、证明混合 Fischer 配对及自配对范数恒等式。

`BapatRankTwoIdentity.lean:50–64` 组合上述两个实际补集桥，将 Gram cofactor 识别为齐次次数 `card ι−2` 的配对。`TwoPointComplement_card` 在 `BapatTwoRowCofactor.lean:125–134` 对不同的两个删除索引证明了这个次数。实际使用处的不同性来自原有序对中的严格不等号，不是额外假设。

### 4.3 有序 S 及最终恒等式

- `BapatRankTwoIdentity.lean:19`：`wedge i j = a_i b_j−b_i a_j`。
- `23–34`：剩余多项式等于删除恰好 i,j 后的真实因子积。
- `37–39`：`wedgePolynomial` 对原顺序 `i<j` 求和。
- `BapatDefs.lean:59–63`：实际 Gram 的 2×2 minor 等于 wedge 乘相应 wedge 的共轭。
- `BapatRankTwoIdentity.lean:67–81` 展开 S 的混合配对；`85–112` 得到

  `2 * weightedInversionSum (gram a b) = choose(n,2) * ||F||² − ||S||²`。

- `116–122` 取实部，得到真实 q-permanent 多项式在 1 的导数恒等式。

关键符号、二倍因子和 binomial 因子均来源于以上逐步证明。没有在该核心恒等式的参数中加入“假设 Fischer 公式”“假设 endpoint identity”或数值正确性等接口。

## 5. 递推计算的是同一个有序 S

`BapatWedgeRecurrence.lean:15–26` 先以原自然数顺序定义真实 `natF`、删除两因子的 `natRemaining` 和 `natS`。递推不是直接拿来充当 S 的定义后就跳过语义证明：

- `64–74` 证明乘积求导；`76–96` 证明齐次 Euler 形式在去齐次化后的 `nF−XF'` 恒等式。
- `113–140` 按新加入的最后一个索引把 S 拆成旧对贡献与全部新对 `(i,n), i<n`。
- `142–153` 推出

  `S_(n+1) = (a_n+b_n X) S_n + b_n (n F_n−X F'_n)−a_n F'_n`。

- `155–173` 才定义 `FSeq/SSeq` 并归纳证明它们等于真实 `natF/natS`。
- `175–207` 通过保序的 `Fin n` 与 `range n` 对应，连接实际因子积、删除积和有序 wedge 和。
- `209–216` 最终证明 `FSeq_eq_twoColorProduct` 与 `SSeq_eq_wedgePolynomial`。

所以递推中 `m` 是已加入的旧因子个数，新增对的符号为 `a_i b_m−b_i a_m`；没有把 `m` 写成 `m+1` 的次数偏差，也没有把本应依赖顺序的 S 当作无序量。

## 6. 高斯整数列表、degree 参数与数值证书

### 6.1 整数列表有真实多项式解释

`BapatExactCoefficients.lean:12–21` 以 `Zsqrtd (-1)` 表示高斯整数，以环同态嵌入 ℂ，并通过 Horner 规则将升次系数列表解释为多项式。`77–143` 分别证明列表加法、数乘、取负、相减、移位、乘一次因子、求导和 `sStep` 的正确性。

`55–60` 的 `state` 与上述 F/S 递推一致。`BapatExactStateBridge.lean:10–34` 对任意输入序列和 n 归纳证明 `state` 的两份列表分别解释成真实 F 和原有序 S，**没有非零因子、除法可行性、系数长度或数值近似前提**。

### 6.2 截断范数不是隐藏漏洞

`BapatExactCoefficients.lean:70–73` 的 `fischerInt n P` 明确只读 `0,…,n` 的系数，缺失项补零。`145–164` 证明列表每一项的多项式系数意义、整数平方模意义和 Fischer 范数意义。

`fischerNormSq` 采用独立的齐次次数参数，不采用可能因最高项为零而下降的单变量 `natDegree`。这正是去齐次化二元齐次形式所需的语义。实际 F 来自 n 个一次因子；S 的每项来自删除两因子后的 n−2 个因子。因而读取 F 的 `0,…,n`、S 的 `0,…,n−2` 与目标对象一致。递推列表允许尾部零或更长表示并不构成额外自由度，因其解释与真实多项式的等式已经证明；相关恒等式本身也对所定义的配对直接证明，不依赖未提供的 degree 假设。

### 6.3 200 行数据的独立文本对应

`BapatN200Data.lean:11–212` 写出了 200 行四个整数坐标，`214` 有 `vectors_length = 200` 的 `rfl` 证明。审核者独立用标准库解析 Lean 元组和 CSV，确认：

- Lean 元组数量：200；CSV 数据行：200；
- 所有四个坐标逐行完全相同，次序完全相同；
- 最大坐标绝对值：20；
- CSV 原始字节 SHA-256：`9d16617d6eb287535a752cf5ef6f3d4672a133812bf0fbd908738a10c223fc25`；
- 22 个源码文件的 SHA-256 均与 `formalization/verify.json` 中冻结值相同。

`BapatN200Matrix.lean:10–12` 将 `Fin 200` 的每一行嵌入 ℂ，定义 `matrix = gram a b`；`BapatDefs.lean:47–48` 的 Gram 正是 `a_i conjugate(a_j)+b_i conjugate(b_j)`，即论文的 `V V*`。

`vectorAt` 在越界时有零向量默认值（`BapatExactCoefficients.lean:62–63`）。实际 `Fin 200` 只访问 0 到 199，且列表实有 200 行，故不存在通过缺省补零偷换矩阵的情形。注意：最终 Lean 证明无需显式依赖 `vectors_length`，因为具体值可定义展开；CSV 与 Lean 的外部对应则由本次文本核对补充确认。

### 6.4 Trace 的静态结构及其限度

`BapatN200Trace0.lean:10–15` 从 `([1],[])` 建立 `state_eq_000`。后续每步的模式均为：先 `rw [state, state_eq_上一编号]`，再 `decide +kernel`。

本次对四个 trace 文件作全文结构匹配，确认恰好 200 个此模式的后继证明，编号从 1 连续到 200，定理名、state 步数、checkpoint 编号与前驱编号全部相符。关键边界位置：

- 50：`BapatN200Trace0.lean:419–425`；
- 100：`BapatN200Trace1.lean:410–416`；
- 150：`BapatN200Trace2.lean:410–416`；
- 200：`BapatN200Trace3.lean:410–416`。

`BapatN200Trace.lean:10–14` 分别定义 `fischerInt 200 checkpoint_200.1` 和 `fischerInt 198 checkpoint_200.2`，以 `decide +kernel` 陈述并证明 `19900 * permanentNorm < wedgeNorm`。

这说明数值证书在源码中是逐步证成的目标，而非通过读取 Python 输出、外部 JSON 或任意常量公理导入。但是本审核没有执行上述决策证明，故不声称自行验证了 200 步大整数算术或最终正差。Python 等外部复算结果也没有被当作 Lean 核心证明前提。

## 7. 负导数、PD、非对角与严格内部下降

### 7.1 数值正差接到真实负导数

`BapatExactStateBridge.lean:54–67` 的 `derivative_negative_of_gap` 使用的唯一特定输入条件是实际 state 范数的严格正整数差；将它转换到 ℝ，再使用已证明的 F/S 解释和真实 derivative/Fischer 恒等式。

`BapatN200Counterexample.lean:13–17` 对真实 200 行输入应用此定理，以 `state_eq_200` 替换计算状态，再以 `norm_gap_positive` 提供严格正差。`200.choose 2 = 19900` 与维度/次数对应正确。

### 7.2 PSD 只是起点，最终是真的 PD

此外直接阅读了固定 mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612` 的上游 `Mathlib/LinearAlgebra/Matrix/PosDef.lean`：`162–163` 的 `Matrix.PosDef` 明确定义为 Hermitian 与所有非零有限支撑向量二次型严格大于零的合取；`454–459` 给出有限索引时与通常向量二次型定义的等价。`167–168` 直接提取 Hermitian 性；`190–200` 证明正对角矩阵正定；`252–255` 是本证明使用的 PSD 加 PD 定理。因此源码中的 `PosDef` 确实是标准复 Hermitian 正定性，没有仅用 PSD 或仅用对角正性冒名。

`BapatDefs.lean:50–56` 用两个外积的 PSD 性证明原 Gram 是 PSD 和 Hermitian。`BapatN200Matrix.lean:14` 实例化这一点。原秩至多二的 200×200 Gram 本身不被冒称 PD。

`BapatDefs.lean:66–72` 定义 `perturb A δ = A + diagonal(δ)`，并在 `hA : A.PosSemidef`、`hδ : 0<δ` 下，用正定对角矩阵与 PSD 矩阵相加得到 `PosDef`。`BapatContinuity.lean:53–59` 证明扰动参数到真实 endpoint 导数的连续性；`84–102` 从 δ=0 的严格负性取得 **严格正的** δ，并保留负导数。

这一步确实改变矩阵为 `A+δI`，同一维度 200，且正定性位于最终存在命题中。它不是援引“PSD 情况等价于 PD 情况”的外部未证接口，也不是仅给出 PSD 反例后停止。

### 7.3 非对角得到独立证据并沿扰动保持

`BapatN200Matrix.lean:17–29` 计算实际矩阵 `matrix 0 1 = 398−I`，取虚部排除该项为零，因此证明非对角。`BapatOriginalStatement.lean:18–24` 证明纯对角扰动不改变这一条件；`BapatN200Matrix.lean:34–35` 实例化。

### 7.4 下降点不只是在区间外，也不依赖端点作为唯一反例点

`BapatContinuity.lean:26–50` 先由导数多项式连续性，在 1 左边且大于 −1 找到负导数点；若原多项式在开区间上单调，其该处导数须非负，矛盾。随后展开非单调性，得到 `a,b∈Ioo(-1,1)`、`a≤b` 和 `P(b)<P(a)`，再排除 a=b，获得严格 `a<b`。

`BapatN200Counterexample.lean:22–30` 的完整存在命题是：

- 存在 `δ : ℝ` 且 `0<δ`；
- `(perturb matrix δ).PosDef`；
- `¬ (perturb matrix δ).IsDiag`；
- 存在 `q₁,q₂∈(-1,1)`；
- `q₁<q₂` 且 `P(q₂)<P(q₁)`。

`BapatOriginalStatement.lean:28–37` 将这样的内部下降点放回闭区间，并与 `StrictMonoOn` 直接矛盾。`BapatN200Counterexample.lean:32–34` 最终无需额外假设地给出 `¬ OriginalBapatConjecture`。

## 8. 源码层缺口扫描与需要保留的限定

全文源码词法扫描未发现 `axiom`、`sorry`、`admit`、`unsafe`、`partial`、`implemented_by`、`extern`、`native_decide` 或 `opaque` 声明。可见的数值决策使用 `decide +kernel`。`set_option maxHeartbeats 0`、较大 `maxRecDepth` 是资源设置，不是数学前提。所有模块设置了 `autoImplicit false`，未见把缺失命题偷偷引入为自动隐式参数的形式。

上述扫描是辅助证据，不替代检查展开后的依赖闭包和内核重放；通用 Lean/Mathlib 基础、经典逻辑和标准定义也不能从“源码未出现 axiom”推断成完全无公理系统。

以下边界必须在公开结论中保留：

1. **δ 是存在的正实数。** 本 Lean 版本未形式化 `proof.md:21–29,101–131` 的特定有理 epsilon 和 q₀，也未给出这些数的数值界；命名 `explicit_counterexample` 不应被解释为已形式化一个数值显式 δ。
2. **最终矩阵不被形式化为有理复数矩阵。** 原 Gram 由高斯整数构造，但所选 δ 的有理性未证明。
3. **两个点严格位于 `(-1,1)`，没有形式化它们的具体取值或与 1 的定量距离。** 命题本身也未要求二者为正数；这不影响原区间反例。
4. **没有推翻实对称限制版。** 见已证明的非零虚部 `398−I`；本结论是复 Hermitian 版。
5. **Lean 不依赖也不形式化 CP1 渐近存在路线。** 该附加论文材料不属于此证明链。
6. **秩恰为二、所有原始行非零和范数差的论文比例界不是最终证明必要条件，也未在这里作为额外形式化成果主张。** Gram 结构、PSD、非对角、严格正差已经足够。
7. **未作历史优先权结论。** 核对 Mitchell 的原陈述不是穷尽文献新颖性搜索。
8. **不把既存 PASS 记录视为本次实测。** 本报告独立于编译者作语义核查，但没有产生第二次 fresh Lean execution。

## 9. 可公开的简短结语

该源码包的最终定理在数学语义上覆盖了原猜想的完整复 Hermitian 正定、非对角、`[-1,1]` 严格递增表述。核心组合恒等式、Fischer 解释和有序 S 递推均在源码内得到证明，具体 200 行输入与 CSV 的顺序及坐标完全对应；PSD 起点经正对角扰动变成 PD，并取得两个严格内部点上的下降。没有发现需要补上的数学语义桥。

此结论是独立静态语义审核结果。大整数证书和全部依赖的形式正确性，应与独立 fresh Lean 编译及内核重放的证据共同呈现；论文指定的有理扰动和定量区间不在本 Lean 版本的形式化范围内。
