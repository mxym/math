# 初步原创性与文献比较：mxym/math

检查日期：2026-10-07。初筛由 GPT-6 Luna（High）执行，主代理复核书目一致性和结论范围。本文是供后续文献复核的初筛，不是证明审计、穷尽性综述、优先权证明或期刊等级判断。按照仓库要求，未把关键词搜索未命中解释成原创证据。引用只在明确列出已读主文时才据主文比较；其余处标明仅查元数据或沿用仓库已存比较记录。

## 主要新稿：全阶对称张量的全收缩交换子残差

### 正在比较的精确命题

`notes/global-orthogonal-tensor-rigidity/all-orders.md` 定义对称实 p 阶张量的全部收缩矩阵 (X_\alpha=T_{\alpha_1,\ldots,\alpha_{p-2},\cdot,\cdot})，并把残差定义为所有有序对的 Frobenius 交换子平方和的平方根 (R_p(T))。它证明，对每个有限维数 m 和 p≥3，

$$
\operatorname{dist}_F(T,\mathrm{ODeCo}_{m,p})\le \frac{p^p}{p!}\sqrt{2p}\,m^{p/2}\sqrt{R_p(T)}.
$$

权重可为零、可重复，不要求小残差、权重下界或分解权重间隔。固定 m,p 时残差指数 1/2 不可改大；常数至少按 (m^{1/4}) 增长。三阶专稿 `global-odeco.md` 把常数改进为 (5m^{3/2})，并在 m=2 给出精确公式 —— 设二元三次的三次谐波分解系数范数为 A、一次谐波系数范数为 B，则距离为 $\sqrt3|A-B/3|$，残差为 $4|A^2-B^2/9|$，最佳统一常数是 $\sqrt3/2$。这些是从手稿中逐项读取的断言；本次未重做全部证明。

### 逐项主文比较

1. **Boralevi–Draisma–Horobeț–Robeva (2017), “Orthogonal and unitary tensor decomposition from an algebraic perspective,” Israel Journal of Mathematics 222(1), 223–260, arXiv:1512.08031, DOI [10.1007/s11856-017-1588-6](https://doi.org/10.1007/s11856-017-1588-6).** 已读取主文 PDF 的可检索文本，尤其定义、定理 4、对称三阶部分 §3.1、引理 11 / 命题 12 和高阶对称部分 §4.2。主文建立 odeco 张量的实代数簇刻画；实对称情形的方程与结合性相联系，三阶对称情形把结合代数对应到正交分解。因而“交换子为零刻画三阶精确零集”的结构背景，以及 odeco 零集/代数观点，是明确已知并且仓库也已正确归属的内容。它没有给出本文使用的全部高阶收缩矩阵 Frobenius 交换子残差到 odeco 集的显式平方根距离误差界，也没有本文的 (m,p) 常数、任意退化权重稳定式或二元三次精确距离。结论：重要基础与精确零集已知；定量距离命题在所读主文中未见，不能据此认定优先。

2. **Auddy–Yuan (2023), “Perturbation bounds for (nearly) orthogonally decomposable tensors with statistical applications,” Information and Inference: A Journal of the IMA 12(2), 1044–1072, arXiv:2007.09024, DOI [10.1093/imaiai/iaac033](https://doi.org/10.1093/imaiai/iaac033).** 已读取 arXiv 主文 PDF，重点看摘要、引言及其通用扰动定理（定理 2.1）。该文比较两个已给 odeco 张量的奇异值/向量，按张量 spectral norm $\|T-\widetilde T\|$ 控制配对分量；对非 odeco 扰动张量，则允许找一个近似 odeco 张量，再研究其分解恢复。它是“给定分解受扰后如何恢复分量”的直接先例，且包含无分量间隔要求的高阶结论。当前命题则从一个可直接计算的全族收缩交换子残差控制到整个 odeco 集的 Frobenius 距离，既不输入底层分解，也不要求小扰动或可识别分量。两者是相邻但方向不同的误差问题；不能把该区别当作新颖性证明。定理比较尚未覆盖该文所有补充结果、范数变换和特殊对称约定。

3. **Mu–Hsu–Goldfarb (2015; arXiv version 2017), “Successive Rank-One Approximations for Nearly Orthogonally Decomposable Symmetric Tensors,” SIAM Journal on Matrix Analysis and Applications 36(4), 1638–1659, arXiv:1705.10404, DOI [10.1137/15M1010890](https://doi.org/10.1137/15M1010890).** 已读 arXiv 主文 PDF，特别是定理 2.2、3.1。其输入是已知正权重 SOD 张量加 spectral-norm 扰动；奇数阶下给出首个 rank-one 分量近似，并在噪声相对最小权重足够小（随 n、阶数变化）的假设下控制 deflation 后完整分解。与当前的无底层分解、任意实权重、无小扰动条件、残差到集合的全局界不同。它仍然是相邻稳定性文献，不能以“所需假设不同”就排除其它误差界版本。

4. **Robeva (2016), “Orthogonal Decomposition of Symmetric Tensors,” SIAM Journal on Matrix Analysis and Applications 37(1), 86–102, arXiv:1409.6685.** arXiv 元数据及摘要可检索到其研究特征向量并给出 odeco variety 上消失的多项式方程，未在本轮获取/逐条阅读整篇主文。它是代数刻画背景；更强的等价或定量距离关系未在此确认。此项仅元数据/摘要，不作定理级排除。

### 初筛判断与必须补的检索

这项全阶界不是上述精确零集定理的直接代数重述：关键新量化内容是用某一最大值方向产生的张量收缩谱隙，把所有混合系数整体估计，再对维数归纳。二元三次公式是更具体且明显强于通用上界的精确分类。检索到的两类经典近 odeco 论文处理“已知 odeco 对象受扰后恢复分解”，不能直接推出本定理的残差距离控制；但“没有直接推出”不等于“此前没有相关误差界”。下阶段宜系统检索实代数几何的 Łojasiewicz/Hoffman 型误差界、近结合/近交换矩阵系、同时近对角化、张量结构方程残差、以及张量分解的 backward stability。若发现更一般误差界，还需逐项核对其幂次是否为 1/2、是否常数可显式控制、适用张量阶数/对称类型/退化情形，以及其残差是否与 (R_p) 等价。

本次 arXiv API 针对“orthogonally decomposable / odeco / commutator / stability / error bound”做了若干关键词和布尔查询；结果含有奇异向量、分解算法、景观拓扑和学习扰动论文，但没有检索命中一个显然同形式的全收缩交换子误差界。此阴性结果只记录检索范围，不是原创证据。

## 本包内相连的张量结果与依赖界线

三阶 (5m^{3/2}) 估计是同一全局误差界的三阶加强，常数更好；这个数值需要三阶特有的合并估计，不能仅代入一般常数公式获得；二元精确式与最佳常数是额外加强。非线性 Jacobian 文稿的局部线性相干性结果及高斯输运推论是另一证明对象。其熵应用明确依赖 OpenAI/math 的 101 号上游输运 remainder (R)（以及非光滑情形的上游逼近输入），因此不能把条件性推论记作本包无条件解决熵不等式。该文还明确说残差指数 1/2 的截断指数障碍无条件成立。仓库 `DEPENDENCIES.md` 和 `README.md` 所述边界与本轮核对一致。

## 仓库其余成果：有明确重叠、直接推论或重大未闭合范围的条目

本节是对当前目录说明、既存比较文档和若干已列引用的筛查，不是逐篇完整读完所有稿件。实际已读外文主文的详细比较复用链接文档；其它项目只给风险级别和下一步。

| 项目 | 当前可支持的初筛结论 | 证据范围 |
|---|---|---|
| 001、007、008 Brenier 稳定性与密度交叠 | 明确存在仓库内部重叠：001 v3 已包含有限 q 指数及一部分尖锐例，007 v1 重叠；001/008 的 density-root Sobolev 条件已相互交叉归属。007 v2 的固定全支撑光滑强对数凹反例及特定无界 Hessian 源扩展属于新增声称，但外部优先权仍未定。半离散 (W_2^{1/3}) 先例已在比较中确认；不同 (W_1,W_2) 指标不能直接按指数判强弱。 | 已读仓库自身比较 [Gaussian finite moments](../../comparisons/2026-10-07-gaussian-finite-moments.md)、[v1/v2 reconciliation](../../comparisons/2026-10-07-modulus-tail-reconciliation.md)、[source regularity reconciliation](../../comparisons/2026-10-07-source-regularity-reconciliation.md)、[density overlap phase](../../comparisons/2026-10-07-density-overlap-phase.md)。其中部分外文主文已读，Mérigot HAL 全文此前不可访问。不是本轮重新核验全部证明。 |
| 002 二次整数环 bounded-step | Gaussian 情形是 OpenAI 上游直接重合；(\mathbb Z[\sqrt2]) 的指定对角线附近命题已有先前结果，但仓库主张的无带状限制版本与所有二次阶的转移需要独立论证。高阶补充更窄：有限状态定理以已提供商图/电压秩条件为前提，特定三次环给有限基数上界，不是任意步长 moat 定理。 | [Primary literature comparison](../../comparisons/2026-10-07-primary-literature.md) 明确逐项对照 OpenAI family 082、Li–Miller–Popescu–Sarnecki–Wattanawanichkul、Prasad、Khale；本轮读了该比较文本，没有重读所有四篇主文。 |
| 004、006、continuum-power / bounded-cluster avoidance | 路由、异常中心修复明确承袭 OpenAI family 084；Feng–Lai–Xiong 给 (f'(0)=1) 的相似性正结果。006 的新声称是定量模量限制下的避让与 profile 扩展；continuum note 有 Kollountzakis–Papageorgiou 连续线排列原理前件，并将命题限制到 2022 年 10 月的精确 BGKMW 问题版本，未声称问题截至当前仍开放。不能把这些整理成“解开 Erdős 相似性猜想”。 | 本轮读 [2026-10-07-modulus-tail-reconciliation.md](../../comparisons/2026-10-07-modulus-tail-reconciliation.md) 与 [continuum note README](../../notes/continuum-power-avoidance/README.md)；未读其保留的所有来源主文。 |
| 005 投影体积/投影体 | 最初乘积反例来自 OpenAI 上游，且上游已给维数 ≥9 的非单纯形反例；后续贡献被限定在特定产品/join 类、单纯形端点、对称体和定量稳定性。若把受限类最大值上界外推到一般凸体则不成立。严格稳定性笔记承认所用 complete Crouzeix 常数 2 及架构为上游已知结果。 | 根 CONTENTS 与 [balanced recursion](../../comparisons/2026-10-07-balanced-recursion.md)、[simplex product rate gap](../../comparisons/2026-10-07-simplex-product-rate-gap.md)、[symmetric projection cone equality](../../comparisons/2026-10-07-symmetric-projection-cone-equality.md) 提供范围。修订后的 bibliographic correction 专门加入 Weil bodies、matroid、lift-zonoid 等前置归属。 |
| 003、critical covering gauge | Assouad 维数 2 的非嵌入对象并非自动“最小维数/最优构造”；仓库明确不声称极小。critical gauge 补充是在 entry 003 sheet construction 上伸缩调度，并附带原完整证明。更一般的先前构造是否已经有同一任意 gauge 上界尚未排除。 | 读取 README/CONTENTS 声明；未逐篇核对 Banach 空间非嵌入文献。需独立检索 Dvoretzky 转移、Assouad 维数及 prescribed gauge 构造。 |
| 009 hard-sphere fluctuations 及 virial/stress 补充 | 主要概率/分析历史输入 H1–H6 是明确导入包，不是本稿新证。补充覆盖限定测试函数的均值修正和局部应力缺陷；README 仍说完整 one-particle mean correction 未完成。不能升级成无条件全测试函数 CLT/完整 Boltzmann 正则性新结果。 | 读取 CONTENTS/README 的依赖声明；本轮没有审查硬球气体主文文献，也未读取外部动力学主文。 |
| 单纯形稳定性诸补充 | sharp-simplex note 的端点幂 (1/(d-1)) 和 simplex truncation obstruction 相互闭合，按本稿明确的“每个最大体积内接单纯形的自身质心包含量”类别幂次尖锐；二次维数常数改善仍在 (d) 与 (d^2) 间留 gap。它不自动证明外部所有 Banach–Mazur 或逆 Minkowski 模稳定性最优。 | 读取 [sharp simplex README](../../notes/sharp-simplex-stability/README.md) 与 CONTENTS；仓库明确未作文献最佳速率或优先权主张。本轮没有完整核查 Böröczky 等外部主文。 |

这些已有比较记录中有些明确使用上游公开稿、已发表主文；本报告不把仓库自审当作独立同行审阅。对其它独立补充（semiconvex entropy、mixed Bellman、strict-domain calculus、higher-degree sieve、kinetic mean refinements 等），当前状态文本提供了清楚的假设和导入依赖，但未做足够外部主文比较，不能给原创性结论。特别是从一个已知主定理加新证明/新证书得到的受限推论，要把数学内容的新增范围与复现、包装或证明工程贡献分开记述。

## 新增定理级比较

### Semiconvex Gaussian entropy loss：与 LSI、entropy dissipation 和 localization 的区别

`notes/semiconvex-gaussian-entropy/entropy.tex` 的定理 1.1 对两条密度 (p,q) 做相同热卷积 (p_r=p*N(0,rI))、(q_r=q*N(0,rI))，比较 (H_0-H_z)。假设只对参考势 (V=-\log q) 要求 (D^2V\succeq-\kappa I)，并要求初始相对熵、相对 score energy 和 (p) 的 exponential-square moment 有限。它定义

$$
J(r)=\mathbb E_p\big|\mathbb E_p[\nabla\log(p/q)(Y)\mid Y+\sqrt rG]\big|^2,
$$

证明 (2(H_0-H_z)\le\int_0^z J(r)(1-\kappa r)^{-2}dr\le(1-\kappa z)^{-1}\int_0^zJ(r)dr)，对 κ>0 只在 (z<1/\kappa) 成立，系数/标量因子尖锐；到达及越过 horizon 后不存在只依赖 κ,z 的有限标量因子。它明说 J 不是 (p_r,q_r) 的相对 Fisher 信息，且结论限制于“熵损失”，不控制 (H_0) 本身。

1. **OpenAI, “A dimension-free logarithmic Sobolev inequality for subgaussian log-concave measures,” pinned `openai/math` commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, 2026-09-23, Lemma 4.2.** 已读仓库 pin 的原文（`/workspace/scratch/openai-math/...` 缓存 PDF/text 有对应来源；`semiconvex-gaussian-entropy/SOURCE_MAP.md` 给出精确链接及页码）。当 κ=0 时，上述 scalar bound 与其 Lemma 4.2 的假设/式子一致：同样是 (2(H_0-H_z)\le\int_0^z J(r)dr)，同一初始 score 的高斯观测条件预测能量。独立 note 明确继承了有限观测/独立拷贝 proof architecture，并对 κ=0 的结论不构成新定理；其数学增量是从正曲率/对数凹参照向 (\kappa)-semiconvex（允许负曲率）推广，导出精确权 ( (1-\kappa r)^{-2})、最优 scalar factor 和有限 horizon/阈值发散障碍。由于上游是公共研究稿而非外部期刊文章，这一依赖应按原稿明确归属。

2. **Bakry–Émery (1985), “Diffusions hypercontractives,” Séminaire de probabilités XIX 1983/84, Lecture Notes in Mathematics 1123, 177–206.** 此处只援引原文已有来源映射所核对的曲率判据：若势 Hessian 有正下界，则有经典 log-Sobolev/entropy 对 score 信息的控制；本 note 的 Lemma 3.1 也在 (a>0) 的正曲率后验上单独证明其变体。逻辑方向与适用区间不同：正曲率 LSI 是对单时刻相对熵 (H(\rho\mid\pi)) 的 score 上界；当前定理允许参考 (q) 仅 semiconvex，并估计沿共同高斯卷积损失掉的那部分熵，由初始 score 经 channel 的条件预测能量控制。LSI 本身不推出本定理的 (J(r)) 积分式或 horizon sharpness；反过来，本定理也不推出对一般 (q) 的 LSI。

3. **Chen–Eldan (2023), “Localization Schemes,” arXiv:2203.04163v2.** 已读 PDF 相关段落。§2.4.2、§3.2.3 的高斯二次似然/均值差熵漂移（原文 (27)）是自适应 localization 架构的实质先行工具；同一 note 的 `entropy.tex` 明确承认并逐条证明它还需处理的有限步自适应观测细节。该来源没有给出这里所需的奇异/自适应有限 observations 熵代价、相对初始 score 条件预测能量界，故是方法先例，不是同定理。

4. **Eldan–Koehler–Zeitouni (2020), “A Spectral Condition for Spectral Gap: The Missing Link to Effective Estimates,” arXiv:2007.08200v2.** 已读 PDF 中 Lemma 2 / §2.0.1 来源映射的对应内容：它构造保持目标函数的正交控制的平滑近似，用于连续 SDE/localization。当前有限观测证明只需可测控制，且没有调用奇异控制 SDE；此文不包含当前熵损失比较。

检索范围：查阅上述指定主文并用 arXiv API 搜索了 “reverse logarithmic Sobolev,” “Gaussian convolution relative entropy semiconvex,” “entropy loss Gaussian channel” 等近邻表达。返回的 reverse-LSI 项目不等于此处定理；没有找到外部发表的逐字同式 theorem。因关键词在这一主题覆盖不足，阴性检索不构成原创证据。能明确定位的最近等式是 OpenAI pin 的 κ=0 Lemma 4.2。应继续将其描述为此既有结论的 semiconvex-curvature 加权延伸候选，而不是“新的 LSI”或已经证明优先。

### Sharp/simplex stability 与经典凸体稳定性

先分清两个具体版本：

- `notes/sharp-simplex-stability` 的 sharp theorem 对每个固定 (d\ge3)、每个凸体 (K)、每个预先指定的最大体积内接单纯形 (S)，以其原质心 (z_S) 定义包含缺陷 (E(K,S)=\inf\{t:K\subset z_S+(1+t)(S-z_S)\})，证明 (E(K,S)\le G_d^\sharp e(K)^{1/(d-1)})，其中 (e(K)=a(K)-1/(d+1)) 是 entry 005 的 projection-cone invariant deficit。截顶单纯形族证明同一个量词类别的幂次不可改大。
- `notes/quadratic-dimensional-simplex-stability` 对完全相同的量词、指标、中心和幂次将系数改进为 (4096d^2)（精确 (G_d\sim16d^2)），而先前多项式维数版本的系数至多 (2^{20}d^6)。其本身也明确仍有线性下界与二次上界间的维数阶 gap。

这不是“凸体靠近某个单纯形”的一般 Banach–Mazur 问题：定理固定**每一个**最大内接单纯形，并控制围绕其自身质心的单侧 homothetic containment。一个只有 (d_{BM}(K,T_d)-1) 的结论不自动给这个所有-maximizer 指标，需额外证明从任意最大 simplex 的选取到所选中心/包含量的传递。

1. **Böröczky Jr. (2005), “The stability of the Rogers–Shephard inequality and of some related inequalities,” Advances in Mathematics 190(1), 47–76, DOI [10.1016/j.aim.2003.11.015](https://doi.org/10.1016/j.aim.2003.11.015).** 期刊信息经 Crossref DOI 核对；主文 PDF 已读 Theorem 1 和 §8。该定理从 Rogers–Shephard 差体积亏损 $\binom{2d}{d}|K|-|K-K|$ 得到到单纯形的 Banach–Mazur 稳定性；在平面，entry 005 invariant 满足精确恒等式 (a(K)R(K)=2)、(R(K)=|K-K|/|K|)，因此定理 1 / §8 可直接换元，给出本 repo 已记录的 (d_{BM}(K,T_2)-1\le576e(K)/(1+3e(K))\le576e(K))。所以平面上的一般 Banach–Mazur 稳定性是已知且线性更强；不能把 d=2 的当前粗幂次 (1/2) 当成最优贡献。该结果没有控制 d≥3 的 entry 005 invariant，也没有直接给每个最大体积内接单纯形质心的 E(K,S)。

2. **Ambrus–Böröczky (2014), “Stability results for the volume of random simplices,” American Journal of Mathematics 136(4), 833–857, DOI [10.1353/ajm.2014.0030](https://doi.org/10.1353/ajm.2014.0030).** DOI 元数据已核对，PDF 主文读了 Theorems 4–5。该文研究独立均匀随机点生成的 simplex 体积矩：Theorem 4 是接近椭球时相应随机单纯形矩最小的稳定性；Theorem 5 是**二维**接近三角形时最大值矩损失至少为 (c_p\delta_{BM}(K,T_2)^2)。其泛函是 (E_p^*(K), E_p^3(K)) 等随机体积矩，不是投影锥 invariant (a(K))，也不是固定最优内接 simplex 的质心外扩量。故它是“随机单纯形泛函的稳定性”先例，但不直接推出本稿高维命题。

3. **Böröczky–Henk (2017), “Cone-volume measure and stability,” Advances in Mathematics 306, 24–50, DOI [10.1016/j.aim.2016.10.005](https://doi.org/10.1016/j.aim.2016.10.005).** Crossref 核对卷页/年份，PDF 已读定理 1.1–1.3。其稳定结论从中心凸体的 cone-volume measure 在子空间上的近饱和假设推出接近互补子空间内积和、线段/平行体等分解结构；关注的是 measure concentration 及分解类，且该经典 paper 的凸体 centered 假设和 deficit 不是 (e(K))。它为 cone-volume stability 提供相邻方法背景，不是 simplex lower-end estimate 的直接来源。

**当前定位。** sharp 指数 (1/(d-1)) 和 simplex truncation obstruction 已在本仓库中构成精确闭合；quadratic-dimensional 补充新增的是维数常数改进 (O(d^6)\to O(d^2))，并未改变幂次或最佳维数阶。二维则存在上述已知更强直接结果。对 d≥3 已读的经典比较分别研究 Rogers–Shephard、random-simplex moment、或 cone-volume concentration，不是同量 (a(K)) 与 same-centroid every-maximizer containment。由于 entry 005 的 invariant 属于特定 affine projection-cone ratio，这轮没找出能等同转化的高维经典 theorem；这只是有限源比较，不是优先权判断。

### 额外抽查：strict-domain Crouzeix 补充中的哪些结论已由转移定理给出

**Åhag–Czyż–Virtanen (2026), “Square Functions, Complete Crouzeix Conjecture in Dimension Three, and the Clouâtre–Ostermann–Ransford conjecture,” arXiv:2608.27346v3, Theorem 8.2, Corollary 8.1, Theorem 5.5.** 已读取 arXiv v3 HTML 主文这些结果。Theorem 8.2 是完全有界的 similarity-transfer theorem：固定 base dimension d，若 (K(B)) 对每个矩阵 (B\in M_d(\mathbb C)) 是常数统一的 complete C-spectral set，且对所有条件数 (\operatorname{cond}(S)<\gamma) 的 base similarities，(K(S^{-1}AS)) 紧包含在有界凸域 $\Omega$ 内，则 $\Omega$ 的最优 complete constant 至多 $\max\{1,C/\gamma\}$。当前 supplement 取 (K(B)=\overline{W(B)})、C=2，把 numerical range 到边界的正 margin 和 (\|A-cI\|) 转成适当 $\gamma$，从而得 (\max\{1,2/(1+d/N)\}<2) 的宽域常数；再用有限 Krylov compression 到 Hilbert 空间。其 broad “larger enclosing domain 上有小于 2 的 complete constant”结论因此是 **Åhag–Czyż–Virtanen Theorem 8.2 + OpenAI pinned complete constant-two theorem 的直接推论**，应明确归为已知输入的合成推论，不是该补充单独的新定理。新稿明示将其称作 deduction。精确 norm-margin 公式未在 ACV 原文中见到逐字表达；本轮不确定其是否曾在其它源出现。

这里用到的 complete constant 2 前件另来自 OpenAI, “A direct proof of the complete Crouzeix inequality,” pinned `openai/math` commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, Theorem 1.1；不能误写成 ACV v3 自己在所有维数证明 complete Crouzeix。报告所读 ACV v3 明确写其 Complete Crouzeix theorem 是 (d\le3)，但 transfer theorem 本身不限此 d。补充中的 retained-deficit、reduced-density、intrinsic $\mu/M$ certificate 不由此 transfer theorem 直接给出，仍需各自文献比较。

## 资料读取记录和未闭合范围

- **完整主文（本轮）**：Boralevi–Draisma–Horobeț–Robeva arXiv:1512.08031 PDF/text；Auddy–Yuan arXiv:2007.09024 PDF/text；Mu–Hsu–Goldfarb arXiv:1705.10404 PDF/text。前者用于精确零集与代数刻画；后两者用于近 odeco 分解恢复比较。文件来自 arXiv 公共接口，标题、年份和 DOI 如上。
- **元数据/摘要或搜索结果**：Robeva arXiv:1409.6685 的搜索结果/摘要；关于“odeco + stability/error/commutator”若干 arXiv API 搜索条目。没有据此排除这些文献的主文相关定理。
- **仓库既有的主文比较记录**：传输、二次环、投影体积、非线性避让几项由既存 comparison 文档保存。该文档报告的已读来源依各文档自身的“primary text”段落；本轮只审阅这些比较文档及项目 README，没有重做全部来源文本读取。
- **明显未闭合**：全阶 odeco 距离界的系统数学文献搜索；代数误差界和近同时对角化文献；三阶精确二元公式独立复核；003/009/多数独立 note 的领域综述；所有论文的证明有效性。所有“本轮未发现直接命题”的表述应理解为查阅边界，不是优先权结论。

## 初筛结论

张量方向目前展示了与既有精确 odeco 代数刻画清楚不同的全局定量问题，并有严谨写明的退化覆盖、指数尖锐性和二维精确基准；读过的近 odeco 扰动文献并不直接覆盖这类“交换子缺陷 → Frobenius 距离”误差界。它值得进一步文献比较与独立证明核查，但本次资料不足以说“首个”或说外部已无等价结果。仓库其余内容整体上已有较好的范围/来源说明，也有若干上游完全重合或内部重复已被显式承认；广泛的补充笔记尚缺少逐项外部主文级比较，当前正确结论是状态未定。
