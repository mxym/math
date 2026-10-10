# 已宣称解决的问题与专题结果

[返回首页](README.md) · [具名猜想与问题清单](README.md#已宣称解决的问题) · [分类研究目录与证明状态](RESEARCH.md)

本页汇总仓库已有公开证明所主张的结论，并提供全部主要专题入口。具名问题的来源、证明或反例结论及具体范围列在首页；下列条目包括完整分类、锐界、结构定理、方法障碍和限定情形的解答。同一研究的多个版本或加强并不重复计为独立猜想突破。

标题只作导航，不替代命题的假设、量词或证明。书面证明、完整 Lean、部分 Lean 和计算证书分别由各项目注明；此清单不表示本次重新审查了所有数学证明，也不自动认定原创性或历史优先权。借用已有定理的直接推论与继承方法在源文件中注明。

## 完整 Lean 的主要入口

- [qutrit–qudit APPT 最大纯度：全部 n≥3](formalizations/appt-qutrit-purity/README.md)：真实复密度矩阵及任意全局酉变换下的部分转置正性；n≤8 时为 (3n+8)/(3n+2)^2，n≥9 时为 3/(8n)，含上界与实际取到。879 模块构建和 155,787 声明空内核重放通过，保留失败对照、源码哈希及完整复现脚本。
- [图态 MMI 禁止子图定理](preprints/graph-state-mmi-forbidden-subgraph-2026-10/README.md)：证明 Fuentes–Keeler–Munizzi–Pollack Conjecture 1，并给出无爪 vertex-minor 的六类分量分类与七顶点连通阈值；完整书面证明与双独立精确 checker，未完整 Lean 化。
- [四个等质量高斯单元的全局锐界](preprints/gaussian-four-cell-global-2026-10/README.md)：所有 d≥3 的正四面体极值与等号分类；完整书面证明，解析端点依赖已发表 Gaussian multi-bubble theorem，Lean 仅覆盖部分代数。

- [复四行永久量—行列式主定理与完整等号分类](formalizations/four-row-complete-equality/README.md)：实际复 4×4 矩阵，所有 c≥0 的锐界、临界两类极值矩阵、两侧权重的完整分类及零行边界；保留已证最优常数、取到和全实参数范数。12 模块干净构建与 15,593 声明空内核重放通过；不将整篇论文的其他扩展纳入证书。

- [余子式谱 Theorem 1 的完整 Lean 形式化](formalizations/cofactor-spectral-asymptotics-progress/README.md)：三类输入矩阵的六个对数主项极限，复方向为 1、实方向为 1/2；后续 ramp／endpoint 命题不在证书范围内。
- [一般互信息连续性拟议界的经典反例](formalizations/mutual-information-continuity-counterexample/README.md)：实际 3×3 概率表、熵、总变差及任意小正距离反例；两侧边缘变化。量子嵌入及必要系数下界仍为书面证明。
- [Bapat 指定复数有理反例](formalizations/bapat-q-permanent-explicit-rational/README.md)与[实对称整数反例存在定理](formalizations/bapat-real-symmetric-existence-counterexample/README.md)。
- [全图强 Chollet 固定工程](https://github.com/mxym/math/tree/4d2eefd40ee930216ccd8fc0f51e4bf694251967/formalizations/laplacian-chollet-all-graphs-progress)：任意有限简单无权图、所有主子矩阵、原图度数；[源码与复核记录核对](verification/chollet-all-graphs-index-2026-10-08.json)。
- [所有周期图染色多项式的完整分类](formalizations/chromatic-cycles-all-n-lean/README.md)，以及[原 C17 一般猜想反例](formalizations/chromatic-infinite-logconcavity-counterexample/README.md)。
- [Wakhare 原始定义的四根反例](formalizations/wakhare-entropy-four-roots-lean/README.md)与[CGF Conjecture 48 反例](formalizations/cyclotomic-prime-factor-counterexample/README.md)。
- [单纯形上界](formalizations/sharp-simplex-upper-bound/README.md)与[实际截角体的锐指数障碍](formalizations/simplex-truncation-sharpness/README.md)，保留各自常数和量词。
- [所有二次整环有界步长主定理](formalizations/quadratic-orders-main/README.md)。
- [全实比值仿射几何避让](formalizations/geometric-avoidance/README.md)与[连续幂／余项避让](formalizations/continuum-remainder-avoidance/README.md)。
- [有限群通用轨道原始—对偶](formalizations/orbital-primal-dual/README.md)。
- [真实高斯测度上的价格与原始—对偶定理](formalizations/gaussian-measure-primal-dual/README.md)；[独立三胞锐界与等号分类](verification/gaussian-three-cell-independent-ci-2026-10-08/README.md)。全部 k 的几何锐比较仍为书面证明与部分 Lean。
- 复三行精确范数、指定 q-永久量半轴反例等的完整主定理入口统一见[预印本证明范围索引](preprints/lean-certified-2026-10/README.md)。

## 主要专题结果目录

以下保留原稿标题，覆盖仓库顶层 `notes/` 与已完成的 `research/` 专题说明；历史加强和独立交叉证明也保留阅读入口。

### 信息论与互信息连续性

- [Extremal same-basis correlations: full-rank rigidity and a stabilizer classification](research/ecqc-stabilizer-saturation/README.md)：不预设稳定子的满 Schmidt 秩等号态完整分类（p≡1 mod 4 时恰 2p² 个射线，否则无满秩取到）；全部奇素数维双 qudit 纯稳定子 ECQC 分数与违反态；每个 p≡1 mod 4 的素数全纯态最优比值 p/2。另证一般等号态的平坦 Schmidt 谱及秩缺口；不声称完成一般秩亏等号分类。
- [The pure-state ECQC conjecture: counterexamples and a prime-dimensional classification](research/ecqc-pure-state-counterexamples/README.md)：完整解决纯态素数维数的普遍有效性（当且仅当 p=2）；三维与五维最优比值为 3/2、5/2；所有奇素数满 Schmidt 秩反例。完整书面证明与精确 checker；三维纯态量子反例现有[完整 Lean 与空内核重放](formalizations/ecqc-pure-qutrit-counterexample/README.md)，全分类、最优性与满 Schmidt 秩结论尚未整体 Lean 化；此前一般混合态反例不归于本项。
- [A ternary counterexample to a proposed mutual-information continuity bound](preprints/mutual-information-continuity-2026-10/README.md)：反驳 Berta–Lami–Tomamichel arXiv:2408.15226v2 Eq. (106) 的一般拟议界。对每个 0 < ε ≤ 1/16，互信息差为 2 h(ε) − ε log 2，严格超过 h(ε) + ε log 8；因此任意小正距离下都有反例。
- [完整经典 Lean 及独立复核材料](formalizations/mutual-information-continuity-counterexample/README.md)，[不可变发布及源码核对](verification/mutual-information-index-2026-10-08/README.md)。量子对角嵌入与必要主导系数至少 2 为书面证明；固定一侧边缘问题及有限距离的完整最优模量未解决。

### 矩阵永久量、余子式谱与多项式

- [A counterexample to Bapat's q-permanent monotonicity conjecture](notes/bapat-q-permanent-counterexample/README.md)
- [Real symmetric counterexamples to Bapat's q-permanent conjecture](notes/bapat-real-symmetric-existence-counterexample/README.md)
- [Cycles refute chromatic infinite log-concavity](notes/chromatic-infinite-logconcavity-counterexample/README.md)
- [Unbounded normalized cofactor spectra](notes/cofactor-spectrum-unbounded/README.md)
- [Exact operator norm for the complete complex three-row permanent–determinant pencil](notes/complex-permanent-determinant/README.md)
- [A counterexample to Billey–Swanson Conjecture 48](notes/cyclotomic-prime-factor-counterexample/README.md)
- [Uniform real-rootedness of the (132,213)-avoiding permutation-polytope family](notes/ehrhart-uniform-real-rootedness/README.md)
- [A counterexample to Wakhare's entropy polynomial root conjecture](notes/entropy-polynomial-counterexample/README.md)
- [Sharp four-row permanent–determinant tradeoff](notes/four-row-permanent-tradeoff/README.md)
- [A strong Chollet inequality for every simple graph Laplacian](notes/laplacian-chollet-general/README.md)
- [Identity padding and a permanent inequality](notes/permanent-inequality-padding/README.md)
- [q-permanent half-line monotonicity counterexample](notes/q-permanent-halfline-counterexample/README.md)
- [Sharp cofactor extrema: stage package](notes/sharp-cofactor-spectral-asymptotics/README.md)

### 高斯分区与重心极值

- [Complete equal-mass Gaussian four-cell theorem](research/gaussian-balanced-four-global/README.md)
- [Equal Gaussian cells: the sharp simplex first-moment theorem](research/gaussian-balanced-simplex-all-k/README.md)
- [Gaussian centroid dimension–rate theorem](research/gaussian-centroid-dimension-rate/README.md)
- [Gaussian centroid partitions: arbitrary-mass two-collision envelope](research/gaussian-centroid-mass-envelope/README.md)
- [Gaussian centroid symmetry–rigidity](research/gaussian-centroid-symmetry-rigidity/README.md)
- [Counterexample to the arbitrary-mass Gaussian regular-simplex conjecture](research/gaussian-fixed-mass-propeller-counterexample/README.md)
- [A sharp Gaussian first-moment inequality for every prescribed mass vector](research/gaussian-prescribed-mass-centroid-ellipsoid/README.md)
- [Sharp mass-constrained Gaussian propeller fans](research/gaussian-propeller-balanced-fans/README.md)
- [Quadratic-logarithmic Gaussian dimension: all integer cell counts](research/gaussian-quadratic-dimension-all-k/README.md)
- [Sharp-constant Gaussian centroid dimension–accuracy tradeoffs](research/gaussian-sharp-dimension-rate/README.md)
- [Spherical-cap obstruction for Gaussian centroid partitions](research/gaussian-spherical-cap-converse/README.md)

### 单纯形稳定性与递归投影体

- [Dimension structure in simplex stability](notes/dimension-structure-simplex-stability/README.md)
- [Sharp projection-body optima for arbitrary product/join trees, dimensions 1–48](notes/exact-product-join-finite-optima/README.md)
- [Independent arities in simplex product/join recursions](notes/independent-arity-simplex-recursions/README.md)
- [Integrated witness simplex stability](notes/integrated-witness-simplex-stability/README.md)
- [Improved certified mixed Bellman ceiling](notes/mixed-bellman-product-join-improved/README.md)
- [A certified mixed Bellman envelope for projection-body growth](notes/mixed-bellman-product-join/README.md)
- [Polynomial-dimensional simplex stability](notes/polynomial-dimensional-simplex-stability/README.md)
- [A rigorous all-degree barrier to sharp positive-power projection-body Bellman bounds](notes/projection-bellman-power-obstruction/README.md)
- [A universal second-order oscillation obstruction for sharp projection-body Bellman potentials](notes/projection-bellman-quadratic-oscillation/README.md)
- [Dimension 55 is the first where product/join nesting is necessary for optimal projection-body volume](notes/projection-first-nesting-d55/README.md)
- [Permanent and sharply quantified projection-body nesting gap](notes/projection-persistent-nesting-gap/README.md)
- [Exact second-level projection spectrum and a strict hierarchy at every product depth](notes/projection-product-depth-hierarchy/README.md)
- [Quadratic-dimensional sharp simplex stability](notes/quadratic-dimensional-simplex-stability/README.md)
- [Effective simplex rigidity for the projection cone invariant](notes/quantitative-projection-simplex-stability/README.md)
- [Effective stability at the symmetric projection-cone endpoint](notes/quantitative-symmetric-projection-stability-bibliographic-correction/README.md)
- [Effective stability at the symmetric projection-cone endpoint](notes/quantitative-symmetric-projection-stability/README.md)（后续文献勘误见相邻 correction 项）
- [Sharp lower-end simplex stability](notes/sharp-simplex-stability/README.md)
- [Exact exponent obstruction for lower-end simplex stability](notes/simplex-truncation-stability/README.md)
- [Stronger symmetric projection stability](notes/stronger-symmetric-projection-stability/README.md)
- [Sharp two-layer projection spectrum and a certified nesting-depth gap](notes/two-layer-projection-depth-separation/README.md)
- [Complete classification of independent homogeneous product–join arities](notes/unbalanced-homogeneous-projection-recursion/README.md)

### 二次整环与格点筛法

- [Exact Eisenstein irreducible-component bounds and sharp periodic sieves](notes/eisenstein-prime-components/README.md)
- [Higher-degree arithmetic sieves](notes/higher-degree-rank-one-sieves/README.md)
- [Exact CRT minimax duality for arbitrary finite lattice sieves](notes/periodic-sieve-admissibility-minimax/README.md)
- [Exact universal finite principal-sieve optimum: 197](notes/sqrt-minus-two-exact-sieve-optimum/README.md)
- [Layered norm refinement: global prime-component bound 241](notes/sqrt-minus-two-prime-bound-241/README.md)（历史较弱界；当前结果见 197 筛法）
- [Sharp radius-two transition and complete period-six sieve rigidity](notes/sqrt-minus-two-radius-two/README.md)
- [Sharp small-radius prime graphs and optimal periodic sieves in Z[sqrt(-2)]](notes/sqrt-minus-two-sharp-moats/README.md)
- [Complete seven-generator rigidity at the sharp norm-six period](notes/sqrt-minus-two-sqrt6-generator-rigidity/README.md)
- [Sharp period 1122 at the norm-six threshold in Z[sqrt(-2)]](notes/sqrt-minus-two-sqrt6-period/README.md)
- [A universal 197-point obstruction to every finite principal-ideal sieve](notes/sqrt-minus-two-universal-sieve-barrier/README.md)

### 相似性与避让

- [Bounded cluster avoidance for uncountable selector families](notes/bounded-cluster-avoidance/README.md)
- [Large closed sets avoiding a continuum of power asymptotics](notes/continuum-power-avoidance-unified/README.md)
- [Continuum power avoidance for bounded logarithmic gaps](notes/continuum-power-avoidance/README.md)
- [Arbitrarily slow critical covering excess in Banach nonembedding obstructions](notes/critical-covering-gauge/README.md)
- [Erdős similarity: growing logarithmic gaps](research/erdos-similarity-growing-gaps/README.md)

### 有限群、张量与覆盖

- [Improved two-band lower family for binary tensor rigidity](notes/binary-tensor-two-band-lower-bound/README.md)
- [Boundary-profile lower bounds for binary tensor rigidity](notes/boundary-profile-binary-tensor-rigidity/README.md)
- [Diffuse optimal fractional covers and integer recovery](notes/diffuse-fractional-cover-rounding/README.md)
- [Fock-profile ceiling for binary tensor rigidity](notes/fock-profile-ceiling-binary-tensor-rigidity/README.md)
- [Fractional extremizers force near-design cores](notes/fractional-design-stability/README.md)
- [Universal fractional cover envelope](notes/fractional-intersecting-cover-envelope/README.md)
- [The complete bounded-packing fractional matching spectrum](notes/fractional-matching-spectrum/README.md)
- [Global quantitative orthogonal tensor rigidity](notes/global-orthogonal-tensor-rigidity/README.md)
- [Fixed-k Johnson orbital compression and exact four-subset moduli](notes/johnson-short-cycle-spectrum/README.md)
- [A 10/3 asymptotic partite edge lower bound](notes/partite-cover-number-linearization/README.md)
- [Partite intersecting cover-number bounds](notes/partite-cover-number-lower-bound/README.md)
- [Intersection excess and partite cover numbers](notes/partite-intersection-defect-cover/README.md)
- [Rank-six counterexamples require at least twenty edges](notes/rank-six-twenty-edge-bound/README.md)
- [Sharp binary tensor rigidity](notes/sharp-binary-tensor-rigidity/README.md)
- [The sharp fractional cover frontier](notes/sharp-fractional-cover-frontier/README.md)
- [Robust permutation permanent inequalities: all arities, sharp-order radius](notes/sharp-robust-permanent/README.md)
- [Simultaneous integer-degree failures of harmonic dimension comparison](notes/simultaneous-harmonic-degree-blocks/README.md)
- [Sparse nearly linear intersecting hypergraphs: cover law and rigidity](notes/sparse-near-linear-cover-law/README.md)
- [Superlinear edge necessity for near-linear Ryser equality families](notes/superlinear-near-linear-partite-cover/README.md)
- [Three-row collision energies: sharp infinite families](research/three-row-collision-tradeoff/README.md)

### 最优传输、熵与动力学

- [A sharp target-atom budget at the critical boundary](notes/critical-atom-budget/README.md)
- [Cubic hard-sphere contact and mean correction](notes/cubic-hard-sphere-contact/README.md)
- [Full-density virial and collisional stress](notes/full-density-virial-stress/README.md)
- [Semiconvex Gaussian entropy loss](notes/semiconvex-gaussian-entropy/README.md)
- [Sharp logarithmic corrections under stretched exponential target bounds](notes/stretched-exponential-sharpness/README.md)
- [Source overlap and target tails in quantitative Brenier stability](notes/transport-source-tail-synthesis/README.md)
- [Sharp transport stability for finite and binary targets](notes/transport-stability-series/README.md)

### 其他限定模型的定量定理

- [Quantitative strict bounds in complete numerical range calculus](notes/complete-crouzeix-deficit/README.md)
- [Complete similarity transfer and the scope of the strict bound](notes/crouzeix-complete-transfer-comparison/README.md)
- [Quantitative stability for power Hadamard matrices](notes/hadamard-power-stability/README.md)
- [Pinned distance densities in nested train-track models](notes/pinned-distance-densities/README.md)
- [Vertex excess and the sharp exponent in simplex stability](notes/vertex-excess-sharp-exponent/README.md)

### 独立论文和跨项目加强

- [所有有限 (n,k) 的精确有理行列式公式](notes/sharp-robust-permanent/universal-exact/README.md)：有限最大值公式，而非无枚举的简单闭式。
- [全固定秩 Chebyshev 锐渐近论文](notes/sharp-robust-permanent/focused-paper/README.md)与[独立全 k 验证](notes/johnson-short-cycle-spectrum/ALL_K_CHEBYSHEV_ASYMPTOTICS.md)。
- [全部子集秩同时约束的精确 5/14 定律](notes/johnson-short-cycle-spectrum/ALL_RANK_SHARP_FIVE_FOURTEENTHS.md)。
- [单纯形稳定性](manuscripts/sharp-simplex-stability/README.md)、[连续幂避让](manuscripts/continuum-power-avoidance/README.md)、[分数覆盖谱](manuscripts/fractional-cover-spectrum/README.md)、[永久量范数](manuscripts/complex-permanent-pencil/README.md)和[轨道原子稳定性](manuscripts/orbital-atom-stability/README.md)的整合稿。各稿保留不同结论的证明范围。
- [001–009 原稿及扩展索引](CONTENTS.md)：最优传输、全二次整环、紧集不可嵌入、密度避让、投影体演算、非线性避让和函数型动力学极限。研究稿的外部输入与假设不因入选目录而删除。

## 条件结论与仍未解决的目标

- [真实 197 素元分量的条件定理](notes/sqrt-minus-two-conditional-prime-197/README.md)依赖未证明的 Schinzel H；无条件只得 90 ≤ B_D ≤ 197。有限主理想筛最优值 197 已证明，两者不同。
- 全图 Laplacian 强 Chollet 不等于任意 Hermitian PSD 矩阵的 Chollet 猜想，也不覆盖任意加权图。
- 高斯等质量一阶矩定理不解决正相关标准单纯形噪声稳定性；固定低维精确最优值也未在该论文中确定。
- [Ryser rank-six](research/ryser-rank-six/README.md)、[Kahn 三重交一般问题](research/kahn-triple-intersection/README.md)、[Bell–Skandera 原问题](notes/bell-skandera-scalar-arithmetic-stage-20261008/README.md)、一般六行碰撞不等式、Lieb 与 Marcus 一般永久量猜想等仍未解决。
- 相似性结果针对明确的序列类、密度条件或余项范围，不等于完整 Erdős 相似性猜想。
- [Borsuk 切片记录](notes/balanced_borsuk_slice.md)只排除一个拟议构造，不解决八维一般问题。

[文献比较](comparisons/) · [证明与验证记录](verification/) · [历史首页档案](RESEARCH_HISTORY.md)
