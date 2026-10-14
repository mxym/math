# 分类研究目录

[返回首页](README.md) · [预印本](README.md#预印本) · [已证明专题清单](SOLVED_PROBLEMS.md) · [历史进展原文](RESEARCH_HISTORY.md)

本页按数学领域提供当前阅读入口。同一研究的加强、整合稿和形式化作为一条研究线列出，不把不同版本重复计为独立突破。表中状态只适用于列出的结论；详细量词、外部输入、证书与 Lean 覆盖范围以链接文件为准。

## 信息论与互信息连续性

| 研究线 | 结果与范围 | 证明／阅读入口 |
| --- | --- | --- |
| 未知态的全局酉预处理纠缠提取 | 一个不依赖谱或本征基的协议族，同时达到最优容量、全速率保真度指数、严格低于容量区间的可靠性函数与非退化高斯阈值 | [Schur 同时分块的完整解析论证](research/universal-schur-extraction/README.md)；标准表示论为外部输入、精确附属检查通过，非 Lean；不解决普通固定输入态 LOCC 蒸馏 |
| 全局酉预处理后的纠缠提取 | 任意固定局域维数与任意谱的精确容量及全速率保真度指数；LO、LOCC、完全 PPT 三类操作一致 | [确定性分块构造与完整解析预印本](research/global-unitary-ppt-extraction/README.md)；熵上界来源明确、精确附属检查通过，非 Lean；不是普通固定输入态蒸馏问题 |
| 集体全局酉变换的对数负性精确增长率 | 对任意固定 2≤m≤n 和任意含零特征值的谱，给出完整 Rényi 变分公式；等维为 ½ log(d² Tr ρ²)，固定 Bell 基下的特征值置换已足够 | [完整解析论证与八页预印本](research/collective-unitary-negativity-rate/README.md)；Tropp 矩阵 Bernstein 为外部已证输入，精确附属检查通过，非 Lean、非外部同行评审 |
| qutrit–qudit APPT 最大纯度 | 全部 n≥3 的分段精确最大值、真实量子语义、上界与实际取到 | [完整 Lean、879 模块、155,787 声明空内核重放](formalizations/appt-qutrit-purity/README.md)；不含所有极值态分类 |
| APPT 纯度与熵：锐渐近及极值谱结构 | qutrit、真实10×38反例、充分长方形区域精确最大值及全部极值态分类已核验；现完整闭合所有总维数增长路径的首阶纯度渐近律，含小于4区域的系数8 | [完整纯度 Lean 覆盖](formalizations/appt-high-dimensional-review/README.md)；[依赖审查](formalizations/appt-high-dimensional-review/REVIEW_SHARP_PURITY.md)；[既有合并预印本](preprints/appt-purity-unified-2026-10/README.md)；完整熵极值及维数变化下的谱刚性仍未整体 Lean 化 |
| APPT 全正阶与任意长宽比熵统一式 | m→∞ 时，对所有 n≥m 和 α>0 同时给出首个非零熵缺口等价；线性阶峰／体耦合、零阶双窗口、有限长宽比全极限阶数近极小谱、有限 D 显式小阶精确带 | [完整全阶证明](research/appt-growing-renyi/ALL_ORDER_VARIATIONAL.md)、[α/m→∞ 的显式相变及全长宽比谱判据](research/appt-ultralinear-spectrum-20261014/README.md)、[窗口、输入及内审范围](research/appt-growing-renyi/README.md)；完整书面证明，未整体 Lean 化；不含固定m的全移动阶问题及一般有限精确解 |
| 同一 APPT 主线：有限高阶精确解 | 2⊗n、n≥4、全部实 α≥2 的幂极值及全部等号；任意 m⊗n 在 D≥6、α≥D/2+1，或 D=4、α≥24 的唯一 spike；截止尺度 Θ(D) | [完整书面稿、预先对应表与 558 行独立内部读稿](research/appt-finite-high-order-20261014/README.md)；披露既有顶点／纯度与 ASEP 输入，未整体 Lean 化，不增加审计或重大猜想数 |
| 同一 APPT 主线：实阶扩展与锐截止 | 2⊗n、n≥8、全部实 α>1 的精确有限包络；n≥4、所有 α>0 的 pole 最优 iff α≥τ_D，临界全部等号，锐展开主系数 log2/2 | [完整稿及 471 行初稿加两行澄清的独立内部核读](research/appt-log-order-phase-20261014/README.md)；一般 m≥3 仅充分界与临界唯一性；未整体 Lean，不增加重大猜想或审计范围 |
| 同一 APPT 主线：非 qubit 的对数阶截止 | 所有3≤m≤n、D≥9、α≥32log D+1，精确 APPT/ASEP pole 最小熵及唯一等号；统一上界和3⊗n的APPT-only必要族给最坏情形Θ(log D) | [完整稿及249行独立内部核读](research/appt-nonqubit-log-band-20261014/README.md)；常数32仅充分，不给每分区必要界或ASEP下界；未整体Lean，不扩审计或重大猜想数 |
| APPT 亚单位 Rényi 阶数与全维谱分类 | 固定 0<α<1 的所有总维增长路径统一首项；固定局域维数的近极小谱、有限长宽比低阶谱刚性与半阶双分支 | [联合增长](research/appt-multilevel-counterexample/SUBUNIT_RENYI.md)、[全维首项及分类](research/appt-multilevel-counterexample/SUBUNIT_ALL_DIMENSIONS.md)、[低阶刚性](research/appt-multilevel-counterexample/SUBUNIT_RIGIDITY.md)；[8 模块、39 入口原范围复核](formalizations/appt-subunit-renyi/README.md)；完整极限及分类未整体 Lean 化 |
| 图态 MMI 禁止子图 | 证明 Conjecture 1；无爪 vertex-minor 六类分量分类与七顶点连通阈值 | [独立预印本与完整书面证明](preprints/graph-state-mmi-forbidden-subgraph-2026-10/README.md)；双独立 checker，未完整 Lean 化 |
| ECQC 极值结构与纯稳定子分类 | 全部满秩等号态；所有双 qudit 纯稳定子精确分数；p≡1 mod 4 的全纯态最优比值 p/2；一般等号的平坦谱与秩缺口 | [八页完整证明、来源与精确重放](research/ecqc-stabilizer-saturation/README.md)；不是一般秩亏等号分类，未完整 Lean 化 |
| ECQC 临界亏秩全部等号 | 对所有奇素数、r=(p+1)/2：p≡1 mod4 或 p=3 时恰 p⁴ 条 Weyl 轨道射线；其余 p≡3 mod4、p≥7 在该秩无等号 | [完整书面证明与真实 Born 重算](research/ecqc-critical-rank-equality/README.md)；有限域核心及矩阵引理已有部分 Lean；更低秩及一般最优比值仍未分类 |
| 纯态 ECQC 素数维数分类 | p=2 普遍成立，每个奇素数存在满 Schmidt 秩纯态反例；p=3、5 达到通用比值上界 p/2；一 ebit 下维数无界超出 | [论文、完整书面证明与精确重放](research/ecqc-pure-state-counterexamples/README.md)；[三维真实量子反例完整 Lean](formalizations/ecqc-pure-qutrit-counterexample/README.md)，全分类未整体 Lean 化；不重称已有混合态反例为首次 |
| 一般互信息连续性拟议界 | 实际 3×3 概率表在任意小正距离下反驳 Berta–Lami–Tomamichel Eq. (106)；两侧边缘均变化 | [署名预印本](preprints/mutual-information-continuity-2026-10/README.md)；[完整经典 Lean](formalizations/mutual-information-continuity-counterexample/README.md)；[冻结证明与附件核对](verification/mutual-information-index-2026-10-08/README.md) |
| 量子嵌入及必要系数 | 对角量子态反例；任何 c h(ε)+C ε 型一般界必须 c ≥ 2，C 为固定有限常数 | 同稿完整书面证明，未 Lean 化；固定一侧边缘版本与完整最优模量未解决 |

## 矩阵永久量与多项式猜想

| 研究线 | 结果与范围 | 证明／阅读入口 |
| --- | --- | --- |
| Bapat 原区间 q-永久量猜想 | 指定复数有理反例；实对称整数正定反例存在，无显式实维数上界 | [合并论文](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/README.md)；两项主结论完整 Lean |
| 全图强 Chollet | 任意有限简单无权图及全部主子矩阵；原图度数；包括空集、孤立点与奇异矩阵 | [书面证明](notes/laplacian-chollet-general/README.md)；[完整 Lean 固定源码](https://github.com/mxym/math/tree/4d2eefd40ee930216ccd8fc0f51e4bf694251967/formalizations/laplacian-chollet-all-graphs-progress)；[源码及复核记录核对](verification/chollet-all-graphs-index-2026-10-08.json) |
| 恒等补齐永久量不等式 | Pan–Skandera–Wang Conjecture 9.3，由其既有 Theorem 8.18 推出 | [完整书面推导](notes/permanent-inequality-padding/README.md) |
| 永久量余子式谱 | 维数无关比值界不存在；Theorem 1 六个对数主项极限已完整 Lean（复 1、实 1/2）；后续 ramp／endpoint 仍为书面结果 | [无界性证明](notes/cofactor-spectrum-unbounded/README.md)；[锐渐近证明](notes/sharp-cofactor-spectral-asymptotics/README.md)；[完整 Lean 工程](formalizations/cofactor-spectral-asymptotics-progress/README.md) |
| q-永久量半轴问题 | 指定 4 × 4 实有理矩阵在 q=49、50 之间下降；与原区间问题分开 | [完整 Lean 主定理预印本](preprints/lean-certified-2026-10/q-permanent-halfline/README.md) |
| 复三行永久量—行列式 | 所有复参数的精确范数主定理 | [预印本与完整 Lean](preprints/lean-certified-2026-10/complex-pencil-norm/README.md)；[完整书面研究](notes/complex-permanent-determinant/README.md)另含等号与张量化 |
| 复四行永久量—行列式 | Theorem 1 锐不等式与全部等号分类完整 Lean，含所有权重和零行；最优常数及全实参数范数沿用已证结果 | [完整等号工程与本轮空内核复核](formalizations/four-row-complete-equality/README.md)；[旧版锐界工程](formalizations/four-row-permanent-tradeoff/README.md)；任意列数、定量稳定性及其他扩展未包含 |
| 四行虚参数精确范数及全部等号 | 任意实际复 4×4 矩阵、全部实数 t，锐常数 max{3/2, abs(t)+1/√3}；零行及 flat／定向 Fourier 块的完整分类 | [范数及精确代数证书](research/four-row-imaginary-pencil/README.md)、[完整等号论证](research/four-row-imaginary-pencil/EQUALITY.md)；无新增 Lean；一般复参数平面仍未解决 |
| 任意权环的强 Chollet | 所有 n≥3、任意非负实 conductance、原图度数下全部主子矩阵与非负对角增量，含 cycle/bipartite 正支撑块 | [完整 all-n 书面证明](research/weighted-cycle-chollet/README.md)；Lieb 及既有二分图输入明确披露；无新增 Lean，任意加权非二分块仍未解决 |
| Wakhare 熵多项式 | (k,r)=(11,10) 至少四个内部不同实根，反驳“恰有两个根” | [预印本](preprints/lean-certified-2026-10/entropy-polynomial-roots/README.md)；[新增完整 Lean 工程](formalizations/wakhare-entropy-four-roots-lean/README.md) |
| 单峰 CGF 因子猜想 | 指定严格单峰 216 次多项式，无素数阶圆分因子 | [完整 Lean 主定理预印本](preprints/lean-certified-2026-10/cyclotomic-unimodal-counterexample/README.md) |
| Ehrhart 实根性 | 指定 (132,213)-避免置换多面体族的全部维数实根性；使用已发表有限范围定理 | [完整书面证明与有理证书](notes/ehrhart-uniform-real-rootedness/README.md)；非完整 Lean |

## 高斯几何与分区极值

| 研究线 | 结果与范围 | 证明／阅读入口 |
| --- | --- | --- |
| 高斯块范数与 PSD 二次型乘积推论 | 任意有限维 centered Gaussian 块、PSD 协方差／二次型、全部正实幂与全部等号；复高斯含 improper 情形 | [完整书面推论与独立内部核读](research/written-breadth-20261014/README.md)；归属 Ouimet–Greaves 2609.20234v1 外部定理，未 Lean 化，不计新的原 GPC 解答；全实自由度 Wishart 行列式问题仍开放 |
| 等质量全部 k | 精确一阶矩上界、足够维数下的最优值和全部等号情形；低维严格性 | [署名预印本](preprints/gaussian-equal-cells-2026-10/README.md)；基于已发表多泡定理的完整书面证明，全部 k 的 Lean 尚未完成 |
| 等质量四胞全局定理 | 所有 d≥3 的协方差变形锐界与正四面体等号分类；独立解决四胞全局端点 | [独立预印本与审计](preprints/gaussian-four-cell-global-2026-10/README.md)；解析端点未完整 Lean 化 |
| 三胞独立形式化 | 实际等质量高斯分数分区的锐界、等号分类及低维严格不等式 | [完整构建与公理审计](verification/gaussian-three-cell-independent-ci-2026-10-08/README.md)；源码在记录中的固定研究分支提交 |
| 任意正质量向量 | 质量依赖矩阵度量下的锐重心椭球不等式；不是普通平方重心和的任意质量猜想 | [完整书面证明、部分 Lean](research/gaussian-prescribed-mass-centroid-ellipsoid/README.md) |
| 任意质量原猜想反例 | 对每个 0<p<1/4 的四胞质量族，平移或旋转的正四面体分区严格非最优；已冻结为独立预印本 | [预印本与 DOI](preprints/gaussian-fixed-mass-propeller-counterexample-2026-10/README.md)；精确算术与部分 Lean |
| 高斯优化原始—对偶 | 真实高斯测度上的平衡价格、唯一性与原始—对偶取到 | [完整 Lean 工程](formalizations/gaussian-measure-primal-dual/README.md)；几何锐比较单独处理 |
| 任意质量双碰撞包络 | 自包含书面界 U−2Q≤M≤U；hazard 核心引理、真实可测集全局上界及末单元熵界已 Lean 化 | [解析核心与本轮空内核重放](formalizations/gaussian-mass-envelope-progress/README.md)：9 模块、47 入口、53,046 声明；阶梯下界及完整主定理仍未 Lean 化 |

## 单纯形稳定性与投影体几何

| 研究线 | 结果与范围 | 证明／阅读入口 |
| --- | --- | --- |
| 单纯形稳定性与锐指数 | 所有 d ≥ 3 的上界，指数 1/(d−1) 不可改进；显式常数不声称最优 | [完整 Lean 主定理预印本](preprints/lean-certified-2026-10/sharp-simplex-stability/README.md)；[上界工程](formalizations/sharp-simplex-upper-bound/README.md)与[截角锐性工程](formalizations/simplex-truncation-sharpness/README.md) |
| 改进稳定性常数 | 完整书面改进与整合；较早常数的完整 Lean 不自动覆盖新常数 | [整合论文与证明范围](manuscripts/sharp-simplex-stability/README.md) |
| 直积／join 递归优化 | 同质独立元数分类、谱增长和等号结构，限定在所述递归类 | [005 编号稿](preprints/005-simplex-product-optimum/README.md)；[独立证明与次优分类](notes/independent-arity-simplex-recursions/README.md) |
| 嵌套层级与首次必要维数 | 构造深度的严格层级；递归类中首次需要嵌套的维数为 55 | [55 维精确证书](notes/projection-first-nesting-d55/README.md)；[深度分离](notes/two-layer-projection-depth-separation/README.md)；非所有凸体的全局优化 |

## 有限群、置换作用与染色多项式

| 研究线 | 结果与范围 | 证明／阅读入口 |
| --- | --- | --- |
| 圆排列交换距离：对径旋转中心化子 | 所有奇数 m≥3 的中心化子循环移位至少 4 环；奇素数 p 时精确最大交换距离为 2p−4；不涉及无对称约束的完整 t(2p) | [完整书面证明与独立穷举](research/circular-sorting-antipodal/README.md)；未 Lean 形式化 |
| 周期图无限对数凹性 | 全部 n ≥ 3；当且仅当 3 ≤ n ≤ 11，所有负例也已形式化 | [预印本](preprints/lean-certified-2026-10/cycle-chromatic-classification/README.md)；[完整 Lean 工程](formalizations/chromatic-cycles-all-n-lean/README.md) |
| 通用轨道原始—对偶 | 任意有限群作用的有理最优证书与锐性 | [完整 Lean 主定理预印本](preprints/lean-certified-2026-10/orbital-primal-dual/README.md) |
| 每个有限 (n,k) 的精确公式 | 有限枚举的有理行列式最大值公式；不是无需取最大值的简单闭式 | [完整书面证明与整数实现](notes/sharp-robust-permanent/universal-exact/README.md)；全公式 Lean 未完成 |
| 固定秩渐近与有限分类 | 全固定 k 的锐一阶渐近，及指定有限范围的精确分类 | [独立论文阅读入口](notes/sharp-robust-permanent/focused-paper/README.md)；[证书与验证范围](notes/sharp-robust-permanent/VERIFICATION.md) |
| 所有子集秩同时约束 | n ≥ 6 的通用精确值 5/14，中间秩条件与全部秩条件等价 | [完整书面证明](notes/johnson-short-cycle-spectrum/ALL_RANK_SHARP_FIVE_FOURTEENTHS.md)；[两个精确 checker](notes/johnson-short-cycle-spectrum/VERIFICATION.md) |

## 二次整环、素元步长图与筛法

| 研究线 | 结果与范围 | 证明／阅读入口 |
| --- | --- | --- |
| 全二次整环有界步长 | 每个固定步长界下分量一致有界；不声称形式化有效数值界 | [完整 Lean 主定理预印本](preprints/lean-certified-2026-10/quadratic-order-moats/README.md)；[002 稿件](preprints/002-quadratic-order-moats/README.md) |
| Z[√−2] 小步长精确图 | D < 2 时最大分量为 3；2 ≤ D < √6 时为 7 | [小半径证明](notes/sqrt-minus-two-sharp-moats/README.md)；[半径 2 跳跃证明](notes/sqrt-minus-two-radius-two/README.md)与精确 checker |
| 范数 6 步长的筛法最优 | 所有有限主理想筛的精确最优界为 197；真实素元图仅知 90 ≤ B_D ≤ 197 | [完整筛法证明与证书](notes/sqrt-minus-two-exact-sieve-optimum/README.md)；[B_D=197 的条件定理](notes/sqrt-minus-two-conditional-prime-197/README.md)依赖未证明的 Schinzel H |
| 一般 CRT minimax | 任意维格点的有限筛最优值等于最大局部容许连通形状大小，并证明有限取到 | [完整书面证明](notes/periodic-sieve-admissibility-minimax/README.md) |
| Eisenstein 素元图 | 指定六步／八邻域图的最大分量 48、132 及锐筛周期分类 | [完整书面证明与精确证书](notes/eisenstein-prime-components/README.md) |

## 相似性、非线性避让与不可嵌入紧集

| 研究线 | 结果与范围 | 证明／阅读入口 |
| --- | --- | --- |
| 连续幂与可控余项避让 | 给定可数有界对数间隙族后构造大测度集合，统一避让允许的幂渐近 | [完整 Lean 主定理预印本](preprints/lean-certified-2026-10/continuum-power-avoidance/README.md)；[完整书面整合稿](notes/continuum-power-avoidance-unified/README.md) |
| 全实比值仿射几何序列 | 单个紧集同时处理所有实 a ≠ 0、b 和 0 < q < 1 | [完整 Lean 工程](formalizations/geometric-avoidance/README.md) |
| 对数密度与非线性扩展 | 所述密度／轮廓条件下的避让；不是完整 Erdős 相似性猜想 | [004 稿件](preprints/004-log-density-similarity/README.md)；[006 稿件](preprints/006-modulus-nonlinear-similarity/README.md) |
| 增长对数间隙 | 覆盖满足晚期环带填充条件的序列类；Theorem 2 及连续间隙特例已完整 Lean 内核复核；完整猜想仍未解决 | [预印本与 DOI](preprints/erdos-similarity-growing-gaps-2026-10/README.md) |
| 精确维数紧集不可嵌入 | Assouad 维数为 2 的 Banach 空间障碍构造 | [003 研究稿](preprints/003-assouad-two-zero-box/README.md) |

## 最优传输与动力学

| 研究线 | 结果与范围 | 证明／阅读入口 |
| --- | --- | --- |
| Brenier 稳定性 | 源正则性、目标矩条件及尾部敏感插值；保持各稿件独立假设 | [001](preprints/001-strongly-log-concave-brenier/README.md)、[007](preprints/007-tail-brenier-stability/README.md)、[008](preprints/008-density-overlap-phase/README.md) |
| 源重叠与边界相变 | 密度根 Sobolev 刻画与传输方法的适用范围 | [研究纲领](notes/transport-source-tail-programme/README.md)；[书面综合证明](notes/transport-source-tail-synthesis/README.md)，应用保留独立势估计假设 |
| 硬球气体随机场极限 | 正则动力学区间上的函数型涨落，列明输入定理 | [009 研究稿](preprints/009-functional-hard-sphere-fluctuations/README.md) |

## 张量刚性与分数覆盖

| 研究线 | 结果与范围 | 证明／阅读入口 |
| --- | --- | --- |
| 二元张量刚性 | 最优增长阶 p^(1/4)、四次锐常数与等号；一般阶最优常数仍开放 | [完整书面证明与部分 Lean](notes/sharp-binary-tensor-rigidity/README.md)；[边界轮廓](notes/boundary-profile-binary-tensor-rigidity/README.md)与[Fock 机制上界](notes/fock-profile-ceiling-binary-tensor-rigidity/README.md) |
| 分数覆盖／匹配谱 | 所述有限比值极限前沿与设计等号结构，引用经典设计输入 | [整合论文](manuscripts/fractional-cover-spectrum/README.md)；完整书面证明、部分 Lean |
| 小三重交的整数恢复 | 在明确区间和三重交假设下由分数最优恢复整数渐近 | [完整书面证明与部分 Lean](notes/diffuse-fractional-cover-rounding/README.md)；一般问题仍未解决 |

## 有限树储库模型可辨识性

- [有限树聚焦论文与公开准备](preprints/finite-tree-jacobian-2026-10/README.md)：[LaTeX／PDF](preprints/finite-tree-jacobian-2026-10/paper.pdf)、定理对应、源绑定内审及原证书逐项核对；未重复投稿、未创建新 DOI。

- [有限树模型定理与 Lean 工程](formalizations/hydrology-tree-core/README.md)：实际矩阵与系数 Jacobian 的全实参数分解、任意泄漏位置的精确重数和零边界奇异集、完整正目标的全部实解分类与精确计数，以及连续输入 ODE 和有符号控制桥接。范围限于文档明确的有限线性树模型；不宣称一般非线性水文问题已解决。 [独立空内核核验](verification/hydrology-tree-core-c2a2ce36/README.md) · [任意泄漏位置的完整书面证明](research/hydrology-tree-real-fibers/ALTERNATE_LEAK_JACOBIAN.md) · [已发表猜想的命题对应](research/hydrology-tree-real-fibers/PUBLISHED_CONJECTURE_ALIGNMENT.md)。

## 探索项目与文献比较

- [两储库降雨—径流可辨识性](research/hydrology-identifiability/README.md)：精确证明系数等价纤维、物理等价流反例、受控或双实验恢复三参数，以及有限并联衰减谱从前 (2k) 个矩确定速率集合（仅差标签置换）；非线性扩展仍在研究。
- [Ryser rank-six 探索](research/ryser-rank-six/README.md)：搜索模型、独立 witness checker 与受限模板排除；未证明一般反例或一般非存在性。
- [Borsuk 平衡切片记录](notes/balanced_borsuk_slice.md)：排除一个提出的构造，不解决八维问题。
- [文献比较](comparisons/)与[原创性初步筛查](research/novelty-assessment/)：区分已有输入、独立推导、加强及待确认的历史关系。

## 历史版本与审查材料

[001–009 及扩展原索引](CONTENTS.md) · [五篇整合稿](manuscripts/README.md) · [验证记录](verification/) · [Release 档案](releases/README.md) · [变更记录](CHANGELOG.md)

[RESEARCH_HISTORY.md](RESEARCH_HISTORY.md)保留整理前的全部首页文字，包括旧范围、旧验证计数和修订轨迹。冻结证明和已公开版本不因本次目录整理而改写。

## 2026-10 archived complete Gaussian notes

- [任意质量高斯质心包络](preprints/gaussian-centroid-mass-envelope-2026-10/README.md) · [DOI](https://doi.org/10.5281/zenodo.23273177)
- [高斯球冠维数下界](preprints/gaussian-spherical-cap-converse-2026-10/README.md) · [DOI](https://doi.org/10.5281/zenodo.23273187)
- [全整数高斯维数阶](preprints/gaussian-quadratic-dimension-all-k-2026-10/README.md) · [DOI](https://doi.org/10.5281/zenodo.23273190)
- [高斯维数—精度常数精化](preprints/gaussian-sharp-dimension-rate-2026-10/README.md) · [DOI](https://doi.org/10.5281/zenodo.23273198)
