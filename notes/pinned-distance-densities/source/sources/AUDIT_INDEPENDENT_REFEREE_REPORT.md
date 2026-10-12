# Pinned distance 四篇系列独立数学审查

审查日期：2026 年 10 月 8 日。

## 结论

**数学结论通过，建议作少量量词和范围澄清后进入下一轮整理。** 逐项重推后，没有发现会推翻四篇主定理的分析或几何缺口。真实嵌套构造、Frostman 控制、Hausdorff/packing 维数、两步 BV quadrature、超稀疏临界端点的取得、固定比例有限临界端点的失败、连续正子密度导出的实际距离区间、精确异常 pin 集，以及固定比例 D_K=0 的无连续版本和双指数上尾，都有有效证明。

本结论限于稿件给定的确定性乘积数字模型及明确增长条件。它不认定文献首创性，不推出任意 Frostman 集的结论，也没有解决 D_K=0 时水平 Cantor curtain 内的 L∞ 问题。报告中的推导是解析检查；文件哈希或附带数值脚本不作为数学证明。

需要修正的主要表述是第二篇摘要对 α=4/3 的非 L^{2+ε} 量词：该不属于结论适用于 p₁∈H 的 pins，特别是 E_-，不能无条件覆盖整个 pin 矩形。p₁∉H 时原始密度实际上有界连续。正文的证明范围是正确的，第四篇也已给出正确完整分类。

## 1 审查对象及冻结状态

以 `research_math/round8_pinned_pin_strata_20261008/RESULTS_INDEX.md` 为入口，完整阅读并逐式检查：

1. `research_math/round8_pinned_traintrack_repair_20261008/TRAINTRACK_POSITIVE_REPAIR.md`，以下称 A。
2. `research_math/round8_pinned_phase_diagram_20261008/FULL_PHASE_DIAGRAM_AND_INTERVALS.md`，以下称 B。
3. `research_math/round8_pinned_fixed_ratio_20261008/FIXED_RATIO_ENDPOINT_SWITCH.md`，以下称 C。
4. `research_math/round8_pinned_pin_strata_20261008/EXACT_PIN_STRATA_AND_BOUNDARY.md`，以下称 D。

另核对了原构造 `research_math/common_pin_traintrack_received/source/nested-train-track-obstruction.md`，确认 A 使用的是同一数字位置规则、同一固定前缀条件化以及原来已允许的超稀疏条件，没有暗换源测度。

审查开始时实际 SHA-256 与索引完全一致：

- A：`aa85b4e46f8752754ce187d8413d200763d87639997f73b0782f874eefb79f81`
- B：`d91c8031c1ab5fecd2980d9048b3f630e2fc925882b9a052f3440a9649ccb0a7`
- C：`4ab70460deb7c4cce215ab442b2590017001dfbb3ffc4952c5ab81787eef3505`
- D：`0fed1a945c4640ae29adddba7947fe99ab3eaf5bf4c90f2857092b26a53ffb72`

没有修改四篇原稿、运行大型 Lean 构建或发布材料。下面的验证不依赖 `check_phase_identities.py`。

## 2 真实构造和维数

统一记 a=(α−1)/2、b=α/2、c=1−b；所以 b−a=1/2，a+c=1/2。每一阶段中水平自由位置为 [1,aL]∪(L/2,L]，垂直自由位置为 [1,bL]。有理 α 和指定整除条件确实使全部端点为整数；固定比例 L_j=K n_{j−1} 也保持这一条件。

在阶段端点 n，水平和垂直自由数字数都恰为 bn。前 k 位条件化之后，每个占用水平/垂直 n-cylinder 的质量恰为 2^{k−bn}；二维质量为 2^{2k−αn}。条件化仅带来固定常数，没有阶段积累的质量误差。

局部自由数之和为

    2l,
    l+aL,
    2l−cL,
    l+(α−1)L,

分别对应分点 aL、L/2、bL、L。每一段均不少于 αl，且端点 l=L 为 αL。故任意深度 N 的质量上界是 C·2^{−αN}。半径相当于 2^{−N} 的球只碰到有界数目 dyadic squares，得到真正的 α-Frostman 估计；端点占用数给出 dim_H E_±=α 的反向上界。这里没有用“数值 profile”替代几何球计数。

### 超稀疏 packing 维数

阶段开始的 aL 位两坐标同时全自由。在任意固定 cylinder 中，深度 n+aL 时新增占用格数为 2^{2aL}，且 L/n→∞，故每个固定 cylinder 的 upper box dimension 为 2。每个非空相对开集含一个足够深 cylinder；对任意可数 cover 取相对闭包，并用 Baire 定理，可得某个覆盖件 upper box dimension 至少 2。因此 packing dimension 的论证成立，不只证明了 upper box dimension。

### 固定比例 packing 维数

对于 L=Kn，二维自由数与深度之比在各线性段单调。三个谷值 l=0,L/2,L 都是 α；候选峰为

    B₁=(α+2aK)/(1+aK),
    B₂=(α+(3b−1)K)/(1+bK).

交叉相乘后，B₁−B₂ 的分子恰为 a(1−b)K²>0，线性项抵消。因此 C 的 β_K=B₁ 正确。固定 cylinder 有相同上盒维数，再用上述 Baire 论证，得到 dim_P E_±=β_K<2。

### 水平集及 curtain

水平自由数至少 (α−1)N，因此 κ 无原子且满足 κ([u−ε,u+ε])≤Cε^{α−1}。坐标端点覆盖的总长度至多 C2^{−(1−b)n_j}→0，故两个坐标支持均 Lebesgue 零测；证明没有偷偷保留绝对连续坐标。

超稀疏水平自由数比例在 n+L/2 趋于 2a=α−1，在 n+aL 趋于 1。因此

    dim_H H=α−1,   dim_P H=1,
    dim_H(H×[0,η])=α,   dim_P(H×[0,η])=2.

固定比例中，水平自由数比例的谷峰分别为

    s_K=(b+aK)/(1+K/2),
    t_K=(b+aK)/(1+aK).

谷值 s_K≤b，峰值 t_K≥b，故未漏掉阶段端点。水平 s_K-Frostman 控制给 Hausdorff 下界，谷值覆盖给上界；固定 cylinder 的上盒维数是 t_K，Baire 给 packing 下界。乘一整段区间后，Frostman 乘积、网格覆盖及同样 Baire 论证分别给

    dim_H B=1+s_K,   dim_P B=1+t_K.

不需要一般情况下未必等号成立的任意 fractal product dimension 公式。

## 3 两步 BV quadrature 的独立检查

本系列的关键输入确实是几何解析估计，而非 Frostman 指数。父方块边长 h=2^{−n}，真实替换参数为

    A=2^{aL},   B=2^{bL},   w=2^{−L/2},   v=2^{−L},
    Bw=A,      Bv=2^{−cL}.

水平初始自由位选择 i/A，末半段自由位加 filled tail 填满宽 w 的水平区间；垂直初始自由位选择 l/B，filled tail 只填宽 v。因此替换确实是稿件的 ξ_{A,w}×ζ_{B,v}，不是仅具有相同子代数的另一个排列。

对每个等分 bin 质量为 1/N 的概率，BV quadrature 误差≤Var/N，直接由逐 bin oscillation 求和成立。在本应用，比较测度均在 bin 内绝对连续，端点代表元不会制造额外项。

令局部输出 t=r/h。对相对水平坐标 u，有

    ∂t/∂u=(X−p₁)/r.

因此水平 coarea 密度确为 (1/w)r/|X−p₁|，没有漏掉 h。h^{−1} 只在最后从 t 密度还原为物理 r 密度时出现。

固定 r 时，水平根为 X−p₁=±√(r²−(Y−p₂)²)。由于 Y−p₂≥v₀>0，各分支随 Y 单调。单条水平 strip 和 |X−p₁|≥ε 截断在每个分支上留下一个区间。倒导数在其上单调，零延拓的总变差≤两倍上确界。两个分支合计≤4D₀/(εw)。垂直 quadrature 故付出 4D₀/(εBw)。

垂直坐标换成均匀后，只有一个垂直根，倒导数 r/(Y−p₂)≤D₀/v₀。允许的水平变量在 pin 左右分别至多一个区间，变差≤4D₀/v₀。水平 quadrature 付出 4D₀/(v₀A)。还原物理尺度恰得 A (3.1)/B (4.1)。

对 ε=h/A，每条 strip 保留部分的最小水平距离为 d_i≥h/A。等距 coarse bins 按 pin 左右排序后，除有界个近邻外，第 l 个 bin 的距离≥c·l h/A；pin 位于父方块之外同样成立。因此

    (1/A)Σ d_i^{−1} ≤ C h^{−1}log(2A).

把这一步放在对 strip 求平均之前，恰得改善后的

    C D₀[(h v₀A)^{−1}+log(2A)/(h²Bw)].

两步估计都先比较同一 pin、同一 mask 下的正测度再取差。父质量加权相加时总权重为 1，确实没有 cell-count 损失。

## 4 正 mask 极限 全 pin 量词和连续密度

固定 ε 时每阶段 L∞ 增量≤C(1+ε^{−1})2^{n−aL}。超稀疏下可求和；固定比例下 aK>1 使其为 C(1+ε^{−1})2^{−(aK−1)n}，也可求和。初始 filled-tail 密度有限，故得到实际一致 L∞ 极限。

识别该极限所需的不连续测试函数问题已正确处理：每个 p 的两条边界线 y₁=p₁±ε 都是 μ 零测，因为 κ 无原子。弱收敛可用于连续距离测试函数乘 mask。所得测度与 L∞ 极限一致；全部输出落在同一有限区间，故同时有 L¹ 收敛。

这个论证逐个适用于任意 p，且估计常数与 p 无关。没有从“几乎处处 pin”升级成“每一个 pin”的漏洞。原始 law 的绝对连续性由 ε↓0 的递增正子测度以及 μ{y₁=p₁}=0 推出，也适用于整个 pin 矩形。

有限 filled-tail 密度 f_j 为有限个矩形示性函数的线性组合。极坐标公式

    g_{j,ε}(p,r)=r∫ f_j(p+rω(θ))1_{|r cosθ|≥ε}dθ

在 r>0 时联合连续：圆与有限矩形边界、mask 边界的交点角度都只有有限个，逐角几乎处处收敛和 dominated convergence 合法。r=0 邻域因统一垂直分离而恒为零。每个连续 r-fiber 的 supremum 等于 essential supremum，因此原 L∞ 增量估计提升为连续代表元的一致 supremum 估计，极限联合连续。这一步证明了连续版本，而非只证明“逐 pin 存在一个有界代表元”。

## 5 从连续正子密度到真实距离区间

选择固定 ε₀ 使丢失质量≤1/2。每个 pin 的连续非负子密度质量≥1/2，且支持于同一长度 W 的输出区间。因此某个 r_p 处密度≥1/(2W)。联合连续性在紧 pin/output 域上给统一模量，从而同一个 δ>0 对所有 p 保证 r_p 附近密度≥1/(4W)。

子测度来自实际 μ 的正限制，其支持包含于紧集 D_p(E_+)。故整个正密度区间都属于真实距离集，不只是属于有限近似或距离集的某个测度论版本。交换上下矩形时只改变垂直导数符号，绝对值估计不变。B 的所有 pin 距离区间以及 C 在 aK>1 下的区间结论均成立。

这里统一的是区间长度下界，区间位置允许依赖 p；不应改写为所有 pin 共享同一个距离区间。

## 6 超稀疏精确 Lq 端点

对原始 stage 增量，以 ε_j=h/A 分成外带和内带。外带由 harmonic quadrature 给

    C(1+L)2^{2n−aL},

在 L/n→∞ 下可求和。

内带是全局估计而非逐 cell 最坏值。其长度 2h/A 只碰到有界数目的全局对齐 coarse bins；每个已占用 bin 质量恰为 C2^{−bn}/A。因此当前与上阶段 horizontal band mass 都满足

    M≤C2^{−bn−aL}.

垂直 filled-tail 密度上界为 H_j=C2^{c(n+L)}，H_{j−1}=C2^{cn}。全局乘积结构使横向 mask 不改变垂直条件分布。由严格单调的垂直 coarea，band distance density 的质量为 M、上界≤CMH，故

    ||band density||_q ≤ C M H^{1−1/q}.

当 1<α<3/2，q_*=(2−α)/(3−2α)，σ_*=1−1/q_* 满足 cσ_*=a。于是上式恰为

    C2^{−bn−aL+a(n+L)}=C2^{−n/2}.

这确实可求和，证明有限临界指数被取得。α=4/3 时 q_*=2，不是“所有低于 2 的指数”的替代结论。

当 α≥3/2，取 q=∞，相同公式为

    C2^{−(α−1)n}2^{−(α−3/2)L}≤C2^{−n/2}.

因此 α=3/2 的有界连续结论是有效端点估计，不是把有限 q 形式上送向无穷。无 mask 的连续有限 stage 密度一致收敛，给原始密度的联合连续性。

对于 p₁∈H，不需任何 p₂ 的 Cantor 条件。选含 p₁ 的水平 track，质量 m=2^{k−bn−aL}，水平宽度 2^{−n−L/2}。垂直支持可用 2^{b(n+L)−k} 个长度 δ=2^{−n−L} 的区间覆盖，且平方水平误差≤C2^{−2n−L}≤Cδ。因此距离像 U 的长度≤C2^{−c(n+L)}。Hölder 给

    ∫_U g_p^q ≥ c_q·2^{[q(c−a)−c]L+[q(c−b)−c]n}.

q>q_* 时 L 系数严格为正，超稀疏迫使右端发散。q=q_* 时残余指数恰为 −q_*n/2，与上界的 2^{−n/2} 一致，不存在上下界冲突。

## 7 固定比例的临界转换

令 L=Kn、D_K=K(c−a)+(c−b)=K(3/2−α)+1−α。外带 supremum 增量为

    C(1+Kn)2^{−(aK−2)n},

在 C、D 主定理统一假设 aK>2 下可求和。内带 Lq 增量指数精确为

    D_K−c(K+1)/q.

因此：D_K>0 时，q<q_K=c(K+1)/D_K 有上界；D_K<0 时可取 q=∞；D_K=0 时每个固定有限 q 都有上界。

q_K 确实大于 1，因为 c(K+1)−D_K=b+aK>0。不存在临界指数落在 Hölder 适用范围之外的问题。

固定比例的同一 track 下界为

    ∫_{U_j}g_p^q ≥ c_q·2^{[qD_K−c(K+1)]n}.

在 q=q_K 时，右端保持严格正的常数，而 |U_j|→0。若 g_p^{q_K} 可积，Lebesgue 积分的绝对连续性强迫左端趋于 0，矛盾。无需 U_j 两两不交或单调嵌套。C 特别强调局部积分而非整个 Lq 范数，这正是端点失败成立的关键。

C (5.5) 的改进也成立：每个条件外带输出长度 O(h)，先利用此长度再用 Minkowski，可把指数 2−aK 改善为 2−1/q−aK。因而有限 q 的充分条件 aK>2−1/q 正确。但这些只是充分增长条件，不证明 aK=1 或 aK=2 为模型真实锐阈值。

例 α=13/10、K=14 有 D_K=5/2、q_K=21/10、β_K=55/31；超稀疏同 α 有 q_*=7/4、packing dimension 2。所列不同 L² 行为成立，不能据此断言 packing dimension 单独决定密度相图。

## 8 完整异常 pin 分类

H 紧，故 p₁∉H 时 d=dist(p₁,H)>0。在其邻域固定 ε=d/2，mask 对整个实际源支持恒为 1。因此原始密度局部联合连续并有界，||g_p||∞≤C/d。不存在未覆盖的、固定 off-H pin 仅因“逼近 H 速度”产生的第三种 membership stratum。

另一方面，track 下界对所有 p∈B=H×[0,η] 成立，包含 coding 边界点，p₂ 只需统一垂直分离。因此 D 给出的精确分类正确：

- 超稀疏 1<α<3/2：Bad_q=∅ 对 1≤q≤q_*；Bad_q=B 对 q>q_*，包括 ∞；Bad_C0=B。
- 超稀疏 α≥3/2：上述异常集均为空。
- 固定比例 aK>2、D_K>0：Bad_q=∅ 对 q<q_K；Bad_q=B 对 q≥q_K；Bad_C0=B。
- 固定比例 aK>2、D_K<0：上述异常集均为空。
- 固定比例 aK>2、D_K=0：有限 Bad_q 全为空，Bad_C0=B；只能断言 Bad_∞⊆B。

连续密度在紧输出支持上必有界，故在有限临界区间中“非连续”的推断有效。这里的异常是自然原始 law 的较强正则性异常，绝不是距离集零测或没有区间的 pins。

## 9 D_K 等于零的边界

### 无连续版本

源的最小垂直坐标是 r₀=1−η。对 p₁∈H，点 (p₁,r₀) 属于源支持，所以最小距离确为 r_min=r₀−p₂。把同一水平 track 与最低垂直深度 n+L cylinder 相乘，质量为

    2^{2k−2bn−(a+b)L}.

距离像位于 [r_min,r_min+Cδ_j]，δ_j=2^{−n−L}。质量除以 δ_j 为

    2^{2k}2^{(1−α)n+(3/2−α)L}=2^{2k}2^{D_Kn}.

D_K=0 时该比值固定为正。连续密度若存在，在 r_min 左侧必须为零，连续性使其在 r_min 也为零，进而上述 shrinking interval 内质量是 o(δ_j)，矛盾。论证对每个 p∈B 都有效，但不排除支持左端的有界跳跃。

### 矩和尾上界

D_K=0 时，band Lq 增量≤C2^{−c(K+1)n/q}，且 C 可对所有 q≥1 统一。初始 stage 及可和外带也有与 q 无关的常数。因为 n=n₁(K+1)^{j−2}，

    Σ_j exp(−A(K+1)^j/q) ≤ C(1+log q).

取第一个 A(K+1)^j≥q 的 j 即可严格分成 O(log q) 个前项与统一可和尾项。因此 sup_p||g_p||_q≤C log(e+q) 成立。令 q=exp(T/(4C)) 并取充分大 T，Markov 得 2^{−q}，所以双指数上尾成立。再取 0<c₃<c₂，用层蛋糕积分即可证明有限区间上的 exp(exp(c₃g)) 可积。

这些均是上界，不是 ||g||_q 的双边渐近。它们不能证明无界，也不能证明有界。把“logarithmic moment growth”改称“logarithmic moment upper bound”更准确。

恒等式 D_K=(K+2)(1/2−s_K) 以及 q_K=(1−s_K)/(1−2s_K) 都正确。边界 α=3/2−1/[2(K+1)] 给 s_K=1/2、t_K=(K+1)/(K+2)，故 dim_H B=3/2、dim_P B=2−1/(K+2)。若维持 aK>2，整数 K 必须至少为 9；稿件示例 K=9、α=29/20 合法。

## 10 其余结果和不能扩展的范围

A 的固定正 mask 产生 ||g_ε||∞≤C/ε、删质量≤Cε^{α−1}，于是原始密度有 weak-L^α 控制，证明正确。更强有限临界上界与它相容。

任意 0≤F≤M_ε 的推前密度由正测度支配，故平方 L² 范数≤(C/ε)m。归一化确实除以 m²，得到 C/(εm)，没有遗漏质量代价。任意进一步 pruning 只保留正 domination；局部 cell 的保留质量另需验证，原稿对此的限制正确。

有界扰动的 collision-window 扩大、共享 pin 的同一性以及相应 whole-low-pass 控制均成立。可以直接用三角形正定核证明 whole-low-pass 比较；不产生任意 mask 的高频壳层衰减。

A (8.2) 的非均匀模板充分条件也成立：将每个条件误差以 m_Q 加权得 (m_Q/h_Q)[A_Q^{−1}+(B_Qw_Q)^{−1}]；可和性、初始有限 filled-square law、边界无原子性足以通过极限。该版本只给固定 mask、原始 AC 及相应 weak-L^{1+β}，不能单凭此条件继承精确 q_* 端点。精确相图所用的全局乘积结构和对齐 bin 质量是额外实质输入。

## 11 可实施的澄清建议

这些建议不要求重做数学主证明，且本次没有直接改原稿。

1. **B 第 20 行的 α=4/3 摘要量词。** 改为：“The original laws are uniformly L² for all p∈P_-; for every p∈E_- (indeed, every p with p₁∈H), they fail every L^{2+ε}.” 这样不会与 off-H 有界结论冲突。
2. **B 第 10 行的 ‘exact upper integrability’。** 可写为“uniform endpoint upper bound on P_-”，并另列 B 上的 sharp fiber classification。整个矩形里的每条 law 并不都只有同一有限积分范围。
3. **D 第 7 节标题及索引的 moment 描述。** 明确是 O(log q) upper bound，尚未给 matching lower growth。双指数也是尾上界，不是尾部渐近。
4. **所有非 membership 概述保留 pin 域。** 尤其相图表和摘要，不应把 E_- 或 B 上的下界移成整个 P 上的下界。
5. **引用路径的起点。** A 中旧构造路径是相对 `research_math/` 的引用；若作为可单独解压的系列包，使用明确包根路径或附带原构造，避免被误认为缺文件。主证明 B–D 已足够自包含，数学不受影响。
6. **版本和状态。** 不改冻结文件可保留本报告作为独立审查附录；若将来出修订版，再更新“尚无 independent audit”的说明和哈希，勿把新文字加入旧冻结件。

## 12 仍开放及未验证事项

- D_K=0、p₁∈H 时的原始 L∞ membership，以及 Bad_∞ 的精确集合，仍未由本系列决定。
- 固定比例有限 q_K 的 weak-L^{q_K} 或更细 Lorentz 端点、边界 O(log q) 的 sharpness，没有证明，也没有在主定理中被冒称已解决。
- aK>1 和 aK>2 是所用估计的充分条件，不是已证明的必要阈值；等号或更小 K 的相图不在本次通过范围内。
- 任意 irrational α 的无 rounding-loss 延伸、任意旋转模板、非乘积精确端点、任意既有 pruning 的局部质量保留，以及 unrestricted common-pin recursion 均未解决。
- 文献首创性没有完成全面审查。本次只核对主要历史归属：[Guth–Iosevich–Ou–Wang, On Falconer’s distance set problem in the plane, §1.2](https://arxiv.org/html/1808.09346v1) 确有近 track 峰与远 track 平滑的区分；不能把该直觉宣称为本系列首次提出。其一般 good-source 构造也不同于这里的固定正 band restriction。

**最终建议：保留四篇作为通过独立解析复核的具体模型结果，合并整理时修正摘要量词并突出 fixed-ratio 与 superlacunary 的端点差别；D_K=0 的 L∞ 问题继续作为真实开放点。没有证据要求撤回任一主定理。**
