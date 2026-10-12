# Round5 弱供给 → 原窗口 → 真正 finite sieve：独立源码数学语义审查

日期：2026-10-07 UTC。审查模式：只读新源码；**没有编译、运行 Lean、重建 olean，或修改 frozen/source 文件**。

源码根：`source/lean/`。下文 `E/` 表示该根下 `Entry002/`；`M/` 表示 `references/pinned-mathlib/Mathlib/`。本报告审查弱供给到 finite sieve 的数学对象、证明接口和关键证明体；不把既有日志当成本轮 kernel replay，不对本轮父审计负责的全递归依赖/二进制一致性作替代认证。

配套可复核证据：`WEAK_WINDOW_STATIC_CHECKS.json` 绑定 57 个涉及源文件的 SHA-256、十个重放文本比较结果和有理数证书；生成器 `helpers/weak_window_static_checks.py` 只读源码，输出该 JSON，绝不调用 Lean。三份新增文件合计约 42 KiB。

## 结论

**源码数学语义 PASS，未发现阻断性缺口。** Round5 中这条链已经不只是传统数学 blueprint 或条件接口：

1. 真正有理素数 Dirichlet 级数的正 upper supply，推出一个固定 `δ>0`、固定 `β>0` 的实际 good-bin harmonic-log cofinal 下界。
2. 新证明用初等 cutoff/几何折扣和 Chebyshev 上界，绕开旧 blueprint 的 Abel 分部积分；没有调用 PNT，也没有推断自然密度或每个充分大 bin 的密度。
3. `log100` 精确有理证书、196-block 覆盖、`m : ℤ` 转 `m : ℕ`、固定低端删去损失、有限双计数、实际正权重模 K thinning 均有证明。
4. `ArithmeticCore` 真的是原 A1–A4 四字段；几何/熵链已以新四字段参数重放，不是把旧五字段接口包装成四字段。
5. 空窗口被保留；rate 按所有实际选中 bins 汇总。`W` 先于 eventual 阈值，`m,J` 先于有限 prime pool，pool 先于 `∀ walk`；同一个真实 `TimeLaw` 上的 residue-word charge 与 telescope 相矛盾。
6. 终点是原 `avoiding` 集合和原 `latticeGraph` 的 `UniformComponentBound ... (S.prod id ^ 2)`，不是仅仅一个新命名的抽象“sieve”谓词。
7. `E/WeakFiniteSieveConsequences.lean:10–15` 已用本轮 proved bridge 消去显式 `hbridge` 参数，给出 `weakFiniteSieveTarget_proved` 和 `weakFiniteSieveNoWalkTarget_proved`。

唯一发现是**非阻断的注释过时**：部分早期接口注释仍写“open/currently open”，而最终组装已经闭合，详见末节。

## 1. 真正审的对象与范围

逐一读取了 `WeakSupply*` 的全部十个文件，`ArithmeticCore`，新窗口 mass/rate/support/sieve/target 文件，以及四字段重放链的声明、关键证明体和完整源码差分。对十个 `WeakCore` 重放模块做了有界规范化文本比较，结果十个全部一致；规范化范围只包括 import/comment/命名空间、`ArithmeticInterface → ArithmeticCore`、共享定义的显式限定名、等价的显式 theorem qualification，和两个没有重新定义的共享常量。不存在算术/几何不等式、概率 law、量词、证明步骤的额外修改。该比较不代替名称解析或 kernel 检查。

另直接读取了所依赖旧模块中真正调用的纯窗口选择、numerics、Chebyshev、backward batch charge、同 law telescope 和 periodic-component 声明与关键证明体。旧大文件中仍存在的 A5 专属 theorem 不因被 import 就成为新证明的 premise；本报告区分了“模块被导入”和“旧强命题被使用”。

底层 Bool-cube、信息论和二维 frame 的所有历史证明没有在本任务中从零重新证明；本次针对的是新四字段重放有无语义换题，以及弱 supply 与这些真实底层对象是否正确接合。

## 2. 输入确实是实际 prime sum、固定 good bins 与四字段 core

### 2.1 实际有理素数，而非代理 coefficients

- `E/WeakSupplyInterfaces.lean:15–21`：`supplyPrimeCoefficient P n` 是实际集合 `n∈P` 的 0/1 指示函数；`supplyPrimeDirichletSeries P s = ∑' n, coefficient/n^s`。
- 同文件 `23–33`：对每个 `s>1` 证明真正 summable，依据有界 coefficients 的 LSeries absolute-convergence bound。不存在拿 nonsummable `tsum=0` 默认值充当分析结论的问题。
- `E/WeakSupplyDirichletGoodBins.lean:12–14` 明确要求 `∀p∈P, Nat.Prime p`。因此 0、1 的除法约定不影响实际输入。
- `E/Sieve.lean:16–20` 的 `SignedResidueData` 存储真实 `Nat.Prime`、真实 additive maps `L →+ ZMod p` 与 onto 性；最终 bridge 的 `hP` 由 `data.prime_mem` 提供（`E/WeakCoreWeakTargets.lean:17–19`）。

### 2.2 “positive upper” 量词正确

`E/WeakSupplyInterfaces.lean:44–50` 的输入是：存在固定 `d>0`，对任意 `η>0` 都存在 `0<ε<min(η,1/2)`，使 `d log(1/ε) ≤ D_P(1+ε)`。这是 cofinal 正 normalized 下界，**不是**所有小 ε 的 eventual 下界。ε<1/2 保证规范化对数严格正。

`goodDyadicBins`（同文件 `52–55`）就是 `Icc 2 J` 中满足真实 batch cardinality 不等式

`δ 2^j / log(2^(j+1)) ≤ #(dyadicPrimeBatch P j)`

的实际 indices。`PositiveUpperLogGoodBinSupply`（`60–63`）为 `∃δ>0, ∃β>0, ∀J₀, ∃J≥max(J₀,2), β log J ≤ Σ_good 1/(j+1)`。固定 δ、β 在所有 `J₀` 之前，且 `log J>0`。这确实给正 harmonic-log limsup；没有用 limsup 一词掩盖逐 J 改阈值。

`E/GenericDyadicDensity.lean:29–48` 的 dyadic batch 是实际 `P∩[2^j,2^(j+1)]`。包含上端不破坏证明：series 分解只需上界，采用 `Nat.log 2 p` 指派每个 prime；所选 good bins 从 j≥2 开始，端点的大于 2 的二幂本来也不是 prime。

### 2.3 Core 到底是哪些字段

`E/ArithmeticCore.lean:15–28` 只有以下四字段，逐字对应 `E/Sieve.lean:36–47`：

1. `crt`：任意有限 actual prime set 和符号选择的 joint residue map surjective。
2. `paired_kernel`：两核交恰是 `pL`。
3. `collision`：非零 kernel vector 的实际 planar norm 至少 `c sqrt p`，固定 c>0。
4. `eligible_product`：primitive lattice direction 的 eligible prime product 至多 `C ‖v‖²`，固定 C≥1。

旧 `density` 位于 `E/Sieve.lean:48–50`，在 core 中完全没有对应字段。`ArithmeticInterface.toArithmeticCore`（`ArithmeticCore:30–34`）只是单向投影，没有 core→strong 的 coercion。源码搜索没有发现反向 instance 或强接口制造器。

实际 quadratic-order core 的构造 `ArithmeticCore:39–58` 只从 principal residues 的 norm/kernel/pair、`signedResidueData_crt` 和 norm-based collision/product 得到四字段；并未调用要求 `hdensity` 的旧 `order_interface_of_principal_residues`。

## 3. Dirichlet → 固定 δ、β 的 good-bin supply

### 3.1 全部上界只用初等 Chebyshev

- `E/WeakSupplyDyadicChebyshev.lean:9–40`：真实 `Σ log p` 上界给 `#B_j ≤ 8·2^j/(j+1)`（j≥1）。独立复核：`#B_j·j log2 ≤ Σ log p ≤ 4 log2·2^j`，再用 j+1≤2j 即得。
- `E/WeakSupplyDyadicSeries.lean:11–30`：单独处理 j=0，得到所有 j 的 ratio cap `#B_j/2^j ≤8/(j+1)`。
- 其底层 `E/GenericDyadicDensity.lean:61–71` 调 `Chebyshev.theta_le_log4_mul_x`。随包真实 `M/NumberTheory/Chebyshev.lean:186–201` 的证明是 `theta=log primorial`、`primorial_le_four_pow` 与 floor/log 单调；**没有 PNT**。

### 3.2 分解和折扣尾部是真正的级数估计

- `WeakSupplyDyadicChebyshev:43–67` 精确写出 `2^(-εj)` factor，并逐 prime 比较 `p^(-1-ε)`。
- `WeakSupplyDyadicSeries:38–50` 证明 discounted batch series summable；`52–58` 把每个实际 prime 放进 `Nat.log 2 p` bin；`60–96` 通过任意有限 prime partial sum、finite fibers 和非负 tsum 上界得到真实 Dirichlet series 的 dyadic 上界。
- `E/WeakSupplyElementaryDiscount.lean:14–61` 对真实 `r=exp(-log2·ε)` 证明 `ε/(1-r)≤4`（0<ε<1/2）。`70–81` 对 `0≤a_j≤1/(j+1)` 建立 summability。
- 同文件 `85–114`：若 εN≥1，则 a_(N+n)≤ε，tail 被 `εΣr^n` 控制，故≤4。没有不受控制的无限换序。
- `E/WeakSupplyDirichletCutoff.lean:10–25` 乘回 ratio cap 的 8，得到 prime-bin tail≤32。

### 3.3 Good/bad split、有限初段和 cutoff 常数

`E/WeakSupplyGoodBinUpper.lean:10–49` 在 bad bins 用实际 cardinality 小于 δ threshold；在 good bins 用全体 primes 的 cap。`51–80` 的 j=0,1 初段≤16，前缀其余折扣≤1。`WeakSupplyElementaryDiscount:133–174` 以 reciprocal-log increment telescope 证明 `Σ_(j∈Icc 2 J)1/(j+1)≤1+log J`。

因此 `WeakSupplyDirichletCutoff:29–47` 得到：若 J≥2、ε(J+1)≥1，

`D_P(1+ε) ≤ 48 + (δ/log2)(1+log J) + 8 H_good(J)`。

这里 48=16+32，δ 任取非负；没有 supply 下界在上界证明中循环使用。

### 3.4 固定 δ、β 的最后提取

`E/WeakSupplyDirichletGoodBins.lean:15–21` **先于 J₀** 设

`δ = d log2 /4 >0`，`β=d/64>0`。

给定 J₀ 后，`23–46` 设 M=max(J₀,2)，取 ε 小于 `1/(M+1)` 和 `exp(-(256/d+4))`，令 `J=ceil(1/ε)`，证明 J≥M 和 cutoff 条件。`48–70` 证明

`log J ≤ log(1/ε)+1`，`d log(1/ε)≥256+4d`。

`71–78` 合并供给下界及 cutoff 上界。独立代数检查：记 L=log(1/ε)，则 `8H_good ≥(3/4)dL−48−d/2`；为了 `H_good≥(d/64)logJ` 只需右边≥`(d/8)(L+1)`，而上述 large guard 提供充分余量。常数偏松但方向正确。

**判定：这是实际 proved forward implication。** 它没有把 traditional blueprint 中的 converse equivalence 一并形式化，最终 finite sieve 也不需要 converse。

## 4. 原整数 m、原窄窗口的 196-block 证书

### 4.1 数值没有浮点前提

`E/WeakSupplyWindowLogCertificate.lean:10–30` 使用恒等式 `log100=6log2+2log(5/4)`；调用有证明余项的 `Real.sum_range_le_log_div`、`Real.log_div_le_sum_range_add`，分别在 x=1/3,N=4 与 x=1/9,N=2 处展开，得到

`4605/1000 ≤ log100 ≤4606/1000`。

本任务另以 Python `fractions.Fraction` 只读算术复核了这两个 rational partial-sum/remainder 值：下界 `352496/76545`，上界 `21150173/4592700`；二者分别在 4.605 之上、4.606 之下。该 rational 重算是辅助核对，不被当作 Lean 验证。

### 4.2 覆盖逻辑是有限格栅，不是 equidistribution

`E/WeakSupplyWindowIndependentGrid.lean:35–68` 证明 h=log(21/20)≥1/21、d₀=5L−23∈[1/40,3/100]、d₀<h。40 个区间 `[kd₀,kd₀+h]` 覆盖 [0,1]，因为 `39/40+1/21=859/840>1`。

`73–97` 对 x−196bL 取整数 floor a，对 fractional part 用该覆盖，返回 k<40 和整数 `m=a−23k`，满足窗口 index `196b+5k` 的 catch。`100–103` 证明 offsets 在各自 196-block 内。

`108–127` 用低端 margin `M+196qL+h≤x` 及 x≤N 保证同一个 catch 的 `M≤m≤N`。这是保守的固定 margin；没有遗失端点质量。`129–157` 将 L 实例化为有证书的 log100，无未证数值假设。

`E/WeakSupplyWindowAveraging.lean:21–37` 再用 M∈ℕ 与 m≥M 保证 m≥0，转成 `m.toNat`，明确证明 cast 等式。最终 base 是真实 `m : ℕ`，不是实数平移后的另一族窗口。

### 4.3 与原 window 的精确等价

`WeakSupplyWindowAveraging:12–14` 定义的是 `[m+w log100,m+w log100+h]`。`162–177` 对 j>0 通过 exp/log 精确证明该条件等价于

`100^w exp(m) ≤ j log2 ≤ (21/20)·100^w exp(m)`。

没有缩放 m、扩大 21/20 宽度、改变 base100，或修改原 schedule 的 floor/ceiling。

## 5. 正权有限平均确实产出任意大的自然 m

### 5.1 计数、平均与不重复

- `WeakSupplyWindowAveraging:41–66` 构造 `Fin q → (m,w)`，不同 block 的 w 范围不交，证明 injection，因此每个 interior atom 有至少 q 个**不同** catches。
- `74–107` 把 catch indicator 的有限 double sum 转成 cardinality×weight；`hweight≥0` 明确出现，才能乘 q 的计数下界。
- `112–141` 在非空自然区间 `Icc M N` 上用有限平均，分母精确是 `N−M+1`，返回一个 m≥M。
- `144–159` 利用 log100>h 证明 fixed m 下 catch 的 w 唯一；`182–204` 将 window double sum 与 genuine finite union 的 weight 严格等同。没有把同一 bin 在固定 m 的重复计数当成额外质量。

### 5.2 处理只沿 subsequence 有供给和巨大固定低端损失

`E/WeakCoreGoodBinWindowMass.lean:16–26` 的结论是对任意 q,M 取得某个 m≥M 和有限 actual good-bin atoms，质量≥qβ/2。

证明 `27–46` 为该固定 q,M 取 H=M+196qlog100+h，再选自然 cut，使 j≥cut 时 `log(jlog2)≥H`。`47–76` 明确令 `C=Σ_(j<cut)1/(j+1)`，在 cofinal supply 中选足够大的 J，使 `βlogJ≥2(C+β)`。移除 low atoms 后仍有

`Σ_atoms 1/(j+1) ≥ (β/2)(logJ+2)`。

`77–95` 设 `N=ceil(log(Jlog2))`，证明 M≤N、`N−M+1≤logJ+2`；注意 ceiling 所需非负性也已由 margin 证明。`96–114` 接 finite average，得到 qβ/2 下界。

因此 m 的 cofinal 性不是从“一次存在”误推出来：**每个 M 都重新选 J、N，并明确扣除依赖该 M 的有限 C**。不需要每个大 J 好，也不需要每个大 m 好。

## 6. Thinning 按真权重进行，且得到全局 separation

`E/WeakSupplyWindowIndependentGrid.lean:161–184` 使用 `exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum`，最大 residue class 保住至少 `Σweight/K`；这不是旧 `thin_bins` 的 cardinality pigeonhole。其一般型允许任意实 weight；新实际应用权重为正数 1/(j+1)，所以后续 subset lower bound 的正性有效。

`E/WeakCoreGoodBinFiniteSieve.lean:37–43` 先令 B 为全部被窗口抓住 atoms 的 finite union，再对 **整个 B 一次** 选 residue r modK，令 T=B.filter(r)，最后按 window 定义 Jw。故：

- `51–60`：`allBins W J=T`，集合不是一个 surrogate。
- `61–70`：每个被选 j 保留原窗口条件及同一个 δ-density。
- `71–74`：整个 union 上 `i<j ⇒i+K≤j`；跨窗口也成立，根本不需要额外窗口间距离补丁。
- `75–79`：thinning 后质量≥qβ/(2K)。

这比 blueprint 的逐窗口 thinning 更直接；全局同余类保证 global separation，而总权重损失仍至多 K 倍。

## 7. 真 rate、W 的选择和空窗口

`E/WeakCoreWindowRates.lean:11–24` 不是引入新信息 rate，而是对原 `windowBatchRate c j` 证明

`(c/10000000)/(j+1) ≤ windowBatchRate c j`（j>0,c≥0）。

证明展开原 rate 的 `log(2^j)=jlog2`，用 log2≤1 比较分母，方向正确。

`WeakCoreGoodBinFiniteSieve:25–35` 固定 c=topCoefficient(a)/4、R=(c/10000000)β/(2K)>0，先选 q 使 `log(#wordStepBall)+1<qR`，再令 **W=196q**。之后才 `intro M` 并调用 cofinal 窗口质量。`80–99` 得总实际 rate 严格超过 word-step alphabet budget。

`core_finite_sieve_of_log_good_bins`（`103–116`）从固定 δ、β 先选 a,K。所用 `E/GenericCommonWindowNumerics.lean:289–317` 只要求 δ>0：a=min(δ/4,1)，再选足够大 K，使 top gap 和 predecessor log-cost 均足够小。没有旧 A5 或 uniform density 参与参数制造。

### 空窗口检查

1. `CofinalSelectedWindowRateExcess`（`E/WeakCoreFiniteSieveSupport.lean:20–30`）的条件是 `∀j∈Jw`，没有 `Jw.Nonempty` 或每窗口 cardinality 下界。
2. 原 `topBlocks` 是 sorted J 的 flatMap（`E/GenericBandParameters.lean:235–236`）；空 J 得空 top block。
3. 原 `windowBlocks`（同文件 `297–305`）仍为每个 w 添加 accurate block；没有把空窗口从 schedule 移除。`commonBlocks` 仍加 bottom block（`E/GenericWindowSchedule.lean:65–69`）。
4. 本地 charge 只对 `w<W,j∈Jw` 要求结论（`WeakCoreCommonWindowCharge:93–116`）。需要的 S.Nonempty 是**选中的 prime batch** 非空，由 δ>0 的 actual local density 推导（同文件 `145–146`），不是要求所有 windows 非空。
5. 数值 tail、smoothing、length 估计只用每个已选 bin 的上界（`GenericWindowSchedule:90–111`，`GenericWindowLogBudget:187–219`），支持空窗口。
6. 所有 bins 的 union 必须非空，在 finite support `62–73` 由 strict aggregate rate excess 和 `log(#wordStepBall)≥0` **推出**，不被默默假定。

## 8. 四字段几何/熵链没有再引入旧强接口

以下重放模块逐个与原对应 Generic 文件作完整差分核对，并检查关键接点。经前述明示规范化，十个文件的剩余代码文本全部相同。

| 新文件 | 核实的真实接点 |
|---|---|
| `WeakCoreSignedArithmetic` | `40–50` joint kernel index 用真实 CRT；`148–157` 只用 paired_kernel；`271–284` 只用 collision；determinant/primitive/lattice geometry 对象不变 |
| `WeakCoreSignSeparation` | `39–54` eligible log mass 来自 A4；`57–73` fair-sign mean 来自 A2；`85–111` 接真实 Hoeffding；`434–445` separationConstant 来自该 proved existential；`450–507,834–867` 真区域/矩形 kernel probability |
| `WeakCoreFreshEntropy` | `167–212` 将矩形 kernel probability 转为真实 prefix entropy；`318–366` 从实际 residue maps 的差分性质得 fresh entropy；`371–391` 接共享 signedFreshCoordinate |
| `WeakCoreWalkFreshEntropy` | `406–436` 根据真实 ActualWalkFrame 推 fresh lower bound；并未把 frame/entropy 结论做新输入证书 |
| `WeakCoreGeometricEnrichment` | `26–39` scale structure 全是数值 inequalities；`43–61` 对同一 walk 的所有起点推 fresh lower；`91–111,141–160` 接真实迭代/共同 endpoint law |
| `WeakCoreGeometricScale` | `63–164` 从显式 floor/scale 条件构造每一字段；`169–199` uniform eventual threshold 先于批次、walk；`203–262` varying-grid guard 也显式证明 |
| `WeakCoreGeometricBands` | `27–67,108–144` 用新 core geometric chain；调用 `Entry002.WeakA5.TimeLaw.iterated_geometric_entropy` 已显式限定，避免误回旧强 theorem；`148–178` future smoothing loss 真正推导 |
| `WeakCoreWindowEntropy` | `25–61` subband + actual suffix loss；`94–140` accurate-grid guards 在 laws/walks 前证明；`144–213` middle/bottom 两 entropy 输入真实构造 |
| `WeakCoreWindowTopEntropy` | `26–45` eventual threshold 在 J、initial、walk/law 前；`49–107` selected dense batch 的 q>0、q≤card、mean及 rate-size 全推出；`139–165` top endpoint 真熵结论 |
| `WeakCoreCommonWindowCharge` | `88–116` 四字段版本地 charge；`118` 抽 A3，`120–133` 汇总新 core entropy+旧纯 numerical estimates，`181–221` 三端 entropy→真实 backward extension→同 law |

两个刻意继续共享而非复制的数值定义是原 `FreshEntropy.batchMeanLog` 和原 `displacementPackingConstant`。新源码用 `_root_.Entry002...` 明确指向它们；其定义不是旧五字段接口的投影。没有以同名新定义变换原 batch mean、entropy law 或 displacement ball。

导入的 `GenericDensityBands` 确实同时含旧 A5 wrappers，但新链用的是 `eventually_dense_dyadic_top_band_ready`、actual local batch bounds、finite pool等纯 conditional lemma；`WeakCoreWindowTopEntropy:50,69` 给入的是所选 bin 的 actual δ-bound。新 proof 中没有调用 `ArithmeticInterface.uniform_dyadic_density`、`common_window_parameters`、旧 `large_step_prime_pool_no_walk` 或旧 `finiteSieveTarget_proved`。

## 9. 先 W，再 m/J，再 S，再所有 walks

关键 executable proof 顺序位于 `E/WeakCoreFiniteSieveSupport.lean:35–98`：

1. 参数 W 已由 `WeakCoreGoodBinFiniteSieve:30–35` 在任何 M 前选定。
2. `49–52` 对这个固定 W，取 `eventually_common_window_batch_charge` 与 `eventually_actual_window_telescope_errors` 的共同自然阈值 m₀。两者都是 `∀ᶠm, ∀J, ... ∀z...`，阈值不依赖后选 J 或 walk。
3. `53` 调 cofinal selection m₀，选 m≥m₀ 和 J；`54` 才专门化两个 eventual lemma。
4. `75` 返回 `S=dyadicPrimePool data J W` 及所有成员属于 data.primes。
5. `76` 才 `intro z hz havoid hs`。因此 `∃S` 严格在 `∀z` 之前，既不依赖 walk，也不依赖起点。
6. 不同 walk 的 `commonSchedule z ...` 可以依赖 z；固定的是有限 sieve pool S。证明不需要不同 walk 共用 probability law，只需要**一个给定 walk 的全部 batch charges** 共用同一 law。

这是 cofinal good-m 与 uniform eventual local guards 的合法交接。代码没有把 cofinal 供给升级为 eventual 供给，也没有 `∀walk ∃pool` 量词逆序。

## 10. 同一 law 的真实 charge 与 telescope 矛盾

### 10.1 观测对象不是抽象替代品

- `E/GenericResidues.lean:22–29`：residue family 是真实 prime/sign `ZMod p` coordinates，`residueFamilyHom` 逐 coordinate 应用原 data.phi。
- `E/GenericWords.lean:15–23`：incrementWord 是 actual successive increments，sum 真正 telescope 成 z(t+len)−z(t)。
- `E/GenericResidueGrowth.lean:28–31`：residueWordCharge 正是 Q 上这些 actual residue observations 与 incrementWord 的 conditional mutual information /len。
- `E/GenericTimeKernels.lean:139–165`：difference kernels 是 actual walk difference laws，smoothing 是 Fin(N+1) uniform law，commonSchedule 是这些 kernels 的 genuine composition。

### 10.2 三个 entropy endpoint 被真正推导并放回同一个 Q

`WeakCoreCommonWindowCharge:135–201` 构造 S, μ, q,qmid,qbot 和 prefix law P；本地密度给 S.Nonempty，top theorem 给 q cap、mean/anchor，accurate band theorem给对**所有起点**的 middle/bottom entropy。A3 和实际 short-word numeric guard 给碰撞控制。

`202–218` 将这些 proved values 给 `exists_positive_dyadic_backward_batch_charge`。其真实类型（`E/GenericBackwardBatchCharge.lean:303–364`）要求实际 avoidance、collision、entropy和数值 bounds，返回 G⊇F、G局部新增自当前 batch 以及实际信息 rate。它没有要求旧 ArithmeticInterface 或任意 prime density。

`WeakCoreCommonWindowCharge:53–70` 证明 window factor schedule 的精确 list/kernel equality。`219–221` 用 `common_window_factor_law` 把返回的信息表达式化为

`Q=(TimeLaw.at 0).advance(commonSchedule z (commonBlocks a m W J) (windowSmoothing W m))`。

这不是“相同类型的 law”或独立挑出的 law；是字面上同一个 Q。

### 10.3 Greedy 所需 ∀F 和预算都被 discharge

`WeakCoreFiniteSieveSupport:77–95` 为每个 sorted-bin index 和任意 `F⊆precedingDyadicLabels` 推存在 G。`91–92` 使用真实 predecessor cost theorem；其 `E/GenericWindowLogBudget.lean:124–137` 只靠 global K-separation、signed-prime Chebyshev cost与 hcost，完全不需要每个窗口的 density/cardinality。

同文件 `153–183` 的整个 prime pool log-cost 也是真实有限 prime union 的 Chebyshev cap；`187–219` 将其转成 smoothing error 与总 error≤1。不存在把“总 alphabet 很小”作为额外未证结论传入。

### 10.4 最后上界确是同一 finite sum

`E/GenericFiniteSieveEngine.lean:35–58` 的 `actual_selected_window_charge_sum_le` 对实际选中 bins 的 rate 求和，结论≤`log(#wordStepBall)+1`。证明 `59–80` 对同一个 Q 做 greedy finite selection，`93–118` 建立所需 nested-family、length divisibility、smoothing error，然后调用原 `schedule_lattice_information_telescope`。`119–127` 用 binEnum finite sum 等式与 total error≤1 得到原集合上的上界。

`E/GenericTimeKernels.lean:420–444` 的 telescope 也明确使用同一个 `P=(at0).advance(commonSchedule z ns N)`。`len=batchWordLength j=2^(2*j/5)>0`，分母不是可归零的人为替代；其正性与 divisibility 分别见 `E/GenericNumericalSchedule.lean:121–129`。

`WeakCoreFiniteSieveSupport:96–98` 最后把该上界与选择的同一个 `allBins W J` strict excess 比较，直接得 False。没有再次选择 rate/mass witness，也没有在求和途中切换 law。

## 11. 真正 finite Q² sieve 与闭合 endpoint

`E/WeakCoreFiniteSieveSupport.lean:103–131` 对给定 D≥0，先在 max(D,1) 上得到 no-walk prime pool，再用 edge monotonicity回到 D。`119` 调的是原 `avoiding_component_bound_of_no_infinite_walk`。

该原 lemma 的真实证明（`E/PeriodicComponents.lean:310–321`）先从 no infinite injective walk 推 actual components finite，再以 product-period translations 和 coefficient residues 得 Q² cardinality bound。`251–293` 的 residue space 是 `Fin 2 → ZMod Q`，card 正是 Q²；`297–304` 的 periodicity 直接来自原 additive maps。没有把组件有限性偷放为 premise。

`E/Graphs.lean:18–23` 定义的 `UniformComponentBound` 同时要求每个实际 Reachable component 有限并且 ncard≤B。因此不会利用 `Set.ncard` 对 infinite sets 的默认值来伪造有限组件结论。

`E/WeakSieveTargets.lean:11–17` 的 target 原封使用实际 avoiding、latticeGraph 与 Q²。`E/WeakFiniteSieveConsequences.lean:10–15` 已把 proved Dirichlet-goodbin implication传入条件 weak target，给闭合 weak finite sieve 与 no-walk 两 theorem。不能因 `WeakCoreWeakTargets` 本身仍接显式 hbridge 参数，就漏看这里已消去该参数。

接口再往原 Main 的连接在 `E/WeakAssembly.lean:14–23,36–63`：实际 weak principal residue witnesses构造四字段 core，调用 weak sieve，识别 avoidance 为不被所选 nonunit generators 整除，再使用原 restoration。这里未对完整 arithmetic supply 和 restoration 另作本任务范围外的全证明审查；但 weak sieve 端没有更换原 Main 所需的几何/graph 结论。

## 12. 非阻断文档项与审计边界

### D1：历史 open 注释应更新，但并非数学缺口

- `E/WeakSupplyInterfaces.lean:5–6,57–59` 仍称 analytic bridge/generalized sieve open。
- `E/WeakSieveTargets.lean:9–10,19–20` 仍称两个 target currently open。
- `E/WeakCoreGoodBinFiniteSieve.lean:7–8,118–120` 与 `WeakCoreWeakTargets:4–7` 说明“本模块”保留 bridge premise；这对模块局部是准确的，但应指向 `WeakFiniteSieveConsequences`，避免读者误认全工程仍未闭合。
- `E/WeakAssembly.lean:6–7,12–13` 继续用“open foundations”描述条件组装。条件 theorem 本身无误，整体项目状态应以最终闭合入口为准。

以上只建议未来文档同步；本任务没有改任何源码。

### 未作/不应从本报告推断的事情

1. 没有 fresh Lean compilation、kernel replay 或证明对象递归扫描。本报告的 PASS 是**数学语义及源码接口 PASS**，应与父审计的 fresh build/递归禁项结果合并。
2. 没有宣称旧 A5 自然密度或旧 `PrincipalSplitPrimeSupplyTarget` 已由弱路线证明。弱 supply足以通过更强的 sieve theorem 得原 Main，不会反推出旧强供给。
3. 没有把正 Dirichlet supply 的实际 arithmetic 提供者在本任务中重新证明。此处只核 supplied premise 的含义，以及它到真正 finite sieve 的闭合链。
4. 文本比较的十个重放模块证明了新 source 没有额外数学编辑，不能替代 Lean 的名称解析；父审计仍应确认实际递归依赖没有落回要求 A5 的旧包装或禁止的外部桥。

**综合建议：弱供给→原整数窗口→core-only common-law charge→原 Q² finite sieve 这一子链可接受；无待修数学缺口。**
