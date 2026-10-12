# 张量残差维数增长：定向文献初筛

检查日期：2026-10-07。目标是核实是否有已知近交换、近同时对角化、近结合代数或 odeco backward-error 结果直接蕴含

\[
\operatorname{dist}_F(T,\mathcal D_{m,p})\le C_p m^{1/4}\sqrt{R_p(T)},
\qquad R_p(T)^2=\sum_{\alpha,\beta}\|[X_\alpha,X_\beta]\|_F^2,
\]

其中 (X_\alpha=T_{\alpha_1,\ldots,\alpha_{p-2},\cdot,\cdot}) 遍历全部 (N=m^{p-2}) 个有序收缩指标，(T) 是完全对称实 p 阶张量，(\mathcal D_{m,p}) 是实正交可分解张量类。此次只做低成本、定向的主文对照；“没有检索到”不解释为原创证据。

## 归一化对照：目标是比一般近交换定理更强的率与结构结论

用 normalized Hilbert–Schmidt 矩阵范数 (\|A\|_{2,\mathrm{tr}}=\|A\|_F/\sqrt m)，定义收缩族的 RMS 交换子

\[
\eta_{\mathrm{RMS}}=\left(\frac1{N^2}\sum_{\alpha,\beta}
\|[X_\alpha,X_\beta]\|_{2,\mathrm{tr}}^2\right)^{1/2}
=\frac{R_p(T)}{N\sqrt m}
=\frac{R_p(T)}{m^{p-3/2}}.
\]

另外因每个有序 tensor entry 恰好出现在一个矩阵 (X_\alpha) 中，

\[
\frac{\operatorname{dist}_F(T,\mathcal D_{m,p})}{\sqrt{Nm}}
=\frac{\operatorname{dist}_F(T,\mathcal D_{m,p})}{m^{(p-1)/2}}
\]

是对应的 normalized tensor/family 误差标度。因此目标 inequality **等价**于该 tensor-structure error 的无维数 RMS 形式

\[
\operatorname{dist}_F(T,\mathcal D_{m,p})/m^{(p-1)/2}
\le C_p\sqrt{\eta_{\mathrm{RMS}}}.
\]

不能把 (R_p) 当成单个矩阵对的 commutator norm，也不能把单矩阵的 normalized HS 换成未归一 Frobenius 而省掉 \(\sqrt m\)。若改用单对最大值 (\eta_{\max}=\max_{\alpha,\beta}\|[X_\alpha,X_\beta]\|_{2,\mathrm{tr}})，只有粗界
\(\eta_{\max}\le R_p/\sqrt m=N\eta_{\mathrm{RMS}}\)。

## 已读主文：Hilbert–Schmidt 近交换 / 同时对角化

### Glebsky 与 Filonov–Kachkovskiy

1. **Lev Glebsky (2010), “Almost commuting matrices with respect to normalized Hilbert-Schmidt norm,” arXiv:1002.3082v1.** 已读主文 PDF。§1 定义的 (\|A\|_{\mathrm{tr}}=(m^{-1}\sum_{ij}|a_{ij}|^2)^{1/2}) 即上文 normalized HS。Theorem 4（文末 §6–7）对任意固定族长度 (k) 的有界 Hermitian 矩阵，若所有两两 normalized-HS commutator 趋于 0，则存在两两交换 Hermitian 近似；误差模数 (\delta(\epsilon,k)\) 对矩阵阶数 uniform，但主定理定性，不给平方根率。Glebsky 还在 Theorem 3 给单个 almost-normal matrix 的近 normal matrix 结果。它确立维数 uniform stability，却没有所需的 (\sqrt{\eta_{\mathrm{RMS}}}) 定量指数，也不保证近似矩阵保留由一个完全对称张量产生的 compatibility。

2. **Nikolay Filonov–Ilya Kachkovskiy (2010), “A Hilbert-Schmidt analog of Huaxin Lin’s Theorem,” arXiv:1008.4002v2.** 已读主文 PDF。Theorem 2（印刷第 3 页）给一对 norm-1 Hermitian 矩阵：若 (\delta=\|[H_1,H_2]\|_{\mathrm{tr}}\le1/16)，则存在 commuting Hermitian contractions (A_1,A_2)，
\[
\|H_j-A_j\|_{\mathrm{tr}}\le2\delta^{1/4}.
\]
Theorem 3（印刷第 4 页）处理长度 (k\ge3) 的 Hermitian tuple，假设每对 commutator 均在 normalized HS 下至多 (\delta)，则给出每个坐标的误差上界形如 (5\delta^{1/4^{k-1}})，小量阈值也依赖 k（定理原式还保留精确阈值）。所以对一对矩阵它给维数无关的 **1/4 次**误差率；对增长的族长度，显式率恶化为 (1/4^{k-1})。它并未给 (1/2) 次率。其先前引用的 Glebsky Theorem 4 本身仅给定性 (\delta(\epsilon,k))。

把这个 tuple 定理应用于 (X_\alpha) 有三项障碍： (i) 族长度是 (k=N=m^{p-2})，显式指数随维数退化；(ii) commutator 的定理前提是最大 pair error，而 (R_p) 给 RMS，转换需要 (\eta_{\max}\le N\eta_{\mathrm{RMS}})；(iii) 定理假设每个矩阵 operator norm ≤1。若 (\|T\|_F=1)，则每个收缩满足 (\|X_\alpha\|_{op}\le\|X_\alpha\|_F\le1)，所以不存在此前写出的 (m^{(p-1)/2}) 放大。因子 (m^{(p-1)/2}) 对应的是把张量族的 RMS 能量归一为 1，也就是 (\|T\|_F=\sqrt{Nm}=m^{(p-1)/2}) 时的原始张量尺度；采用该尺度时各收缩矩阵也需相应缩放后才能使用定理。即使得到普通 commuting 近似族，原三阶 slice 家族的完全对称 compatibility 也未自动保留，且需另外证明投影回对称张量后仍有目标 odeco 距离界。

### 同时近对角化指标的其它版本

3. **Klaus Glashoff–Michael M. Bronstein (2013; arXiv 修订版 2018), “Almost-commuting matrices are almost jointly diagonalizable,” arXiv:1305.2135v2.** 已读 PDF 的 Theorem 2.1、3.1、4.1。其 (J(A,B)) 是在 unitary basis 下两矩阵非对角部分平方 Frobenius 和的最小值。定理 2.1 对 (\|A\|_F=\|B\|_F=1) 给 (\epsilon_1(\|[A,B]\|_F)\le J(A,B)\le n\epsilon_2(\|[A,B]\|_F)) 的定性函数界；下界 Theorem 3.1 是 (\frac14\|[A,B]\|_F^2\le J(A,B))，上界 Theorem 4.1 在 operator norms ≤1 时仍有显式维数因子 n 乘一个趋零模数。印刷页 3–7。该指标针对一个共同 unitary 对角化 basis，相关但没有提供此处 tensor-structure distance 的 (1/2) 率或与 (R_p) 对应的全族 RMS 结果。

4. **David Herrera (2020/2022), “On Hastings’ approach to Lin’s Theorem for Almost Commuting Matrices,” arXiv:2011.11800v2.** 已读主文。Theorem 2.1 是 operator norm 近交换的定量 Lin 型结果，误差率 (E(1/\delta)\delta^{1/6})，而文中引言指出 Hastings 的特殊结构情形曾有 (1/2) 率；这些是 operator norm（不是 normalized HS），其假设也不是收缩矩阵 RMS Frobenius residual。此条只用于防止把同名近交换结果跨范数搬用，不是目标界的直接前件。

## 精确结合 / 近结合交换代数

**Boralevi–Draisma–Horobeț–Robeva (2017), “Orthogonal and unitary tensor decomposition from an algebraic perspective,” Israel Journal of Mathematics 222(1), 223–260, arXiv:1512.08031, DOI [10.1007/s11856-017-1588-6](https://doi.org/10.1007/s11856-017-1588-6).** 主文已读（§3.1、Lemma 11、Proposition 12；高阶 §4.2）。它给出实 symmetric cubic 的精确代数结构：由张量定义的交换、内积相容乘法，其乘法算子两两交换/结合与正交分解零集相联系；更广泛地刻画 odeco variety。此为“commutative metrized exact associative algebra ↔ odeco”结构层面的明确先例。它未给非零 associator/commutator 下的定量近似分类。定向检索 “approximately associative algebra,” “Hyers–Ulam stability of commutative associative algebras,” “metrized algebra associator stability” 未找到一个主文定理给出适用于实有限维 commutative metrized algebra、对维数依赖明确且依赖范数与当前 (R_p) 匹配的 stability estimate；该阴性结果仅是检索记录。

特别地，一般矩阵 tuple 的近交换结论不自动是这个 algebra 的 Hyers–Ulam 结论：由立方张量定义的 (x\mapsto L_x) 还满足 (L_xy=L_yx)（完整三阶对称性）。逐矩阵替换为共同对角矩阵一般不保留该线性/对称约束；必须找到“保持乘法 compatibility 的”联合投影或一项单独稳定定理，才能推出附近正交分解。对于 (p>3)，还需要处理全部高阶张量对称性，而不是只处理三阶 Frobenius algebra。

## ODeCo backward error / 恢复型扰动定理

本轮逐条复核了已有初筛中的 Auddy–Yuan arXiv:2007.09024 与 Mu–Hsu–Goldfarb arXiv:1705.10404：前者将两个 odeco 张量间 spectral-norm 差转成分量恢复误差，后者从已知正权重 SOD tensor 加小 spectral-norm noise 控制 successive rank-one recovery。两者都研究“给定 odeco 基准/分解受到 tensor perturbation 后如何恢复 factor”，不是把一个可检验的全部 contraction commutator residual (R_p(T)) 映为到 odeco variety 的 Frobenius distance；没有直接给目标 (m^{1/4}\sqrt{R_p}) 维数阶。它们仍是最接近的 tensor backward/forward perturbation 先例，应在后续版本引用，但这个问题方向差异不证明此前没有相同 residual error bound。

## 对当前维数问题的结果

读过的近交换文献已提供了固定长度 self-adjoint matrix family 的 dimension-uniform qualitative normalized-HS stability，并且 pair case 有 explicit (O(\delta^{1/4})) 上界；tuple rate 对族长 k 依赖强（Filonov–Kachkovskiy Theorem 3 为 (\delta^{1/4^{k-1}})）。这些结果没有给 (O(\sqrt{\eta_{RMS}})) 的 family RMS error，也没有自动保留 tensor slice compatibility。因此目前没有从已读定理直接推出 (C_p m^{1/4}\sqrt{R_p})；也没有找到反例否定它。由于 (N=m^{p-2})、输入 contraction operator norms、以及 symmetry constraints 都要同时处理，这里不能只把 tuple 定理中的“constant independent of matrix size”改写成目标 dimension law。

## NP 难度与 Banach 定理

1. **Banach (1938), “Über homogene Polynome in (L2),” Studia Mathematica 7, 36–44.** Friedland–Wang 下文明确将对称张量 spectral norm 的对角最大值刻画归于 Banach（他们 arXiv:1808.03864v3 §1、Lemma 1 / Theorem 7）。这是精确数学恒等式：完全对称多线性型在实/复 Hilbert 单位球乘积上的谱范数可由 (\max_{\|x\|=1}|T(x,\ldots,x)|) 达到。因此全阶证明所选最大方向本身可看作对称张量谱范数最大化。

2. **Shmuel Friedland–Li Wang (2020), “Spectral norm of a symmetric tensor and its computation,” Mathematics of Computation 89(325), 2175–2215, arXiv:1808.03864v3, DOI [10.1090/mcom/3525](https://doi.org/10.1090/mcom/3525).** Crossref 核对卷、期、页和 DOI；已读 arXiv 主文，尤其 Theorem 15 与二元 (n=2) 的 §§6、Theorems 18–19。Theorem 15 取零对角 (0/1) 对称图邻接矩阵 A，构造实对称 quartic (f_A(x)=\sum_{ij}A_{ij}x_i^2x_j^2)，其对角 spectral norm 正好是 (1-1/\kappa(A))，(\kappa(A)) 为最大 clique 大小；把该 norm 以相对精度 (\varepsilon<1/(2n^2(n+1))) 计算是 NP-hard。故即使固定 tensor order (p=4)，一般完全对称实 tensor 的最大对角方向/谱范数问题在维数 variable 时也有精度受控的 NP-hardness。不要把这个结论表述成任何常数精度的近似皆已证明 NP-hard；该定理给的是随 n 缩小的 inverse-polynomial 误差阈值。它支持不应默认全局最大化有高效算法，但与一个仅证明存在性的 rigidity inequality 逻辑独立。

3. 同一 Friedland–Wang 文的 Theorems 18–19 处理 binary symmetric forms：固定 (n=2) 时通过一个至多 ((p-1)^2+1) 次的一元多项式的根计算谱范数，文中将 p 的给定精度复杂度称为多项式。该结论只算 (\max |f(u)|)，不直接给到二元 quartic odeco 集的最近点。

## Binary quartic 的 exact distance：已知的初等变分式与未确认的闭式

对 (p=4,m=2)，任何正交分解只能用一对正交单位向量 (u_\theta=(\cos\theta,\sin\theta))、(v_\theta=(-\sin\theta,\cos\theta))。因为 (u_\theta^{\otimes4},v_\theta^{\otimes4}) 是 tensor Frobenius 空间的正交单位向量，对固定基最优权重就是 (T(u_\theta^4),T(v_\theta^4))。所以直接投影有完全精确的公式

\[
\operatorname{dist}_F(T,\mathcal D_{2,4})^2
=\|T\|_F^2-\max_{\theta\in[0,\pi/2]}
\{T(u_\theta,u_\theta,u_\theta,u_\theta)^2+
T(v_\theta,v_\theta,v_\theta,v_\theta)^2\}.
\]

它将距离化成一个一元三角多项式极值；与三阶 binary cubic 文稿的 A/B harmonic closed form 不同，此处搜索没有发现类似的显式闭式/完整相位分类 theorem。Friedland–Wang Theorem 18 给 binary quartic **单次谱范数**的根求解，不是上式“两正交方向的平方值之和”的最大化，不能直接称为相同的 binary-odeco distance formula。上式是由正交投影立即推出的精确降维表达，本报告不主张这是文献中的首个公式或它不能再化简。

## 证据界线

- 已读全文：Glebsky arXiv:1002.3082v1；Filonov–Kachkovskiy arXiv:1008.4002v2；Glashoff–Bronstein arXiv:1305.2135v2；Herrera arXiv:2011.11800v2；Friedland–Wang arXiv:1808.03864v3；BDHR arXiv:1512.08031；以及先前报告已读的 Auddy–Yuan / Mu–Hsu–Goldfarb 主文。
- 定理页码均以各 arXiv PDF 印刷页/节号记。期刊元数据仅对 Crossref 直接返回且与 DOI 核对的 Friedland–Wang、BDHR 等书目给出；其它保留 arXiv 标识，不补猜卷页。
- 近结合代数搜索范围是标题/摘要/公开全文关键词和上述 odeco 代数主文；没有证明近结合的 Hyers–Ulam 定理不存在。Binary quartic 距离只做定向关键词检索和初等几何化简，没有穷尽计算代数几何/优化文献。所有阴性结果都不构成原创性或 priority 结论。
