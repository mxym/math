# Sparse near-linear cover law：有限文献比较

检查日期：2026-10-07。比较对象为 notes/sparse-near-linear-cover-law/paper.md 中的 Theorem 1–4；不审核证明，也不作原创性优先权结论。

## 所比较的结论

主稿考虑有限 simple 相交 (r)-均匀超图，不要求 partite。令 (m=|E(H)|)、(t=\tau(H))，并定义
\[
I(H)=\sum_{\{A,B\}\subset E(H)}(|A\cap B|-1)
     =\sum_v\binom{d(v)}2-\binom m2.
\]
主稿 Theorem 1 给出：对每个固定 (C\ge1)、\(\varepsilon>0\)，存在常数 (B_{C,\varepsilon}\)，使 (m\le Cr) 时
\[
\tau(H)\le r h(m/r)+G_C\,I(H)/r+\varepsilon r+B_{C,\varepsilon},
\]
其中 (h(x)=\min_{k\ge1}\{(k-1)/(k+1)+x/[k(k+1)]\})。因此，对 (m/r\to c<\infty) 且 (I=o(r^2)) 的序列，有 \(\limsup\tau/r\le h(c)\le c/(1+c)\)；若 \(\tau/r\to1\)，则 (m/r\to\infty)。Theorem 3 还指出，整数端点 c=a 且 tau/r→a/(a+1) 时 n/r²→a/(a+1)，并有 Σ_v(d(v)−a−1)²=o(r²)；Theorem 4 说明非整数 (c>1) 处不能达到 (h(c))，但不声称非整数端点 sharp。主稿 Section 6.1 进一步给出显式保守 gap：令 \(P=k(k+1)\)、\(\theta=c-k+1\)、\(\Delta=(k-1)(k-c)/P\)、\(A=2(k+2)P^2\)、\(J=1+[k+A(k+2)]/(2\theta)\)，则可取 \(\zeta_c=(\Delta/J)^2>0\)。该数值并未声称最优，最佳 gap 仍是开放问题。

## 相关已知结果及适用范围

1. **Zoltán Füredi, “Maximum degree and fractional matchings in uniform hypergraphs,” *Combinatorica* 1(2) (1981), 155–162, DOI 10.1007/BF02579271.** 查阅了 Springer 摘要（未读到全文）。摘要明示：若 (H) 是相交 (r)-均匀超图，则要么 (H) 是阶 (r-1) 的 projective plane，且 \(\Delta(H)=m/(r-1+1/r)\)，要么 \(\Delta(H)\ge m/(r-1)\)。这是 (m) 与原超图最大顶点度 \(\Delta\) 的关系；当 (m=Cr) 时只给常数级 \(\Delta\) 下界，未直接给出关于 (m/r) 的 cover 上界或超线性边数下界。此处 Δ 是 vertex degree，不是 edge size/rank (r)。

2. **Z. Füredi, J. Kahn, P. D. Seymour, “On the fractional matching polytope of a hypergraph,” *Combinatorica* 13(2) (1993), 167–180, DOI 10.1007/BF01303202.** 核对了 Springer 的摘要及题目所指主要内容；该文处理 fractional matching 与 integral matching 的转换，摘要所述适用情形包括 uniform 或 intersecting hypergraphs。这里没有检出依赖 (m/r) 的 cover 定理。fractional matching/covering 的 LP 对偶提供的是值的相等关系，本身没有边数 (m) 参数，故不能直接推出主稿的分段函数或超线性结论。

3. **Michael A. Henning and Anders Yeo, “Transversals in Uniform Linear Hypergraphs,” arXiv:1802.01825v1 (2018), Theorems 2–7.** 已读主文。Theorem 2 对连通的 (k=2,3) 线性系统给出 \(\tau(H)\le(n+m)/(k+1)\)；Theorem 3 对连通、任意 (k) 且最大度至多 2 的线性系统证明同式；Theorem 7 证明 (k=4) 的线性情形。文中也指出类似的 \((n+m)/(k+1)\) 猜想在大 (k) 失败，并构造出反例（Theorems 4–5）。这些结果依赖 vertex count (n) 或限制 rank/degree，不能直接化成仅依赖 (m/r) 的 (h) 上界；原始 rank 随 (r\to\infty) 增长时尤其不能把固定小秩结论外推。

4. **Kahn 的两类结果需分开。** Kahn, “Asymptotically good list-colorings,” *Journal of Combinatorial Theory, Series A* 73 (1996), 1–59 的 small-codegree edge-colouring theorem 是主稿所用的 published input，形式上要求固定辅助 rank 和小相对 pair-codegree。它不能直接套到原超图：原 rank 为变动的 (r)，而相交结构有高码度。主稿用它处理固定 (D) 的辅助 (D)-block 系统，这是适用范围不同的用法。

   本轮已读取 **Jeff Kahn, “On a Problem of Erdos and Lovasz. II: n(r)=O(r),” *Journal of the American Mathematical Society* 7(1) (1994), 125–143, AMS DOI [10.1090/S0894-0347-1994-1224593-5](https://doi.org/10.1090/S0894-0347-1994-1224593-5), JSTOR DOI [10.2307/2152722](https://doi.org/10.2307/2152722)** 原文（AMS 公共 PDF: https://www.ams.org/journals/jams/1994-07-01/S0894-0347-1994-1224593-5/S0894-0347-1994-1224593-5.pdf；印刷页 125–143）。其 Theorem 1 的构造在 pp.126–127, (5)–(8)，给出每个充分大 r 的一般相交 r-均匀超图，(τ=r)、(m≤Cr)；构造以 dual 形式给出，不声称 partite。

   对本题直接相关的是该文 §5, Corollary 5.4, p.140：若 H 是 r-均匀相交超图，(|E(H)|≤cr)（固定 c），且
   \(\max_{A\ne B\in E(H)}|A\cap B|=o(r)\)。则 \(\tau(H)\le(c/(c+1)+o(1))r\)。因此任何 \(\tau=r\)、\(m=O(r)\) 的族都不可能线性，也不可能有最大两两交集 \(o(r)\)；Kahn 在 p.139, §5.B 还明确指出其 (n(r)) 例子不属于“所有 edge intersections 都 small”的类。Corollary 5.4 也直接给出线性 \(\tau=r\) 边数函数 \(n_{\rm linear}(r)/r\to\infty\)；没有给出其显式增长率。

   更一般地，Kahn 的 Corollary 5.4 连同简单删边可推出主稿 Corollary 2 中**较弱的调和界**，但不是分段包络 h。令 ε_r=I(H)/r²→0，取 δ_r=√ε_r+r^(-1/2)。则 δ_r→0 且 δ_r r→∞。满足 |A∩B|≥δ_r r 的坏边对，每对对 I 的贡献至少 δ_r r−1，因此坏对数至多 I(H)/(δ_r r−1)=o(r)。若 ε_r=0，则 I=0 且坏对数为 0；同一 δ_r=r^(-1/2) 选择仍满足条件。每个坏对删去一条边，总计删去 o(r) 条；剩余简单相交 r-均匀超图的最大交集小于 δ_r r=o(r)，其 cover number 至多比原超图少 o(r)。若 m/r→c，则剩余边数比仍趋 c，应用 Corollary 5.4 得 limsup τ/r≤c/(c+1)；若 τ/r→1，任意有界 m/r 子列都矛盾，故 m/r→∞。因此 Kahn 的 O(r) 构造也不能满足 I=o(r²)。该删边推论不提供主稿更强的 h(c)（非整数区间严格低于调和曲线）、有限惩罚型 Theorem 1 或度数刚性结论。Kahn 在 projective plane 中随机取约 22r log r 条线的另一结果（Kahn 1992, “On a problem of Erdos and Lovasz: random lines in a projective plane,” *Combinatorica* 12(4), 417–423, DOI 10.1007/BF01305234；也由 ABW 2016 Theorem 1.2 引述）给出线性 O(r log r) 例，是不同构造。
5. **全类 partite 稀疏边数问题及后续构造。** Toufik Mansour, Chunwei Song and Raphael Yuster, “A comment on Ryser’s conjecture for intersecting hypergraphs,” arXiv:0709.3138v1 (2007)，提出 \(f(r)=\Theta(r)\) 猜想并给出约 \(2.764r\) 的线性 lower bound。Aharoni–Barát–Wanless, “Multipartite hypergraphs achieving equality in Ryser’s conjecture,” *Graphs and Combinatorics* 32 (2016), 1–15, DOI 10.1007/s00373-015-1575-9, arXiv:1409.4833v2，Theorem 2.5 / Corollary 2.6 将普适 partite lower bound 提高至 \(293r/96+O(1)\)，Conjecture 2.11 仍为 \(f(r)=O(r)\)，且 Open Problems 1–3 询问定义域及线性是否有助于降低 (f(r))。这些来源未解决一般 (f(r)=O(r)) 问题。

   Haxell–Scott, “A note on intersecting hypergraphs with large cover number,” arXiv:1609.05458v2 (2017), Theorem 6, 对充分大 (r) 构造偶数阶 \(\tau\ge r-3\)、奇数阶 \(\tau\ge r-4\) 的 partite 系统；这不是 \(\tau\ge r-1\) 的 (f(r)) 问题，Theorem 6 也不主张边数线性。Abu-Khazneh–Barát–Pokrovskiy–Szabó, “A family of extremal hypergraphs for Ryser’s conjecture,” arXiv:1605.06361v2 (2018), 提供 extremal cover/matching 构造族，但不是 edge-minimal (f(r)) 定理。检查这些后续未见它们证明全体 (r) 的 (f(r)=O(r))。

6. **边对重复交点的已知计数 slack。** ABW 2016 Lemma 2.2（已读主文）在残余最大度 \(\Delta\le4\) 时使用
\[
 x_2+3x_3+6x_4=\sum_v\binom{d(v)}2\ge\binom m2.
\]
不等式左侧相对右侧的 slack 正好是 (I(H))。保留此项可将该引理 proof 中的式 (3) 改写为
\[
 x_3+3x_4\ge\binom m2+r\tau-rm+I(H),
\]
再加上各 part 顶点数超过 \(\tau\) 的非负 slack。ABW 原文写出不含 (I) 的较弱式，并说明取等当且仅当 (H) linear 且每 part 恰有 \(\tau\) 个点。这是有界最大度计数中的明确近邻，不是全 rank 的 (h(m/r)) cover law，也未推出 (I=o(r^2)\Rightarrow m/r\to\infty)。

7. **设计对偶与整数端点例。** resolvable (2-(v,k,1)) BIBD 的原 block 系统中，同一 parallel class 的 blocks 两两不交，故原设计不是 intersecting hypergraph。但取 incidence dual 后，points 成为 hyperedges、blocks 成为 vertices；任意两个 points 同属唯一 block，故 dual 是 simple linear intersecting hypergraph。每个 parallel class 成为 dual 的一个 part，每个 point 对应一条边在每部恰取一个 vertex。特别地，仿射空间 (AG(N,s)) 的线设计是 resolvable (2-(s^N,s,1)) 系统；其 dual 参数正是主稿第7节的
\[
 m=s^N,\quad r=(s^N-1)/(s-1),\quad \tau=s^{N-1}.
\]
 cover number 由每条线含 (s) 个点给出下界 (s^{N-1})，一个 parallel class 达到。故整数斜率端点的仿射几何 dual 例是标准设计结构的直接实例；不能把“设计本身有 parallel disjoint blocks”误判为其 dual 不相交。此次未找到某个 general resolvable-BIBD cover theorem 直接蕴含主稿的普适 (h) 不等式。

## 有限检索结论

对 `linear intersecting hypergraph cover number m/r`, `fractional matching intersecting linear hypergraph`, `transversal bound number of edges rank`, `resolvable BIBD covering number` 等进行了 arXiv、Crossref/OpenAlex 定向检索，并读了上列几篇关键主文或标明只查摘要/引述。未找到直接给出主稿有限 (h(m/r)) 包络、全局有限惩罚型不等式、非整数端点严格缺口或整数度方差刚性的已知结果。需要修正一项重要先例归属：Kahn 1994 Corollary 5.4 已给出 max-pair-intersection=o(r) 条件下的调和 cover bound；加上删去 o(r) 条 bad edge pairs 的论证后，它蕴含主稿 Corollary 2 的弱调和界以及线性 / I=o(r²) 子类的超线性边数结论。因此这些较弱渐近推论不能写成未有先例。Kahn 并未给出较强分段函数 h、有限 I/r 惩罚、非整数 gap 或整数端点 degree variance rigidity。以上仍为 limited screen，不构成不存在先例或优先权判断。
