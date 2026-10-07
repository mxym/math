# 线性/近线性 partite equality 例的超线性下界：定向先例比较

检查日期：2026-10-07。本短记核查以下候选是否已有文献先例：在线性 partite 子类中，若定义 \(f_{linear}(r)=\min |E(H)|\)，其中 H 为相交 r-partite r-均匀线性超图且 \(\tau(H)\ge r-1\)，是否已知 \(f_{linear}(r)/r\to\infty\)；更一般地，对 \(r_j\to\infty\)、\(\tau(H_j)\ge r_j-1\)、全局交叠超额 \(I(H_j)=o(r_j^2)\) 的相交 partite 序列，是否已有 \(|E(H_j)|/r_j\to\infty\) 定理。这里只做文献比较，不审查候选推导。

## 直接相关主文

1. **Ron Aharoni, János Barát, Ian M. Wanless, “Multipartite hypergraphs achieving equality in Ryser’s conjecture,” *Graphs and Combinatorics* 32 (2016), 1–15, DOI 10.1007/s00373-015-1575-9, arXiv:1409.4833v2.** 已读主文引言及 §2 的开放问题。

   - 作者定义 \(f(r)\) 为所有相交 r-partite 超图中满足 \(\tau\ge r-1\) 的最少边数。其 Conjecture 2.11 是全类的线性上界 \(f(r)=O(r)\)，并明确说该函数是否处处定义（每个 r 是否存在相应例子）也未解决。
   - Theorem 1.3 证明：当 \(r-1\) 阶有限射影平面存在时，从截短射影平面中随机取 \(22r\log r\) 条线，\(r\to\infty\) 时以概率趋于 1 仍有 \(\tau\ge r-1\)。该构造是线性系统，给出相应子序列的 \(f_{linear}(r)\le22r\log r\) 上界；它不是超线性下界。
   - §2 明确把“若另外要求 H 线性、但不要求来自射影平面”列作变体，并说不清线性是否有助于达到 \(f(r)\)；Open Problem 3 问最优例通常为线性、非线性或两者。Open Problem 2 另问截短射影平面的线子集可以稀疏到何种程度而仍保持 \(\tau=r-1\)。因此 ABW 知道线性子问题存在，但没有断言或证明 \(f_{linear}(r)/r\to\infty\)；其表述将线性是否改善 edge minimum 留作开放问题。

2. **Francetić–Herke–McKay–Wanless, “On Ryser’s Conjecture for Linear Intersecting Multipartite Hypergraphs,” *European Journal of Combinatorics* 61 (2017), 91–105, DOI 10.1016/j.ejc.2016.10.004, arXiv:1508.00951v3.** 已读主文引言及第 2、4 节相关陈述。文章证明线性相交 partite 系统在 \(r\le9\) 时满足 Ryser 界；对 \(r\le7\) 的 \(\tau=r-1\) 线性例作了分类，并报告 r=8 有非截短射影平面的例子。结果是小阶结构结论，没有推出线性 equality 例的渐近边数下界或 \(\omega(r)\) 结论。

3. **Varun Sivashankar, “An Improved Lower Bound for the Erdős–Lovász Cover Number Problem,” arXiv:2606.24878v2 (2026), Theorem 1.** 已读主文。其 \(g(r)\) 的定义要求一般（不要求 partite 或线性）相交 r-均匀超图满足 \(\tau=r\)，证明渐近斜率约 3.053。它不处理 partite \(\tau=r-1\) 的线性 equality 类，也没有按原超图全局 \(I(H)\) 控制的近线性定理。

## 初筛结论（Kahn 更正见下）

在上述 ABW 与 FHMW 主文、Sivashankar 的一般 lower bound 及以 `linear intersecting partite`, `f_linear`, `linear Ryser`, `near-linear intersecting`, `intersection excess`, `superlinear edge lower bound` 为词的 arXiv/Crossref/OpenAlex 定向搜索中，**Kahn 1994 Corollary 5.4（见下节）已推出**线性且 \(\tau/r\to1\) 时 \(m/r\to\infty\)，并经删边推出 \(I(H)=o(r^2)\) 的近线性版本；它不给显式增长率。已知的全类 ABW lower bound \(f(r)\ge293r/96+O(1)\) 自动适用于线性子类，但只是线性阶；ABW 的射影平面随机子集给出某些 r 上 \(O(r\log r)\) 的线性上界。

Kahn 的结论关闭了“是否超线性”这一弱渐近问题，但没有回答显式速率，也没有给出一般非线性 partite 类的强下界。ABW 对线性限制是否改善具体 edge minimum 的开放问题仍不等同于这个渐近推论。以上是定向检索，不构成优先权结论。


## Kahn 1994：直接结论与 §5 更宽猜想

Jeff Kahn, “On a Problem of Erdos and Lovasz. II: n(r)=O(r),” *Journal of the American Mathematical Society* 7(1) (1994), 125–143, AMS DOI [10.1090/S0894-0347-1994-1224593-5](https://doi.org/10.1090/S0894-0347-1994-1224593-5), JSTOR DOI [10.2307/2152722](https://doi.org/10.2307/2152722)，原文 §5 Corollary 5.4, 印刷 p.140 的假设及结论是：对固定常数 c>0，H 是一列简单的相交 r-uniform 超图，边数 m=|E(H)|≤cr，并且最大两两边交集满足 max{|A∩B|: A,B∈E(H), A≠B}=o(r)，则 τ(H)≤(c/(c+1)+o(1))r。r 同时是每条边的大小和 uniformity/rank，随序列趋于无穷；c 固定，结论为渐近式。线性系统满足最大交集 1=o(r)，所以 Kahn 直接推出线性相交 r-uniform 且 τ/r→1 时 m/r→∞，特别是 unrestricted 线性 τ=r 边数函数 n_linear(r)/r→∞；没有给出显式增长率。其 p.139, §5.B 还明确说本文 n(r)=O(r) 例子不能来自所有边交集都 o(r) 的族，因此该构造不是线性的。

AMS PDF 公开来源：https://www.ams.org/journals/jams/1994-07-01/S0894-0347-1994-1224593-5/S0894-0347-1994-1224593-5.pdf 。AMS 站点拒绝直接下载，但已通过文本提取完整读取 AMS 原文；本地全文文本为 `/tmp/kahn-jina-pdf`（逐页提取文本，不是 PDF）。Theorem 1 的 O(r) 构造见印刷 pp.126–127, equations (5)–(8)。Corollary 5.4 的证明在 p.140 引用作者当时尚在准备中的 [18] “On a theorem of Frankl and Rodl”，并说其结果延伸 Rödl、Frankl–Rödl、Pippenger、Pippenger–Spencer 的近完美覆盖工作。

同一推论还蕴含主稿在 I(H)=o(r²) 下的弱调和界，方法是删边而非 Kahn 原文直接陈述。令 ε_r=I(H)/r²→0，取 δ_r=√ε_r+r^(-1/2)，则 δ_r→0 且 δ_r r→∞。满足 |A∩B|≥δ_r r 的坏边对，每对对 I 的贡献至少 δ_r r−1，因此坏对数至多 I(H)/(δ_r r−1)=o(r)。若 ε_r=0，则 I=0、坏对数为 0，取 δ_r=r^(-1/2) 仍满足上述条件。每个坏对删去一条边，总计删去 s_r=o(r) 条；剩余简单相交 r-uniform 子族的最大交集小于 δ_r r=o(r)，且其 cover number 至多比原超图少 s_r。若原序列 m/r→c<∞，剩余边数比仍趋 c，cover 比率只变化 o(1)；应用 Kahn Corollary 5.4 得 limsup τ/r≤c/(c+1)。若 τ/r→1，任何有界 m/r 子列都导出矛盾，故 m/r→∞。这也说明 Kahn 的任何 O(r)、τ=r 构造都不满足 I=o(r²)。

Kahn §5 的 Theorem 5.2 是固定辅助 uniformity/rank 的 fractional-cover 到 integral-cover 渐近定理；Corollary 5.4 给出单条调和曲线 c/(c+1)。这一节没有按整数 degree 层次取整得到主稿的分段包络 h(c)，也没有主稿的非整数端点 gap 或整数端点 degree-variance rigidity。c/(c+1) 在正整数 c 处等于 h(c)，非整数 c 处弱于 h(c)。已核对的 §5 引用链（Rödl、Frankl–Rödl、Pippenger、Pippenger–Spencer，以及当时未发表的 Kahn [18]）未见分段插值或相同刚性结论；这是有限来源核对，不作不存在先例或优先权声明。

## Kahn §5 的 Conjectures 5.5–5.6：有限状态核查

原文把两条内容明确标为 conjecture，而非定理（印刷 pp.140–142）。Conjecture 5.5 的原始假设是辅助超图 J 为 r-regular、顶点数至多 cr（c 固定），对所有不同顶点 x,y 有 d(x,y)>0，且 max{d(x,y,z): x,y,z 两两不同}=o(r)；预言 integral covering number p(J)≤(c/(c+1)+o(1))r。r 是 J 的 regular degree，不是 J 的 uniformity；J 可为非均匀超图。其 incidence dual 可写作一族 r-uniform 两两相交边，边数至多 cr，三边公共交集最大值为 o(r)，而两两边交集不要求 o(r)。原 conjecture 以辅助超图假设为准；对偶中不额外宣称边无重复（simple），因为 J 的条件并未排除两个顶点有相同关联边集。此情形不由 Corollary 5.4 覆盖。

Conjecture 5.6 假设固定 edge-size bound k 的超图 J 有 fractional tiling t。按原文，对 X⊆V(J) 定义 t|X(A)=Σ{t(B): B∩X=A}（A⊆X）；b(t) 是所有满足“每个 |X|≤b 时 t|X∈MP(X)”的最大 b；α₃(t)=max{t(W): W⊆V(J), |W|=3}。当 b(t)→∞ 且 α₃(t)→0 时，猜想 p(J)≤t(J) 的渐近式。Kahn 说明这类局部匹配多面体条件意在刻画 fractional tiling 转为近完美 integral cover 的充分局部结构。其说明给了图情形的匹配定理类比及三均匀情形反例，但没有把 Conjecture 5.6 写成已证定理。

有限后续核对包括该文所引 Rödl、Frankl–Rödl、Pippenger、Pippenger–Spencer 与 Kahn 1996, “Asymptotically Good List-Colorings,” *Journal of Combinatorial Theory, Series A* 73(1) (1996), 1–59, DOI 10.1006/jcta.1996.0001。后者是相关近完美超图边染色工具，但本轮未找到其陈述或证明 Kahn 1994 Conjecture 5.5/5.6 的上述 cover 版本。以精确标题/术语检索的有限范围内，未确认两猜想已被完整解决，也未确认反例或足以推出目标结论的部分定理；故目前只能记为“本轮未核实到解决”，不能据此断言仍开放。Kahn 1994 §5 的引用链将其结果追溯到 Rödl、Frankl–Rödl、Pippenger 及 Pippenger–Spencer，并将 “On a theorem of Frankl and Rodl” 列作当时在准备中的未刊稿；因此不能把这些前置工具误记成两条 conjecture 本身的证明。
