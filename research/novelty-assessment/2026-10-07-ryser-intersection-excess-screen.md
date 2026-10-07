# 交叠超额惩罚项：定向文献比较

检查日期：2026-10-07。本短记只比较已公开文献中是否有形如“边数/cover 下界带全局交叠超额惩罚项”或近线性 partite 边数下界的先例，不审查新候选证明。

## 待比较对象

对相交超图 (H)，令
\[
I(H)=\sum_{\{A,B\}\subseteq E(H)}(|A\cap B|-1).
\]
也即 (I(H)=\sum_v\binom{d(v)}2-\binom{|E(H)|}2)，因为每对边至少相交一次。待比较候选为：任意 \(\delta>0\) 存在 (C_\delta)，使
\[
|E(H)|\ge 5\tau(H)-\left(\frac{27-5\sqrt{17}}4+\delta\right)r-\frac{10I(H)}r-C_\delta.
\]
据此，线性类及 (I(H)=o(r^2)) 的 \(\tau\ge r-1\) partite 族会有斜率 \((5\sqrt{17}-7)/4\approx3.40388\) 的候选边数下界。这里的式子和推论仅作为待比较的候选记录。

## 最接近的已知方法

1. **Varun Sivashankar, “An Improved Lower Bound for the Erdős–Lovász Cover Number Problem,” arXiv:2606.24878v2 (2026), §4, Theorem 1(ii), 式 (11)–(13).** 已读主文。该文定义的全局参数是一般 (r)-均匀相交超图、\(\tau=r\) 的 (g(r)\)，并证明 \(g(r)\ge((41-\sqrt{19})/12-o(1))r\)。其第4节有 degree-5 peeling、degree-4 blocks 的 pair-excess 线性化，以及 Kahn 小码度边着色、匹配和大度线性星 cover 的组合。具体地，式 (11)–(12) 对 degree-4 vertices 的 pair-codegree excess 做删除线性化，得到 \(|E(Q_{lin})|\ge\binom q2-5qr/4\)；式 (13) 将匹配与星 cover 的节省合并为平方根项。

   这是**pair-excess 线性化及 matching/star 方法的直接先例**，但其 pair-excess (X=\sum_{\{A,B\}}(\lambda_{AB}-1)_+\) 只计度4块在边对上的重复，随后用于下界辅助线性 4-图大小。它不是对全体原超图交叠超额 (I(H)) 的惩罚型 cover/edge 不等式，也没有给出随 (I(H)/r) 退化的 partite (f(r)) 下界。故新候选的可比内容应限定为全局 (I(H)) 惩罚项及其在 partite 计数中的具体系数/近线性推论；peeling、局部 pair-excess、Kahn matching/star 框架应引用 Sivashankar。

2. **Ron Aharoni, János Barát, Ian M. Wanless, “Multipartite hypergraphs achieving equality in Ryser’s conjecture,” *Graphs and Combinatorics* 32 (2016), 1–15, DOI 10.1007/s00373-015-1575-9, arXiv:1409.4833v2, Theorem 2.5 / Corollary 2.6.** 已读主文。其 proof 使用度数计数及各部中度4顶点形成的 cover saving，推出全体 partite 类 \(f(r)\ge293r/96+O(1)\)。这些计数按顶点度数表达边对交点数，但没有显式保留 (I(H)) 项，最终系数约为 3.05208。

3. **Francetić–Herke–McKay–Wanless, “On Ryser’s Conjecture for Linear Intersecting Multipartite Hypergraphs,” *European Journal of Combinatorics* 61 (2017), 91–105, DOI 10.1016/j.ejc.2016.10.004, arXiv:1508.00951v3.** 已读主文第2节。它处理线性相交 partite 类的度数和 cover 结构，证明 (r\le9) 时 Ryser 界成立；没有给出当 (r\to\infty) 的边数最小值下界，也没有近线性 (I(H)>0) 的稳定型不等式。

## 初筛结论与范围

本次窄查已核对 Sivashankar 第4节、ABW 的 (f(r)) 主下界证明、以及线性 partite 的 FHMW 主文；另以 `intersection excess`, `near-linear intersecting hypergraph`, `Ryser codegree excess`, `cover number` 等词组检索 arXiv、Crossref/OpenAlex。**未找到**形如 \(|E(H)|\ge 5\tau(H)-c r-C I(H)/r-O(1)\) 的全局交叠超额惩罚定理，也未找到对 (I=o(r^2)) 的 partite (f(r)) 给出大于 10/3 斜率的既有下界。此为有明确来源边界的阴性初筛，不能据此称该结果为首次或断言不存在其他先例。
