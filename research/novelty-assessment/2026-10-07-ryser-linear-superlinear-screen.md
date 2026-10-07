# 线性/近线性 partite equality 例的超线性下界：定向先例比较

检查日期：2026-10-07。本短记核查以下候选是否已有文献先例：在线性 partite 子类中，若定义 \(f_{linear}(r)=\min |E(H)|\)，其中 H 为相交 r-partite r-均匀线性超图且 \(\tau(H)\ge r-1\)，是否已知 \(f_{linear}(r)/r\to\infty\)；更一般地，对 \(r_j\to\infty\)、\(\tau(H_j)\ge r_j-1\)、全局交叠超额 \(I(H_j)=o(r_j^2)\) 的相交 partite 序列，是否已有 \(|E(H_j)|/r_j\to\infty\) 定理。这里只做文献比较，不审查候选推导。

## 直接相关主文

1. **Ron Aharoni, János Barát, Ian M. Wanless, “Multipartite hypergraphs achieving equality in Ryser’s conjecture,” *Graphs and Combinatorics* 32 (2016), 1–15, DOI 10.1007/s00373-015-1575-9, arXiv:1409.4833v2.** 已读主文引言及 §2 的开放问题。

   - 作者定义 \(f(r)\) 为所有相交 r-partite 超图中满足 \(\tau\ge r-1\) 的最少边数。其 Conjecture 2.11 是全类的线性上界 \(f(r)=O(r)\)，并明确说该函数是否处处定义（每个 r 是否存在相应例子）也未解决。
   - Theorem 1.3 证明：当 \(r-1\) 阶有限射影平面存在时，从截短射影平面中随机取 \(22r\log r\) 条线，\(r\to\infty\) 时以概率趋于 1 仍有 \(\tau\ge r-1\)。该构造是线性系统，给出相应子序列的 \(f_{linear}(r)\le22r\log r\) 上界；它不是超线性下界。
   - §2 明确把“若另外要求 H 线性、但不要求来自射影平面”列作变体，并说不清线性是否有助于达到 \(f(r)\)；Open Problem 3 问最优例通常为线性、非线性或两者。Open Problem 2 另问截短射影平面的线子集可以稀疏到何种程度而仍保持 \(\tau=r-1\)。因此 ABW 知道线性子问题存在，但没有断言或证明 \(f_{linear}(r)/r\to\infty\)；其表述将线性是否改善 edge minimum 留作开放问题。

2. **Francetić–Herke–McKay–Wanless, “On Ryser’s Conjecture for Linear Intersecting Multipartite Hypergraphs,” *European Journal of Combinatorics* 61 (2017), 91–105, DOI 10.1016/j.ejc.2016.10.004, arXiv:1508.00951v3.** 已读主文引言及第 2、4 节相关陈述。文章证明线性相交 partite 系统在 \(r\le9\) 时满足 Ryser 界；对 \(r\le7\) 的 \(\tau=r-1\) 线性例作了分类，并报告 r=8 有非截短射影平面的例子。结果是小阶结构结论，没有推出线性 equality 例的渐近边数下界或 \(\omega(r)\) 结论。

3. **Varun Sivashankar, “An Improved Lower Bound for the Erdős–Lovász Cover Number Problem,” arXiv:2606.24878v2 (2026), Theorem 1.** 已读主文。其 \(g(r)\) 的定义要求一般（不要求 partite 或线性）相交 r-均匀超图满足 \(\tau=r\)，证明渐近斜率约 3.053。它不处理 partite \(\tau=r-1\) 的线性 equality 类，也没有按原超图全局 \(I(H)\) 控制的近线性定理。

## 初筛结论

在上述 ABW 与 FHMW 主文、Sivashankar 的一般 lower bound 及以 `linear intersecting partite`, `f_linear`, `linear Ryser`, `near-linear intersecting`, `intersection excess`, `superlinear edge lower bound` 为词的 arXiv/Crossref/OpenAlex 定向搜索中，**未发现**已有 \(f_{linear}(r)/r\to\infty\)、\(\Omega(r\log r)\) 边数下界，或对 \(I(H)=o(r^2)\) 的相应近线性 partite 序列推出 \(m/r\to\infty\) 的定理。已知的全类 ABW lower bound \(f(r)\ge293r/96+O(1)\) 自动适用于线性子类，但只是线性阶；ABW 的射影平面随机子集给出某些 r 上 \(O(r\log r)\) 的线性上界。

所以“线性/近线性子类的边数必为超线性”在本轮核对来源中没有被报告为已证结论；尤其 ABW 的措辞反而明确将线性是否有助于降低 f(r) 列为开放问题。以上是定向检索，不构成不存在先例或优先权结论。
