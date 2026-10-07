# Rank-six、19 边必要界：定向先例比较

检查日期：2026-10-07。这里只比较已发表/公开定理是否已蕴含“6-partite、6-uniform、intersecting 且 τ=6 时至少 19 条边”；不核查新的度分拆证书。

**本轮检索没有发现已知定理蕴含 19 边界。**但一个 2026 年新预印本已将此前核对到的一般下界从 (q(6)≥13) 提高到 (q(6)≥14)，因此引用时应使用 14 作为当前已核对的一般下界。

1. **Varun Sivashankar, “An Improved Lower Bound for the Erdős–Lovász Cover Number Problem,” arXiv:2606.24878v2 (2026-07-29).** 已读主文。作者定义 (g(r)) 为简单 (r)-均匀相交超图 (H) 中满足 τ(H)=r 的最少边数；Theorem 1(i) 对每个正整数 (r) 证明 (g(r)≥3r-4)。故 (g(6)≥14)。该一般定理自动适用于其 6-partite 子类，但仍比 19 少 5 条边。文中 Theorem 1(ii) 是大 (r) 的渐近界，不应外推到 (r=6)。这是预印本，本文只按其明示定理记录。

2. **János Barát, “Intersecting and 2-intersecting hypergraphs with maximal covering number: the Erdős–Lovász theme revisited,” Journal of Combinatorial Designs 29(3) (2021), 193–209, DOI [10.1002/jcd.21763](https://doi.org/10.1002/jcd.21763), arXiv:2011.04444.** 已读主文 §6。文中回顾的 Erdős–Lovász 通用界为 (q(r)≥\frac83r-3)，所以在 (r=6) 给 (q(6)≥13)；文中称当时该下界 45 年未改进。Sivashankar 2026 的 (3r-4) 已将这个数值提升为 14。Barát 的小阶计算确定 (q(3),q(4),q(5))，没有给 (q(6)) 的 19 边结论。

3. **Ahmad Abu-Khazneh and Alexey Pokrovskiy, “Intersecting extremal constructions in Ryser’s Conjecture for (r)-partite hypergraphs,” arXiv:1409.4938, Theorem 1.1.** 已读主文。其 (f(6)=13) 使用不同定义：(f(6)=\min |E(H)|)，其中 (H) 是 6-partite intersecting 且 τ(H)≥5。构造实际有 τ=5；这个结果既不声称也不反驳 τ=6 的边数下界。应将 (f(6)=13) 与一般 (q(6)≥14) 及待查的 τ=6 partite 子类严格区分。

定向检索了“6-partite intersecting τ=6 edges/lower bound”“(q(6)) intersecting hypergraph”等 OpenAlex/Crossref 词组；结果中未发现给出至少 19 条边的直接先例。可据此说：19 比本轮核对到的适用一般界 14 更强，且不等于 (f(6)=13) 的已知 τ=5 极值例；不能据此主张优先权或文献中不存在更专门的结果。

## 扩展到 partite 的 (τ≥r−1) 边数函数

进一步核对了 (f(r)=min{|E(H)|: H 是 r-partite intersecting 且 τ(H)≥r−1})。目前找到的最接近既有 partite 下界是 **Ron Aharoni, János Barát, Ian M. Wanless, “Multipartite hypergraphs achieving equality in Ryser’s conjecture,” Graphs and Combinatorics 32 (2016), 1–15, DOI [10.1007/s00373-015-1575-9](https://doi.org/10.1007/s00373-015-1575-9), arXiv:1409.4833v2.** 已读主文。其 Theorem 2.5 通过各部度数计数及 greedy cover，推出 Corollary 2.6：
\[
f(r)\ge \frac{293}{96}r+O(1)\approx 3.05208r+O(1).
\]
该 (f(r)) 定义包含 (τ=r) 的 Ryser 反例，但系数低于本轮给定的 3.19375 与 3.25。Theorem 2.7 的 (f(6)=13) 构造实际满足 (τ=5)，不是 (τ=6) 反例或其下界。

该文的 Theorem 2.5 已有“逐部/度数分层 + cover 估计”的方法学近邻，但其明确结论只达到 Corollary 2.6 的系数；本次未在已查资料中发现 (3.19375r−O(1))、(3.25r−O(1))、(4r) 或超线性的 (f(r)) 下界。若采用 max-degree-3 residual-cover inequality (4τ(J)≤q+r+4)，后续应标明这是 Sivashankar arXiv:2606.24878v2 Theorem 1(i) 的 Lemma 2（或重述其证明）；当前所述 3.19375 版本才是不依赖该引理的独立初等分支。以上是定向检索，不作优先权结论。

## 本轮针对更强 partite 界及长期问题的复核

所给加强的逐超图不等式是
\[
|E(H)|\ge 5\tau(H)-\frac74r-5.
\]
因此代入定义域 (τ(H)\ge r-1) 得 (f(r)\ge\frac{13}{4}r-10=3.25r-10)。独立初等分支给出的 (|E(H)|\ge5\tau(H)-\frac{289}{160}r-\frac{57}{16}-\frac5{32r})，相应为 (f(r)\ge\frac{511}{160}r-\frac{137}{16}-\frac5{32r})，斜率为 3.19375。ABW 的 Corollary 2.6 仍是本次找到的最强直接 partite 渐近下界 ((293r/96+O(1)\approx3.05208r+O(1)))；Theorem 2.5 的逐部度分布与贪心覆盖是方法近邻，但其明确推出的系数为 293/96。定向查看其引用链及后续讨论（尤其线性系统文献和 Sivashankar 2026 一般非 partite 下界）没有找到 exact same (f(r)) 参数下 (\ge511r/160-O(1)) 或 (\ge13r/4-O(1)) 的已发表或预印本定理。Sivashankar 的 (g(r)) 假设 τ=r，不能代替对 τ=r−1 extremals 的 (f(r)) 下界；其约 3.0534 的渐近系数同样低于两个给定 partite 系数。这里比较的是报告中指定的来源及其可核对引用/后续，不把定向搜索未命中解释为不存在先例。

已核对的 partite 上界/开放问题如下。ABW Theorem 1.3：当阶为 (r-1) 的有限射影平面存在（特别是 (r-1) 为素数幂）时，从相应截短射影平面中随机取 (22r\log r) 条线，在 (r\to\infty) 时以概率趋于 1 仍有 τ\ge r-1；因此该子序列上 (f(r)\le22r\log r)。ABW 引言将“是否总有 (f(r)=O(r))”记录为此前猜想/长期问题；此轮未检索到对所有 r 的线性 partite 上界或 (f(r)) 全部有限的定理。ABW 还讨论 (f(6)=13,f(7)=17)；后来的 Abu-Khazneh–Barát–Pokrovskiy–Szabó, “A family of extremal hypergraphs for Ryser’s conjecture,” *J. Combin. Theory Ser. A* 161 (2019), 164–177, DOI [10.1016/j.jcta.2018.07.011](https://doi.org/10.1016/j.jcta.2018.07.011), 给出进一步 extremal constructions，属上界/存在性而非更强的通用 f(r) 下界。另，Francetić–Herke–McKay–Wanless 关于线性 intersecting partite 系统在 (r\le9) 的结果有线性假设，不能解决一般 partite (f(r))。

因此当前可比较的差距是：所给 (3.25r-10) 若证明成立，会超过 ABW 的 (3.05208r+O(1)) 下界，并适用于其更宽的 τ\ge r-1 定义；即使不使用 Sivashankar 的 max-degree-3 residual-cover 引理，3.19375 斜率的初等分支也超过已查到的下界。关于长期上界，ABW Theorem 1.3 给出当 (r-1) 阶有限射影平面存在时的子序列上界 (f(r)\le22r\log r)，但它不是全体 r 的线性界；本轮核对的来源仍把“是否对所有 r 有 (f(r)=O(r))”作为未解决问题。ABW 的定义只在存在相应超图时才有有限最小值，本轮也未找到证明每个 r 都有 τ\ge r-1 的 r-partite intersecting hypergraph 的结果。以上是来源状态初筛，不核验新推导或其证明。
