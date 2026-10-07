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

## 定向核查 10/3 斜率与线性化 4-block 计数

本轮针对 (f(r)\ge(10/3-o(1))r)（等价地，任意固定 (\epsilon>0) 下对充分大的 r 有 (f(r)\ge(10/3-\epsilon)r)）及其 partite 专属计数组合做了窄范围检索。对 `10/3`, `3.3333`, `f(r)`, `intersecting multipartite` 的 OpenAlex、Crossref、arXiv 搜索，以及下列相关主文比对中，未找到斜率达到 10/3 的 (f(r)) 下界。检索范围有限，不能据此主张不存在先例。

需明确归属：Sivashankar, “An Improved Lower Bound for the Erdős–Lovász Cover Number Problem,” arXiv:2606.24878v2 (2026), §4 已经有本候选使用的完整一般工具链：degree-5 peeling、度-4 blocks 的 pair-excess 线性化（式 (11)–(12)）、Kahn small-codegree edge-colouring / matching，以及大度时的线性 star cover；式 (13) 将 matching 与 star saving 合并为平方根项。故这些 peeling、线性化、Kahn matching/star 及平方根保存**不是新方法**。Sivashankar 在其更一般 r-uniform、τ=r 设置下给出 `|E(Q_lin)|\ge\binom q2-5qr/4`（式 (12)），再结合 matching/star 覆盖，证明其 Theorem 1(ii) 的渐近 `g(r)\ge((41-\sqrt{19})/12-o(1))r`。本轮未在其它来源中找到直接达到 10/3 的 partite f(r) 结论，也不再把上述组合工具的来源状态表述为未检出。

所给新候选相对于该节的具体比较对象应限定为：在残余中保留 (W=x_3/2+x_4)，证明更精细的 partite pair-count 界 `e\ge\binom q2-qr/2-3W`，并将它与由各部结构得到的 `W/r` cover saving 联立，以导出 10/3 渐近斜率。Sivashankar §4 的式 (12) 是直接方法学和技术先例，但其 `5qr/4` 误差项、无 (W) 权重保存以及参数域不等同于此处 partite `f(r)`；当前窄查未发现相同的精细组合或结论。此前报告中的 13/4 有限界候选也应按主文已有署名引用 Sivashankar §4 的相应工具，不应作为该匹配/星保存方法的新意来表述。

最接近的直接 partite f(r) 先例仍是 ABW, *Multipartite hypergraphs achieving equality in Ryser’s conjecture* (2016), Theorem 2.5 / Corollary 2.6（arXiv:1409.4833v2；DOI 10.1007/s00373-015-1575-9）。其证明在假设最大度小于 5 时，先由度数计数得到 4-度顶点数下界（主文 Theorem 2.5 proof 中的 `x_4` 不等式），再由鸽巢原理选一个部内至少 `\lceil x_4/r\rceil` 个 4-度中心，并用贪心构造 cover，获得 `\tau\le |H|/2-\lceil x_4/r\rceil` 型节省。它与 partite 端的逐部度数和 cover saving 有明确近邻性；其最终普适下界仍为 `293r/96+O(1)`，低于 10/3。关于 auxiliary 4-graph 的 near-linear matching/star 平方根步骤，应引用 Sivashankar §4，而非作为未发现的组合工具。

线性子类方面，窄查未发现已知 (f_{linear}(r)) 渐近下界超过 10/3。Francetić–Herke–McKay–Wanless, “On Ryser’s Conjecture for Linear Intersecting Multipartite Hypergraphs,” *European Journal of Combinatorics* 61 (2017), 91–105, DOI 10.1016/j.ejc.2016.10.004, arXiv:1508.00951v3，已读主文第 2 节：它对线性相交 partite 系统按度数计数并处理高次数顶点，但结论限于 `r≤9` 时 Ryser 界成立，没有给出线性类 edge-minimum function 的渐近下界。ABW 的 f(r) 全类下界 `293r/96+O(1)` 当然也适用于线性子类；其 Theorem 1.3 的射影平面子序列随机删边构造本身为线性，给出上界 `f_linear(r)\le22r\log r`（当 `(r-1)` 阶射影平面存在）。在本轮核对的文献中没有发现 `f_linear(r)` 斜率超过 10/3 的既有下界；因此候选 `(5\sqrt{17}-7)r/4\approx3.40388r` 应明确标作待证明的新候选，不是已证明结论或先例结论。

需区分 J. Kahn, “On a problem of Erdős and Lovász II: n(r)=O(r),” *Journal of the American Mathematical Society* 7 (1994), 125–143（ABW 文献 [12]）。该结果是**非 partite**、(\tau=r) 的相交 r-均匀超图线性边数存在性上界；ABW 将其用于截短射影平面随机抽线的构造。它不提供 (f(r)) 的下界，也未在本轮核对到它给出上述 4-block weighted-saving 估计。故“借鉴 Kahn 型匹配结论”应作为候选证明所用的一般工具陈述，并避免暗示 Kahn 已证明 10/3 partite 边数界。

## 20 边 rank-six 更新：与已知 f(6)=13 的区分

新稿 `notes/rank-six-twenty-edge-bound/paper.md` 陈述的是另一参数问题：若六部相交六均匀超图满足 **τ(H)=6**（即确为 Ryser 反例），则至少需要 20 条边。这个 20 边候选结论不等于也不由已知 `f(6)=13` 表达；后者定义为 τ(H)≥5 的最小边数，而已知 13 边实例实际 τ=5。故 `f(6)=13` 是 τ=5 的极值例，不能当成 τ=6 反例或 τ=6 边数下界。

新稿的 Input F 写为：每个六部相交六均匀 H 若边数至多 12，则 τ(H)≤4。已核读其先例 Abu-Khazneh–Pokrovskiy, **Theorem 1.1, §2.1**：作者先引用 Mansour–Song–Yuster 已有 `f(6)≥12`，排除不超过 11 条边的 τ≥5 情形；随后 Lemma 2.9 对恰有 12 条边的情形按最大度分类手工排除 τ=5。该 lemma 字面设 τ=5；τ=6 可由同一分类中的贪心界直接处理：若最大度至少 6，则删去该点关联边后至多 6 条边可由至多 3 点覆盖，连同高次点共至多 4 点；最大度为 5 或 4 时，余下 7 或 8 条边可贪心用至多 4 点覆盖，加上所删高次点给 τ≤5；最大度至多 3 时，文中按 τ≥5 推出的每部至少 5 个顶点及交点总数上限本身矛盾。因此结合已知 `f(6)≥12`，确有“边数≤12 ⇒ τ≤4”的推论。AP 的下界论证是度数分类与手工计数（使用 Lemmas 2.1、2.8、2.9 和 Claims 2.10–2.11），不是计算机证书；该文明确把 computer-aided search 用于 13 边上界构造，而非 12 边下界。

AP 来源应标作预印本 **Ahmad Abu-Khazneh and Alexey Pokrovskiy, “Intersecting extremal constructions in Ryser’s Conjecture for r-partite hypergraphs,” arXiv:1409.4938v1 (submitted 17 Sep 2014; arXiv PDF manuscript dated 9 Oct 2018)**，https://arxiv.org/abs/1409.4938v1。对这篇同题 AP 作品未核到单独期刊发表书目，不附会卷页或 DOI。相同 `f(6)=13` 结果另由 Ron Aharoni, János Barát, Ian M. Wanless 独立发表：“Multipartite hypergraphs achieving equality in Ryser’s conjecture,” *Graphs and Combinatorics* 32(1) (2016), 1–15, DOI [10.1007/s00373-015-1575-9](https://doi.org/10.1007/s00373-015-1575-9)，arXiv:1409.4833v2。两条文献身份与发表状态应分开记录。

对“六部相交且 τ=6 的超图至少 20 条边”做了窄范围快速检索（关键词覆盖 six-partite/intersecting、τ=6、Ryser counterexample、minimum edges，并检查本报告已列的 AP、ABW、Mansour–Song–Yuster、Barát 与 Sivashankar 来源）。目前未命中直接给出同一受限 partite 参数下界 20 的定理；一般 τ=r 的已核一般界仍只给 `g(6)≥14`，而 AP/ABW 的 `f(6)=13` 是 τ≥5 定义。检索范围很有限，只能写“在本次核对的来源中未见”，不据此作原创性、优先权或文献不存在结论。此段记录新稿所引 Input F 的来源和问题参数对照，不审查新稿的 20 边证明。
