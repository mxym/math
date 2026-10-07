# Rank-six、19 边必要界：定向先例比较

检查日期：2026-10-07。这里只比较已发表/公开定理是否已蕴含“6-partite、6-uniform、intersecting 且 τ=6 时至少 19 条边”；不核查新的度分拆证书。

**本轮检索没有发现已知定理蕴含 19 边界。**但一个 2026 年新预印本已将此前核对到的一般下界从 (q(6)≥13) 提高到 (q(6)≥14)，因此引用时应使用 14 作为当前已核对的一般下界。

1. **Varun Sivashankar, “An Improved Lower Bound for the Erdős–Lovász Cover Number Problem,” arXiv:2606.24878v2 (2026-07-29).** 已读主文。作者定义 (g(r)) 为简单 (r)-均匀相交超图 (H) 中满足 τ(H)=r 的最少边数；Theorem 1(i) 对每个正整数 (r) 证明 (g(r)≥3r-4)。故 (g(6)≥14)。该一般定理自动适用于其 6-partite 子类，但仍比 19 少 5 条边。文中 Theorem 1(ii) 是大 (r) 的渐近界，不应外推到 (r=6)。这是预印本，本文只按其明示定理记录。

2. **János Barát, “Intersecting and 2-intersecting hypergraphs with maximal covering number: the Erdős–Lovász theme revisited,” Journal of Combinatorial Designs 29(3) (2021), 193–209, DOI [10.1002/jcd.21763](https://doi.org/10.1002/jcd.21763), arXiv:2011.04444.** 已读主文 §6。文中回顾的 Erdős–Lovász 通用界为 (q(r)≥\frac83r-3)，所以在 (r=6) 给 (q(6)≥13)；文中称当时该下界 45 年未改进。Sivashankar 2026 的 (3r-4) 已将这个数值提升为 14。Barát 的小阶计算确定 (q(3),q(4),q(5))，没有给 (q(6)) 的 19 边结论。

3. **Ahmad Abu-Khazneh and Alexey Pokrovskiy, “Intersecting extremal constructions in Ryser’s Conjecture for (r)-partite hypergraphs,” arXiv:1409.4938, Theorem 1.1.** 已读主文。其 (f(6)=13) 使用不同定义：(f(6)=\min |E(H)|)，其中 (H) 是 6-partite intersecting 且 τ(H)≥5。构造实际有 τ=5；这个结果既不声称也不反驳 τ=6 的边数下界。应将 (f(6)=13) 与一般 (q(6)≥14) 及待查的 τ=6 partite 子类严格区分。

定向检索了“6-partite intersecting τ=6 edges/lower bound”“(q(6)) intersecting hypergraph”等 OpenAlex/Crossref 词组；结果中未发现给出至少 19 条边的直接先例。可据此说：19 比本轮核对到的适用一般界 14 更强，且不等于 (f(6)=13) 的已知 τ=5 极值例；不能据此主张优先权或文献中不存在更专门的结果。
