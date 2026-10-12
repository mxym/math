# Ryser 的 intersecting rank-six 情形：文献状态初筛

检查日期：2026-10-07。范围限于有限 (r)-partite、(r)-uniform 超图的 Ryser 覆盖数猜想及其 ν=1 特例。直接检查了早期主文、相关极值构造主文，以及一篇 2026-09-13 发布的近期预印本；以下“未发现”指在这些来源和定向检索中未发现证明，不是对文献完备性的证明。

## 结论

**没有核对到证明每个 intersecting 6-partite 6-uniform (H) 都满足 τ(H)≤5 的定理。**截至本次可核对来源，intersecting（等价于 ν(H)=1）Ryser 特例的最小未决 rank 是 (r=6)：(r≤5) 已知，(r≥6) 仍未决。因而 rank-six 是一个真实的未解决目标；本报告不声称解决它。

需要区分完整 Ryser 猜想。对任意匹配数 ν，猜想是 τ(H)≤(r−1)ν(H)。该一般版本在 (r=2) 是 König 定理、(r=3) 由 Aharoni 证明；一般 (r=4) 尚未解决，所以一般猜想的最小未决 rank 是 (r=4)，不是 6。即使 ν=1 的 (r=4,5) 子情形成立，也不能推出 ν≥2 的完整结论。

## 直接文献依据

1. **Toufik Mansour, Chunwei Song, Raphael Yuster, “A Comment on Ryser’s Conjecture for Intersecting Hypergraphs,” Graphs and Combinatorics 25(1) (2009), 101–109, DOI [10.1007/s00373-008-0821-9](https://doi.org/10.1007/s00373-008-0821-9), arXiv:0709.3138.** 已读 arXiv 主文。引言明确定义 intersecting 等价于 ν=1，记其特例为 τ≤r−1；并称该特例 (r=4,5) 已由 Tuza 证明，(r≥6) 仍开放。文中引理/来源归属列出 Tuza, “Ryser’s conjecture on transversals of (r)-partite hypergraphs,” *Ars Combinatoria* 16 (1983), 201–209；Mansour 等的参考文献还列有 Tuza 1979 manuscript。该文 Theorem 4 给出 (f(4)=6, f(5)=9, 12≤f(6)≤15)，其中 (f(r)) 是存在 (r)-partite intersecting (H) 且 τ(H)≥r−1 时所需的最少边数。它研究极值边数，不证明所有 rank-six 超图有五点覆盖。

2. **Ahmad Abu-Khazneh and Alexey Pokrovskiy, “Intersecting extremal constructions in Ryser’s Conjecture for (r)-partite hypergraphs,” arXiv:1409.4938 (2014; 修订版 2018).** 已读主文。摘要与引言仍明确说 intersecting 版本只在 (r≤5) 已证；其贡献 Theorem 1.1 是 (f(6)=13)，另给出 (r=7) 的 extremal construction。(f(6)=13) 给出 6-partite intersecting 的 τ=5 extremal 例子（存在性/边数最优），说明猜想若真则常数 5 尖锐；它不证明对所有这类 (H) 都有 τ≤5。该 arXiv 主文与发表文章书目可能不同，本报告只引用可直接核对的预印本标识，不把二者书目混为一条。

3. **Patrick White, “Tuza’s Ryser-Conjecture Claim for Four-Partite Hypergraphs with Matching Number Two,” arXiv:2609.14281v1 (2026-09-13).** 已读主文。Theorem 1.1 证明每个 4-partite 4-uniform (H) 且 ν(H)=2 时 τ(H)≤6；这是一般版本中的 ((r,ν)=(4,2)) 个案，并非完整 (r=4) 猜想。引言明确概述 ν=1 的已知边界 (r≤5)，第 4.4 节末尾也明确称 (r≥6) 的 intersecting 特例仍开放。它是截至检查日很新的直接陈述，但属于预印本；不能把其文献综述本身当作“不存在证明”的论证。

4. **R. Aharoni, “Ryser’s conjecture for tripartite 3-graphs,” Combinatorica 21 (2001), 1–4.** 由上述主文引用并核对元数据。其结果证明一般 (r=3) 情形；它决定一般 Ryser 猜想未解决 rank 从 (r=4) 开始，与 ν=1 特例的 (r=6) 边界不同。

## 状态边界

检索中也见到线性 intersecting 系统、(t)-intersecting 版本、extremal construction 分类及一般 Ryser 的部分参数结果；它们各自增加结构或匹配数假设，不能直接推出无附加条件的 rank-six τ≤5。当前证据支持的陈述是：早期公开主文把 ν=1 的 (r≥6) 列作开放，2014/2018 的后续主文仍如此，并且 2026-09 的近期预印本再次明确称其开放；本次未找到后来证明 rank-six 的主文或公告。故应写“截至 2026-10-07 所核对来源中仍未见证明”，而不是无范围限定地断言不存在此类证明。
