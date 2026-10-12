# Kahn 1994 Conjecture 5.5：后续状态有限筛查

**日期：2026-10-07。** 仅核对文献与来源状态，不审查仓库证明，也不以有限未命中宣称猜想仍开放。

## Kahn 1994 原文陈述

Jeff Kahn, “On a Problem of Erdős and Lovász. II: \(n(r)=O(r)\),” *Journal of the American Mathematical Society* 7(1) (1994), 125–143, DOI [10.1090/S0894-0347-1994-1224593-5](https://doi.org/10.1090/S0894-0347-1994-1224593-5). 已核读 AMS 全文 PDF（本地提取文本 `/tmp/kahn.txt`），相关内容在 §5，pp. 139–141。

**Corollary 5.3** 设辅助超图 \(\mathcal H'\) 为 `r`-正则、有至多 `cr` 个顶点（`c` 固定），任意两点共边，且最大 pair codegree 为 `o(r)`；则其 edge-cover number `ρ(H')≤(c/(c+1)+o(1))r`。Kahn 通过分数 cover `t(A)=|A|/(n+r−1)` 得到总权重 `nr/(n+r−1)`，其渐近值为通常的 harmonic expression `nr/(n+r)`，并先做消除大边的步骤。

**Conjecture 5.5** 提议将 Corollary 5.3 的 pair-codegree 条件放宽为 triple-codegree 条件：`H'` 仍为 `r`-正则、顶点数 `n≤cr`，所有不同点对 `x,y` 均满足 `d(x,y)>0`，并要求

`max{d(x,y,z): x,y,z distinct}=o(r)`.

结论仍为 `ρ(H')≤(c/(c+1)+o(1))r`。Kahn 随后写道，他**预期**不能把 triples 再放宽成 4-sets，并预期存在满足 n(r)=O(r)（对偶记法）的例子，其最大四点 codegree 为 `o(r)`。这是作者在 §5.B 的明确预期，不是该文已构造或证明的例子。

**Conjecture 5.6** 是另一条一般化：固定 `k`，`H` 为 `k`-bounded 超图，`t` 为 fractional tiling；若 triple weight `α₃(t)→0` 且局部参数 `b(t)→∞`，则 `ρ(H)≤t(H)` 渐近成立。`b(t)` 表示最大的整数，使任意至多该大小的顶点集 `X` 上聚合后的 `t|X` 都属于 `2^X` 的 matching polytope。注意它不是仅有 2-subset 坐标的图 matching polytope：坐标包含所有大小至少 2 的子集。Kahn 明说 5.6 可能蕴含 5.5，但他当时没有证明这一点；对 5.5 给出的 cover，三重 weight 条件可从 triple-codegree 条件（预先去除大边后）推出，而 `b(t)→∞` 并非一般自动成立。

## Kayll 与 Kahn–Kayll 后续来源

- **P. Mark Kayll, “Asymptotically Good Covers in Hypergraphs,” Ph.D. dissertation, Rutgers University, October 1994.** 全文未取得。本轮取得并阅读了其公开扩展摘要：P. M. Kayll, *Asymptotically Good Covers in Hypergraphs: Extended Abstract of the Dissertation*, DIMACS Technical Report 95-55 (December 1995)，本地全文 `/tmp/kayll95-55.txt`、PDF `/tmp/kayll95-55.pdf`；公开记录：[DIMACS 95-55](https://archive.dimacs.rutgers.edu/TechnicalReports/abstracts/1995/95-55.html)。其 Theorem 2.1 是 Kahn 5.6 的推广版本：固定 `k`、`k`-bounded `H`、fractional cover `t`，在 `α₃(t)→0` 且 `b(t)→∞` 时有 `ρ(H)≤t(H)` 渐近成立。扩展摘要说这是学位论文主定理，并说证明将发表于下条 Kahn–Kayll 论文；没有声称因此无条件证明 Kahn 5.5。
- **Jeff Kahn and P. Mark Kayll, “Fractional v. Integral Covers in Hypergraphs of Bounded Edge Size,” *Journal of Combinatorial Theory, Series A* 78(2) (1997), 199–235, DOI [10.1006/jcta.1997.2761](https://doi.org/10.1006/jcta.1997.2761).** 书目信息由 Crossref 核实，Rutgers Research With Rutgers 页面可读其摘要。该摘要与 Kayll 扩展摘要一致：对固定边大小上界、fractional cover 给出充分条件，使 edge-cover number 渐近不超过 fractional cover weight；它称解决了 1991 年公开提出的一项猜想。Elsevier 全文访问返回 403/captcha；CORE 的 PDF 镜像也返回 403。因此此处没有核读该期刊论文全文，不能确认其正文是否另有对 5.5 的推论或构造。准确标题检索到的是这篇 Kahn–Kayll 论文与 Kayll 学位论文/扩展摘要；没有核实到独立题为 “Edge-covering sparse hypergraphs” 的 Kayll 论文。

因此，**Conjecture 5.6 有 Kayll 学位论文定理及 Kahn–Kayll 1997 论文摘要/书目支持，属于已解决的结果**；但可读取文本没有证明 5.5 的两个结构假设之间蕴含 `b(t)→∞`，也没有明确宣告 5.5 已解决。有限检索未发现能够确认 5.5 状态的后续主文；据此不能称 5.5 仍开放，也不能称其已解决。

## 小四重交叠例子的证据边界

Kahn 1994 §2–§4 的构造确实证明了 `n(r)=O(r)`，即存在边数线性、cover number 为 `r` 的相交 `r`-均匀族。其 §5.B 只把“同样例子还满足最大四点 codegree `o(r)`”写成预期，没有给出该性质证明。Kayll 95-55 扩展摘要没有找到这项四重交叠声明。后续已抽查的两份完整 arXiv 主文——Bucić、Jain、Sivashankar, “Intersecting hypergraphs with large cover number,” arXiv:2503.14918v2，以及 Sivashankar, “An Improved Lower Bound for the Erdős–Lovász Cover Number Problem,” arXiv:2606.24878v2——引用 Kahn 的线性 cover 构造/结果，但讨论的是 cover-number/边数下界或约束顶点数问题；未见它们证明最大四点 codegree `o(r)` 或讨论 Kahn 5.5 的状态。

本次来源检查没有核实到一族满足 `n(r)=O(r)`、`τ=r` 且最大四点交叠 `o(r)` 的已发表构造，也没有核实到其不存在的结果。Kahn 的 “I also expect” 应继续标作预测，不能转述为定理。

## 核验范围

已读全文：Kahn 1994 AMS 论文、Kayll 1995 DIMACS 扩展摘要、arXiv:2503.14918v2、arXiv:2606.24878v2。已核对摘要/书目：Kahn–Kayll 1997 JCTA 论文。未取得：Kayll 1994 dissertation 全文、Kahn–Kayll 1997 JCTA 论文全文。后续引用检索为有限抽查；此记录不是关于 5.5 当前开放状态的穷尽性证明。
