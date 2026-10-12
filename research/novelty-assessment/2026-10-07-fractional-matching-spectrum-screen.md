# 固定匹配数下的分数匹配谱：有限文献筛查

**日期：2026-10-07。** 本记录仅作来源比较，不检查候选证明，也不作原创性或优先权判断。

## 待比较对象

候选设 `s≥1` 固定，`H` 为秩至多 `r` 的有限超图，匹配数 `ν(H)≤s`，边数 `m`，并令 `m/r→c`。记 `ν*(H)=τ*(H)` 为分数匹配数（由 LP 对偶等于分数覆盖数）。候选完整极限谱为

`Ψ_s(c) = max { ψ(c_1)+…+ψ(c_s) : c_i≥0, c_1+…+c_s=c }`,

其中 `ψ` 是仓库已公开的相交超图分数匹配曲线。候选有限界为 `τ*(H)≤r Ψ_s(m/r)+s/2`；分离的相交组件被给作渐近 sharpness 构造。此处忠实记录候选表述，不审核其推导或构造。

## 已核对的近邻来源

1. **Z. Füredi, “Maximum degree and fractional matchings in uniform hypergraphs,” Combinatorica 1(2) (1981), 155–162, DOI [10.1007/BF02579271](https://doi.org/10.1007/BF02579271).** 已读全文。其主定理针对秩 `r≥3`、匹配数 `ν`，若超图不含 `p+1` 个两两点不交的阶 `r−1` 射影平面副本，则 `ν*(H)≤(r−1)ν+p/r`；Corollary 2 给出相应仅依赖 `r,ν` 的极值结论。它不按边数 `m` 或 `m/r` 细分谱。

2. **Zoltán Füredi, “Intersecting designs from linear programming and graphs of diameter two,” Discrete Mathematics 127(1–3) (1994), 187–207, DOI [10.1016/0012-365X(92)00478-A](https://doi.org/10.1016/0012-365X(92)00478-A).** 已读全文。§4 先回顾上述匹配数—分数匹配数结果，并定义按秩上界 `r` 与匹配数上界 `v` 的极值 `ν*(r,v)`。Conjecture 4.10 明确提出 `ν*(r,v)=v ν*(r,1)`。该猜想没有边数参数；它与候选的组合谱相关，但不陈述 `m/r` 依赖或候选有限误差项。这里仅报告原文的猜想与范围，不判断其后续状态。

3. **Z. Füredi, J. Kahn and P. D. Seymour, “On the fractional matching polytope of a hypergraph,” Combinatorica 13(2) (1993), 167–180, DOI [10.1007/BF01303202](https://doi.org/10.1007/BF01303202).** 已读全文。论文给出 uniform、intersecting 等条件下的加权 matching-polytope 结果，但本轮未找到固定匹配数 `s` 与边数/秩比 `m/r` 联合参数化的谱定理。

4. **Hao Huang, Po-Shen Loh and Benny Sudakov, “The Size of a Hypergraph and its Matching Number,” Combinatorics, Probability and Computing 21(3) (2012), 442–450, DOI [10.1017/S096354831100068X](https://doi.org/10.1017/S096354831100068X).** 本轮只核对 Crossref 元数据与摘要，未读全文。摘要研究固定顶点数 `n`、固定均匀度 `k` 且匹配数受限时的最大**整数边数**。这是 matching-number/edge-count 极值问题，但其参数化、目标量以及固定对象与候选分数匹配谱不同，不能视为候选公式的直接先例。

5. **Peter Frankl, “On the maximum number of edges in a hypergraph with given matching number,” Discrete Applied Mathematics 216 (2017), 562–581, DOI [10.1016/j.dam.2016.08.003](https://doi.org/10.1016/j.dam.2016.08.003).** 本轮仅核对书目元数据，未读摘要或全文。标题显示其属于无权边数与匹配数极值方向；未据此推断其是否包含候选的分数谱或任何等价结论。

## 有限检索结论

本轮用 Crossref 与 DuckDuckGo 搜索了 “fractional matching number”, “matching number”, “rank”, “number of edges” 的联合词组，并核对上列较近来源。已发现的经典背景包括 Füredi 1981 的秩—匹配数上界和 Füredi 1994 Conjecture 4.10 的仅秩、匹配数谱猜想；边数敏感文献检索到的附近结果主要是固定顶点数下的整数边数极值。当前有限检索未找到直接给出候选 `Ψ_s(c)`、`r Ψ_s(m/r)+s/2` 或 `s` 个相交分量谱卷积的定理。此为有限范围未命中，不证明不存在先例；无原创性或 priority 结论。
