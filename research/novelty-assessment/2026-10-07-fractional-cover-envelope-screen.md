# Universal fractional-cover envelope: limited prior-work screen

检查日期：2026-10-07。对象为 [fractional-intersecting-cover-envelope/paper.md](../../notes/fractional-intersecting-cover-envelope/paper.md) 的有限界与渐近界。本次只作有限文献比较，不检查证明，也不作优先权结论。

## 被比较的结论

主稿假设 H 是有限、简单、相交、r-均匀超图，r≥2，边数 m≥1。令 τ*(H) 为分数顶点覆盖数，亦即其 LP 对偶分数匹配数。对 k=ceil(m/r)≥2，主稿的有限上界为

Uₖ(r,m) = [k(k−1)r²+(2k−1)r+1−m] / [(k²+k−1)r+1−m].

主稿还给出等号分类：τ*=Uₖ 当且仅当 m=(k−1)r+1、H 线性且每个活动顶点度数为 k；等价地，H 是某个 Steiner 2-(m,k,1) 设计、点复制数 r 的 incidence dual。这里不要求 resolvability；若 m>(k−1)r+1，则有限界严格。

对 m/r→c 的序列，主稿推出 τ*/r 的上界 φ(c)：在 k−1≤c≤k（k≥2）时 φ(c)=k(k−1)/(k²+k−1−c)，整数端点 φ(k)=k/(k+1)。在非整数内部，φ(c) 严格小于此前的整数端点线性插值 h(c)。该结果本身是 fractional-cover 结论；主稿明确不从中宣称 integer-cover envelope，并指出一般最优分数权重不能无条件套用 Kahn 的 rounding 条件。

## 最相关的已知结果

1. **Zoltán Füredi, “Maximum degree and fractional matchings in uniform hypergraphs,” Combinatorica 1(2) (1981), 155–162, DOI 10.1007/BF02579271.** 已核对 Springer 原摘要，未读全文。对相交 r-均匀 H，摘要结论是：若 H 是阶 r−1 的 projective plane，则 Δ(H)=m/(r−1+1/r)；否则 Δ(H)≥m/(r−1)。这是最大顶点度与边数的定量关系。摘要没有给 τ*(H) 依赖 m/r 的分段上界，所述 Δ 也不能与 r（边大小）混为一谈。

2. **Zoltán Füredi, Jeff Kahn and Paul D. Seymour, “On the fractional matching polytope of a hypergraph,” Combinatorica 13(2) (1993), 167–180, DOI 10.1007/BF01303202.** 核对 Springer 原摘要，未读全文。摘要陈述其证明了加权 matching conjecture 在 H uniform、H intersecting 或边权函数 b 为常数等情形。取相交 r-均匀 H 的常数边权，并注意任何 integral matching 至多含一条边，可得经典粗界 τ*(H)=ν*(H)≤r−1+1/r；projective-plane 例达到等号。该例是主稿 Steiner-design 等号类的特殊情形，但 FKS 界本身不按 m/r 分层，也不提供主稿的完整有限等号分类。

3. **László Lovász, “On the ratio of optimal integral and fractional covers,” Discrete Mathematics 13(4) (1975), 383–390, DOI 10.1016/0012-365X(75)90058-8.** 核对了出版方摘要及书目，未读全文。摘要给出的主结论是整数 cover 与分数 cover 的比率不超过 1+ln d，其中 d 是最大顶点度。该定理界定的是整数/分数比，不是 τ* 对 m/r 的上界，因而不直接给出本稿的分段式。

4. **Jeff Kahn, “On a Problem of Erdos and Lovasz. II: n(r)=O(r),” Journal of the American Mathematical Society 7(1) (1994), 125–143, DOI 10.1090/S0894-0347-1994-1224593-5.** 已读全文，特别是 §5 Theorem 5.2。Theorem 5.2 设辅助超图 edge-size 有固定上界 k，给定 fractional cover t，并要求其加权 pair codegrees α₂(t)→0；在此条件下，整数 cover 渐近不超过 t 的总权重。它是带小加权码度条件的 fractional-to-integral rounding 结论，不是对任意简单相交 r-均匀 H 的 τ* 上界。§5 Corollary 5.4 的 m/r 调和界也是整数 cover 定理，假设最大两边交集 o(r)。两项结果都未给出本稿的无小交叠假设 Uₖ 或 φ。

5. **Jeff Kahn and P. Mark Kayll, “Fractional v. Integral Covers in Hypergraphs of Bounded Edge Size,” Journal of Combinatorial Theory, Series A 78(2) (1997), 199–235, DOI 10.1006/jcta.1997.2761.** 本轮只核到书目和出版摘要/检索摘要，没有读主文；因此这里只记录为主题相关的 bounded-edge-size fractional/integral cover 先例，不将其定理认作主稿 Uₖ/φ 的先例或断言其不含相关推论。完整定理级比较仍待核读主文。

6. **仓库内先前的 sparse near-linear cover law。** 该工作给出整数 τ 的 h(m/r) 界，但需 I(H)=o(r²) 等条件，并依赖 Kahn 对满足低交叠条件的整数-cover工具。新稿的 τ* 界无需 partite、线性或小交叠条件；对象、参数和结论均不同。主稿也明确提醒：不能直接把新分数界经 Kahn rounding 变成相同整数界，因为所用最优权重未必满足 Kahn 的加权 pair-codegree 假设。

## 有限检索结论

本次围绕 fractional matching/cover 的 m/r 分段界、weight/degree quantile、Füredi、Lovász 与 Kahn 相关主文做了有限检索和上述来源核读。已核实的最近结果分别是 Füredi 的 Δ 对 m 界、Füredi–Kahn–Seymour 的分数匹配对整数匹配界、Lovász 的积分/分数 cover 比率，以及 Kahn 的带固定 edge-size 与低加权 pair-codegree 条件的 rounding。当前已核对来源中没有发现直接陈述主稿 Uₖ、φ(c) 或相同有限等号分类的定理；Kahn–Kayll 1997 主文尚未读，不能据此作排除判断。以上是 limited screen，不代表检索未命中即可证明不存在先例。

## 新增的非整数比率显式缺口

主稿 §6 Theorem 3 进一步表明：固定非整数 c∈(k−1,k)、k≥2，对任意相交 r-均匀超图序列且 m/r→c，无需小交叠条件，均有 limsup τ*(H)/r ≤ φ(c)−ζ_c，其中 ζ_c>0 有显式保守取值。原稿定义 θ=c−k+1、p=φ(c)、a₀=k−1−θ/k、b₀=1−p、t₀=p/k、d₀=b₀−t₀；令 e₀=min{t₀/4,d₀/4,(k−1)d₀/[4(k+1)]}、δ₀=min{a₀d₀/[8(k+1)],kt₀/4}、M=ceil(2/t₀)，则可取 ζ_c=min{δ₀, θ/((a₀+1)(2M/d₀+(M+1)/e₀))}。此处只记录主稿陈述，不审核证明；ζ_c 被标为保守、非最优。

这条 gap 是对无 small-intersection 假设的 fractional optimum τ* 的渐近加强，参数 c 为非整数；它不同于 Kahn §5 Corollary 5.4 的整数 τ 调和界（该结果要求最大两边交集 o(r)），也不同于仓库旧整数 cover law 在 I(H)=o(r²) 条件下排除达到 h(c) 的结果。后两者既不直接给出 τ*≤φ(c)−ζ_c，也不能通过 Kahn rounding 自动转成新 integer-cover 结论，因为新稿没有保证最优 fractional 权重满足 Kahn 的加权 pair-codegree 条件。本次不扩展来源检索，也不据此作原创性优先权判断。
