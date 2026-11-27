# Exact open 60-degree cap multiplicities of the D_n roots, in all ranks

Let Φ=D_n={±eᵢ±eⱼ : i<j} in Rⁿ, n≥4, and let ‖x‖²=2. Write b(x)=|{r∈Φ : r·x>1}| for the number of roots strictly inside the 60-degree cap about x. Then
```
max b(x) = max{ 2n−2, binom(min(n,7),2) } .
```
Both witnesses below are nonroots. The minimum **over nonroots** is 3 for 4≤n≤7 and 0 for n≥8. In particular an arbitrary real nonroot in dimension five blocks between three and ten D5 roots, with both endpoints attained. This sharp all-rank statement is about the classical root configuration, not the unrestricted kissing number.

## When a coordinate exceeds one

Use signed permutations to arrange a₁≥⋯≥aₙ≥0. If a₁=1+t>1, the other coordinates have squared sum <1. All n−1 sums involving coordinate 1 exceed one. The extra star differences a₁−aⱼ>1 arise at the s leaves with aⱼ<t. None of those leaves can belong to a leaf-leaf blocker: if aⱼ<t and aᵢ+aⱼ>1, then
```
a₁²+aⱼ²+aᵢ² > (1+t)²+t²+(1−t)² > 2 ,
```
using that y²+(1−y)² decreases up to 1/2 and t≤√2−1. No difference among leaves is a blocker. The strict sum-edges among the remaining k=n−1−s leaves are pairwise intersecting: two disjoint edges would contribute more than 1 to the leaf squared norm. A pairwise intersecting family of edges is a star, a triangle, or empty and has at most k members. Thus b(x)≤(n−1)+s+k=2n−2, attained at x=√2e₁.

## The threshold graph when every coordinate is at most one

Only sums can be strict blockers. Form the graph with edge ij if aᵢ+aⱼ>1. Its smallest entry is either isolated (if the largest plus smallest is ≤1) or the largest entry is universal. Induction shows that up to relabeling every such graph is constructed by adding isolated or universal vertices, starting with one vertex. In proving the upper bound for this sum-only graph, the argument works under ‖a‖²≤2 as well.

Any four disjoint edges are impossible since each pair contributes more than 1/2 to ‖a‖². Any K₃,₆ is also impossible: summing its 18 strict inequalities and applying Cauchy–Schwarz to the degree coefficients gives ‖a‖²>18²/(3·6²+6·3²)=2. More generally any nonnegative edge weights w, not all zero, certify impossibility if
```
(Σₑ wₑ)² ≥ 2 Σᵢ (Σₑ∋ᵢ wₑ)² .
```
Indeed the actual sums on all edges are strictly greater than one.

For n≤7 the claimed binomial bound on sum-edges is immediate. For 8≤n≤12 the [standalone exact checker](verify-root-dn-cap-multiplicities.js) exhausts all 2ⁿ⁻¹ isolated/universal strings and certifies every graph with more than the proposed number of edges:

| n | over the bound | four-edge matching | K₃,₆ | residual integer weight certificates |
|---:|---:|---:|---:|---:|
|8|14|14|0|0|
|9|82|82|0|0|
|10|279|275|3|1|
|11|739|722|9|8|
|12|1,674|1,641|18|15|

Approximate calculations only *propose* integer weight vectors for the 24 residual graphs; the support, signs and squared inequality are accepted only by exact integer arithmetic. For n≥13, if the smallest coordinate has at least three neighbors, the top three coordinates are joined to all remaining n−3 vertices by monotonicity. This includes a forbidden K₃,₆. So delete a vertex of degree at most two and induct from n=12; the edge count is at most 2(n−1)−2+2=2n−2.

For the other lower witness, put k=min(n,7), take k coordinates equal to √(2/k), and set the others to zero. All binom(k,2) pairs in the support are strict sum-edges, establishing the maximum formula in every rank.

## The opposite endpoint

For n≥8 take all coordinates equal to √(2/n)≤1/2: there are no strict blockers. For 4≤n≤7 the vector with three equal nonzero entries √(2/3) has exactly three. Suppose a point in one of those dimensions had at most two. If a₁>1 its n−1 star sums already suffice; if a₁≤1/2 the squared norm is at most n/4<2. So 1/2<a=a₁≤1. The strict sum-graph has at most two edges, hence a₁+a₄≤1 and a₂+a₃≤1. If a₂≥1/2 then a₂²+a₃²≤a₂²+(1−a₂)²≤a²+(1−a)²; if a₂≤1/2 the same bound follows from a₂²+a₃²≤1/2. Therefore
```
2 = Σaᵢ² ≤ 2a²+(n−2)(1−a)² ≤ max{n/4,2}=2.
```
Strict convexity forces a=1, then equality forces a₂=1, a₃=⋯=aₙ=0. This is itself a root, proving the stated nonroot minimum. Strict rather than closed caps are essential, especially at n=8.
