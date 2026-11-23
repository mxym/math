# All maximum cocliques form a Sidon family

In a strongly regular graph with parameters (99,14,1,2), let C range over **all** 22-point cocliques. For ordered pairs of distinct such sets the map
```
(C,D) -> 1_C − 1_D
```
is injective. Equivalently, distinct unordered pairs have distinct sums of their two indicators. No compatibility of discriminant classes, maximal extension, rank or graph symmetry is needed.

**Proof.** By the equality case of the Hoffman bound each vertex outside C has exactly four neighbors in C. This also follows by counting: the 77 outside degrees into C have sum 308 and sum of their binomial second moments equal to 2 binom(22,2)=462; their variance is zero. Hence A1_C=4*1−4*1_C. For C≠D put k=|C intersect D| and n=22−k. The indicator difference is a nonzero integral neutral −4 eigenvector of squared norm 2n, hence 2n≥14 by the [neutral minimum](../affine-witness.md). Thus 0≤k≤15 and 7≤n≤22.

Its two exclusive signs give independent n-sets P,Q with four neighbors across for every one of their vertices. Outside P union Q the two side degrees agree by the eigenvector equation; call their common value h_x. Counting edges from P, then double contacts of pairs of vertices in P, gives
```
sum h = 10 n,
sum binom(h,2)=2 binom(n,2)−n binom(4,2)=n(n−7),
sum h²=2 n(n−2).
```
Thus the common residual R=C intersect D, of size k, must lie in a set Z of size at most 99−2n−ceil(50n/(n−2)): the other exterior vertices with h>0 number at least ceil((10n)²/[2n(n−2)]) by Cauchy. In the order k=0,...,15, subtracting k from this upper bound gives
```
0,0,1,2,2,3,3,4,4,4,5,4,4,3,2,0.
```
In particular |Z|≤k+5. Now a second residual R' yielding the same ordered difference would also have k points in Z. The first cocliques of these two ordered pairs therefore share at least n+max(0,2k−|Z|)≥n+k−5=17 points, whereas distinct cocliques share at most 15. Thus the two ordered pairs coincide. Equal sums of two different unordered pairs would yield a repeated nonzero ordered difference by rearranging terms. Doubles 2*1_C cannot equal the sum of a different pair of indicators. This proves the assertion.

**Unfolded graph bounds.** Write m for the total number of actual 22-cocliques and B_k for the number of ordered pairs of distinct ones meeting in k. Simultaneously for 0≤k≤15,
```
B_k <= N_(44−2k),           B_k <= 2G(4,44+2k).
```
The first injection uses the oriented neutral difference (count both signs in N_t). Its image has only 0 and signed units, so on a shell with nonunit entries allowed one may replace the raw N_t above by its signed-unit part. The second injection uses the sum of the two NEGATIVE indicators, a charge-four label with sum −44 and squared norm 44+2k. The extra factor of two is just the two orderings. For k>0 this sum has k entries −2, not just signed units; raw G is the correct enclosing population. Neither graph bound has a divisor of eight or a factor involving the Seidel rank.

For example, sum B_k=m(m−1). If m_x counts cocliques containing x, sum k B_k=sum_x m_x²−22m≥(44/9)m²−22m. Omitting all nonpositive terms of sum(k−4)B_k gives the rank-free consequence
```
sum_{j=7}^{17} (18−j) N_(2j) >= (8/9)m²−18m.
```
This is a necessary conditional population inequality; it does not assert that a coclique exists.
