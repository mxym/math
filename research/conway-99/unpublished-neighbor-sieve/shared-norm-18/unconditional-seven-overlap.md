# Every absolute-seven norm-18 overlap is balanced and contains at least five edges

Let t,u be two integral neutral −4 eigenvectors of squared norm 18 in a putative SRG(99,14,1,2). Reverse one sign to make t·u=7. Their supports S,T meet in a set F of seven sites, all with matching nonzero signs: q=t−u is a signed-unit norm-22 eigenvector, so opposite nonzero entries are impossible and the dot product counts the overlap. Let e(q) count edges induced by the eleven positives of q; its negatives induce the same number by the eigenvector equation. Then:

* The seven agreeing sites have three of one sign and four of the other.
* The subgraph induced by F has at least 5+e(q) edges. It is a subgraph of the bipartite support of t, with the sign split just stated.

There is no hypothesis on the Seidel rank, on any short-shell vanishing or on the internal edges of q. For a pair with product −7, negate one field first. We use the [seven-cancelling-site obstruction](seven-overlap-core.md) only **after** proving its required independence in the only troublesome unbalanced case.

For the elementary facts used below, the neutral norm-18 support is four-regular bipartite on its two nine-site signs. Norm 22 is always signed-unit: a doubled site would translate by a standard mark d_i=(3I−A)e_i to charge one of norm at most 17, below its minimum 21. See [the short-shell graph analysis](../short-shell-moments.md). Denote a_t=1_S. The [true norm-36 fields](height-three.md) satisfy
```
s(t)=1+3·1_{neg(t)}−A1_{pos(t)},   s(t)−s(−t)=t,
z_t=s(t)+s(−t)=2·1+(3I−A)a_t.
```
From Aq=−4q, summing on the positive and negative sites shows that q has 44+2e(q) cross edges, hence its support has 44+4e(q) internal edges. Set H=e(F), a=H−e(q), and m=Σ_F t=Σ_F u. The relation (3I−A)^2=7(3I−A)+2J gives
```
z_t·u=z_u·t=7m,      z_t·z_u=7(3|F|−a_tᵀA a_u+36).
```
Indeed (3I−A)1=−11·1, and each support has size 18. There are 28−2H edges from F into S\F and equally many into T\F. Each of these two exclusive sets then induces 36−H−(28−2H)=8+H edges. Their union is the support of q, so the number joining them is 44+4e(q)−2(8+H). Therefore a_tᵀA a_u=84+4e(q)−4H. As s(−t)=(z_t−t)/2, the integral neutral field y=s(−t)+s(−u) has
```
y² = 72+(z_t·z_u−14m+7)/2 = 14a−19−7m.
```
At every common negative site of t,u, the entry of y is +2. Two such sites i,j are nonadjacent. The charge −2 translate y−d_i−d_j has squared norm y²−6: the norm of d_i+d_j is 50 at a nonedge, and y·d_i=y·d_j=14. The translated vector has coordinate sum +22 and two actual entries −1 at i,j. Its sum of absolute coordinates, and hence its squared norm, are at least 26. It follows directly that y²≥32. This argument does not posit a missing norm-30 or charge-one shell.

For completeness, the initial two-support counting argument of [seven-overlap-core.md](seven-overlap-core.md#why-there-are-only-two-preliminary-imbalances) is valid even when q has internal same-sign edges. Negate both inputs to make the positive subset of F the larger, of size k. Each of its k sites has four neighbors in each original nine-site negative set, and all pairs among these k have at most two common neighbors globally. The two nine-site negative sets overlap in exactly 7−k sites. For k=6 balancing 24 contacts over nine targets gives at least 21 pair witnesses in each; subtract at most six duplicated witnesses (one shared target of degree at most four). Thus 36>2 C(6,2). For k=7 they are disjoint, giving ≥2·30>2 C(7,2). For k=5, write r,s for the numbers of the five sites adjacent to its two shared opposite sites. Then r,s≤4 and r+s≤7, since distinct shared sites can have at most two common neighbors. The common-neighbor quota on the five is
```
C(r,2)+C(s,2)+2 min{Σ C(x_i,2): seven nonnegative x_i sum to 20−r−s} ≤20.
```
The minimum distributes entries as evenly as possible; checking 0≤r≤s≤4, r+s≤7 gives only r=s=3. Hence H=6. Here m=3, and a≤5 in the displayed formula for y² would give at most 30, one of the forbidden sizes above (or a negative number). Hence a≥6, forcing e(q)=0. The precise hypothesis of the certified seven-overlap-core theorem now holds for t and −u; it rules out this 5/2 split. Finally k=4, m=1, leaves y²=14a−26 with three doubled positive sites. Again a≤4 would give at most 30 in the forbidden list. Therefore H≥e(q)+5 as claimed.
