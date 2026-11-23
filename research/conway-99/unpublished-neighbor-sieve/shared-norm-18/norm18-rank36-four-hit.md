# A rank-36 four-type must-hit from Fano neighborhoods and the oriented norm-18 count

At every rank, if N16=N20=0, then the **oriented** neutral graph populations satisfy
```
9 N18 + 210 N14 ≤ 110,880.
```
At rank 36 at least one of the four selected signed-unit types **016, 020, 228, 337** must occur, without excluding N24. Thus the complementary eight-type support is impossible (not the whole rank).

## A Fano seed and its three-parent neighborhood

Write a [Fano marking](../../short-support-packing/README.md) for an oriented norm-14 field. Its support is 7+7 bipartite, 4-regular, every same-sign pair having both its common neighbors in the opposite sign. Three like-signed sites determine the whole oriented marking, so distinct Fano fields on different antipodal lines satisfy |f·g|≤4. A norm-18 marking has a 4-regular 9+9 bipartite support. Distinct oriented norm-18 markings have squared distance at least 16, by the [norm-18 distance bound](../short-shell-moments.md#bounding-the-norm-18-alternative).

If f is Fano and t has norm 18 then |f·t|≤5 under N16=N20=0. Orient for a nonnegative dot. At dot 6 or 8, t−f has forbidden norm 20 or 16. At 7 it is a norm-18 marking at squared distance 14 from t. At 9 it is a Fano field whose dot with f is −5, impossible by the Fano intersection bound (it cannot be ±f). Larger dots would give a nonzero neutral marking of norm below 14.

At a positive root o of f, let F be its four negative neighbors. Its six remaining positives are the six distinct other common neighbors of pairs in F. Every seed at o has at most two oriented norm-18 fields by the [triangle-free theorem](norm18-triple-remaining-bridges.md#unconditional-capacity-and-scalar-pressure), since N16=N20=0. The seed F itself has none: if d of its pair centers were positive in t, then among t's eight other positives exactly d−4 miss F by the 12 incidences, and only those could be f-negative. Every f-positive except o touches F and hence cannot be t-negative. Consequently f·t≥1+4+d−(d−4)=9.

Now let Q be ANY independent four-parent seed sharing exactly three elements U with F. For t at Q let d count its positives besides o with two contacts in U; these are exactly the chosen pair centers from the three U-pairs. By nine incidences from U to the other eight positives, d−1 of them miss U. Every f-positive besides o meets U, because each two-set in F meets this retained three-set. Thus none is t-negative. Only t-positives missing U can be f-negative, and the shared o, three negative parents, and d pair centers give
```
f·t ≥ 1+3+d−(d−1) = 5.
```
Equality must hold, so t−f is a neutral norm-22 field. It has only unit nonzero entries: at an oriented doubled site, subtract the site field to obtain a charge of magnitude one and cost at most 22+23−28=17, below 21. Thus there are no opposite-sign conflicts at all, forcing d=1.

If Q carried two markings, their positive pair-center sets would have size exactly four each, sharing exactly two and covering all six. Each uses at least four, and their intersection has size at most two by [the rooted pair-label bound](panel-heights.md) at the only possible dots 7 or 9. But both markings use only one of the three U-pair centers by the preceding paragraph, contradicting full coverage. Every such Q is therefore at most a singleton.

For each F there are 28 distinct Q: choose one omitted parent in four ways and replace it by any of the seven other sites which extend the retained independent triple (eight extensions including the omitted parent). Distinct rooted Fano parent sets at a given root share at most one site: a shared pair of negatives would give a norm-20 difference by [the Fano square theorem](fano-difference-packing.md#uniqueness-of-oriented-differences-with-the-antipodal-symmetry-accounted-for). Therefore no two of their three-parent neighborhoods overlap, because two triples within a four-set share at least two points. Their own seeds are distinct from every other near seed too.

There are exactly 7N14 rooted Fano seeds and 55,440 potential norm-18 seeds. Per Fano seed the unused capacity is at least two at the seed itself plus one on each of 28 three-near seeds. Each oriented norm-18 marking occupies nine seeds. This proves the claimed joint graph bound.

## Exact rank-36 comparison with the same N18

In [the native rank-36 programme](rank36_four_hit_sets.py), let N=N18, f=N14, A=8,429,899,495, B=104,248,536,974,733 and c=80,688,058,247. The [exact integer verifier](norm18_rank36_four_hit.py) proves under N16=N20=0 that
```
A N + (2,567,141,254,326 U228+1,283,078,454,961 U337)/2402 ≥ B+c(112−f).
```
The nonnegative inputs are W333, W335, W444, the native Y1 and Y3 rows, the original coclique tangent ('Ct',34), the graph Sidon tangent ('G',15000), and nonnegative unit populations including 024. The conditional row called 'no20/24' is used only for its exact **linear form** 112−f, *not* for its sign; no bound on f is needed here. Here 2402 is the rank-36 conversion from normalized anisotropic unit counts to graph counts; N and f count both orientations and U228,U337 count positive charge.

Insert the joint graph bound. The affine function `9[B+c(112−f)]−A(110880−210f)` is positive at zero (84,863,139,479,973), with positive slope 210A−9c. Hence
```
9(2,567,141,254,326 U228+1,283,078,454,961 U337) ≥ 2402·84,863,139,479,973.
```
The two positive-charge graph counts cannot both vanish. In fact U337=0 forces U228≥8,823, and U228=0 forces U337≥17,653. This excludes, among others, the earlier formal exact-four support `{018,026,125,230}`.
