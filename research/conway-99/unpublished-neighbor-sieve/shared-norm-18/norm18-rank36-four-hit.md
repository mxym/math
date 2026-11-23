# Flipping a Fano seed and a rank-36 four-type must-hit

At every rank, if N16=N20=0, then the **oriented** neutral graph populations satisfy
```
9 N18 + 42 N14 ≤ 110,880.
```
At rank 36 this implies that at least one of the four selected signed-unit types **016, 020, 228, 337** occurs, without excluding N24. Thus even the complementary eight-type support is impossible, not just a four-type scalar profile. This is not an exclusion of rank 36 itself.

## A Fano seed and its four neighbors

Write a [Fano marking](../../short-support-packing/README.md) for an oriented norm-14 field. Its support is 7+7 bipartite, 4-regular, every same-sign pair having both its common neighbors in the opposite sign. Hence every off-support site sees at most one of each sign. Three like-signed sites determine the whole oriented marking, so distinct oriented Fano fields not opposite satisfy |f·g|≤4 (in each alignment at most two common sites of either sign). A norm-18 marking has a 4-regular 9+9 bipartite support. Distinct oriented norm-18 markings have squared distance at least 16, by the [norm-18 distance bound](../short-shell-moments.md#bounding-the-norm-18-alternative).

If f is Fano and t has norm 18 then |f·t|≤5 under N16=N20=0. Orient for a nonnegative dot. At dot 6 or 8, t−f has forbidden norm 20 or 16. At 7 it is a norm-18 marking at distance 14 from t. At 9 it is a Fano field whose dot with f is −5, impossible by the Fano intersection bound. Larger dots would give a nonzero neutral marking of norm below 14.

At a positive root o of f, let F be its four negative neighbors. Its six remaining positives are the six distinct other common neighbors of pairs in F. Every seed at o has at most two oriented norm-18 fields by the [triangle-free theorem](norm18-triple-remaining-bridges.md#unconditional-capacity-and-scalar-pressure). The seed F itself has none: if d of its pair centers were positive in t, then among t's eight other positives exactly d−4 miss F by the 12 incidences, and only those could be f-negative. All f-positives touch F or are o. Consequently f·t≥1+4+d−(d−4)=9.

Replace one y∈F by its unique mate x in the neighborhood matching of o, obtaining a four-parent seed Q. Write U=F∩Q, the retained triple. For any t at Q let d count its positives besides o with two contacts in U; these are precisely the chosen pair centers from the three U-pairs. By nine incidences from U to the other eight positives, d−1 of them miss U. Every f-positive besides o meets U, because each of the six pairs of F meets the retained three-set U. Thus none of them is t-negative. Only t-positives missing U can be f-negative, and the shared o, three negative parents, and d pair centers give f·t≥1+3+d−(d−1)=5. Equality must hold, so **every** one of the d−1 positives missing U is f-negative.

Suppose Q were double. The two norm-18 markings use exactly four of its six pair centers each, sharing exactly two and covering all six: each uses at least four, and at dot seven or nine their intersection has size at most two by the [pair-label bound](panel-heights.md). (Dots eight and ten are already excluded by N20=N16=0.) Thus at either marking every positive besides o meets Q; those missing U must be adjacent to x. But x is f-zero and sees the f-negative mate y; since off-support f-height is at most one, that is its only negative f-neighbor. The site y cannot be t-positive as it neighbors the t-positive root o. Hence d−1=0 for **both** markings: together they cover at most two of the three U-pair centers, contradicting coverage of all six. Each of the four one-mate flips of F is therefore at most a singleton.

These four flips are distinct from every Fano seed at that root, since two Fano fields sharing three negative parents would agree. Nor do the flips of two different Fano seeds collide. If they did, F,G would differ on exactly two of the same four mate axes, sharing two negative parents. Thus the fields f,g agree positively on o and the center of the common pair, and negatively on those two parents. A possible f-positive/g-negative conflict could only be the center for the two nonshared parents y,z of F: all the other centers meet G, while g's negative side is independent. However y is g-zero, adjacent to the g-positive o and already to its g-negative mate (in G). It cannot have a second negative g-neighbor, so this last center is not g-negative either. The symmetric argument excludes the reverse conflict. The two distinct Fano markings then have dot four, so their difference has forbidden norm 20. In this reasoning y is indeed g-zero because it is adjacent to o and is not one of its four negative g-parents.

There are exactly 7 N14 distinct rooted Fano seeds, and 55,440 possible norm-18 seeds altogether. Per Fano seed the unused capacity is at least two on the seed itself plus one on each of four distinct flips, disjoint from all other such charges. Each oriented norm-18 marking occupies nine positive seeds. This proves the inequality claimed above.

## Exact rank-36 comparison with the same N18

In [the native rank-36 programme](rank36_four_hit_sets.py), let N=N18, f=N14, A=8,429,899,495, B=104,248,536,974,733 and c=80,688,058,247. The [exact integer verifier](norm18_rank36_four_hit.py) proves, **without any assumption on N24**, that under N16=N20=0
```
A N + (2,567,141,254,326 U228+1,283,078,454,961 U337)/2402 ≥ B+c(112−f).
```
The nonnegative inputs are W333, W335, W444, the native Y1 and Y3 rows, the original coclique tangent ('Ct',34), the graph Sidon tangent ('G',15000), and nonnegative unit populations including 024. The conditional row called 'no20/24' is used only for its exact **linear form** 112−f, *not* for its sign. The valid row 'no20' independently gives f≤198. Here 2402 is the rank-36 conversion from normalized anisotropic unit counts to graph counts; N and f count both orientations and U228,U337 count positive charge.

Substitute the new graph bound. The affine function `9[B+c(112−f)]−A(110880−42f)` takes the positive values `84863139479973` and `11180063884239` at 0 and 198, respectively. Therefore
```
9(2,567,141,254,326 U228+1,283,078,454,961 U337) ≥ 2402·11,180,063,884,239.
```
The two unit counts cannot both vanish. In fact U337=0 forces U228≥1,163, and U228=0 forces U337≥2,326. The earlier formal exact-four support `{018,026,125,230}` is one of the excluded subfamilies.
