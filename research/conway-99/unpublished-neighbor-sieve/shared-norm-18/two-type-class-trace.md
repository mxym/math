# Whole-class trace bounds for the residual two-type 18-supports

Suppose the only selected unit types are neutral norms 18 and 24, at Seidel rank 40 or 42. In each determinant-49 extension there are **at least 810 distinct unordered pairs** of norm-18 supports whose orientations can be chosen to have dot 6 or 7. At rank 40 this gives **at least 20,250 such pairs in the graph**. These are different pairs; the pairs need not have disjoint endpoints or disjoint sets of graph sites. In particular the result does not replace the separate size-42 matching conclusion or settle the two-type case.

Fix one maximal isotropic extension. All seven-ranks here are ranks of the Seidel matrix over F7. By [residue balance](two-type-residue-balance.md), [short counts](two-type-short-counts.md), and [absence of Fano roots on this face](two-type-no-fano.md), there are n norm-18 labels in each of the eight signed residue classes of norm 4 in the terminal anisotropic plane. For M=1 eligible 22-coclique, 50≤n≤54; for M=3, 51≤n≤53. The eligible labels have zero ordinary inner product with every centered eligible coclique (see the residue-balance proof: the pairing is zero modulo seven and nonzero lifts violate the short-shell restrictions). The centered coclique vectors have squared norm 154/9 and pairwise inner products −35/9 or 28/9: overlap fifteen would force a Fano. For M≤3 their Gram is strictly diagonally dominant, so the labels lie in dimension at most d=44−M.

Choose one signed residue from each antipodal class pair: for the plane with form 4I, take (1,0),(0,1),(2,2),(2,−2). This chooses one orientation of each of 4n distinct norm-18 supports; the [short-support classification](../../short-support-packing/README.md) gives unique orientation up to sign for each support. Write E₆,E₇ for unordered pairs among these representatives of absolute dot 6 and 7 respectively, E=E₆+E₇. Within a class distinct ordinary inner products are −3 or 4, as in the [overlap-matching proof](two-type-overlap-matching.md); use the absolute dot bound 10 and the absence of norms 16 and 20. Two of the six cross-class pairs are perpendicular in the plane, allowing ordinary dots 0 and ±7. Each other pair has baseline a fixed sign ±1 and its exceptional value of the opposite sign and magnitude 6. The values ±8 would give a forbidden norm 20. After orienting an exceptional pair to positive dot, its difference is a neutral labeling of norm 22 or 24; both are unit by the charge-one minimum, so the shared sites all agree in sign. Thus actual support intersections have exactly 6 or 7 sites. No converse is assumed.

## Uncentered: a weighted inequality

For the Gram matrix G of all 4n representatives, the trace-rank inequality gives tr(G²)≥(72n)²/d. Bounding the same-class off-diagonal squares by 16, and using the exact six cross-class baselines, gives
```
98 E₇ + 70 E₆ ≥ (72n)²/d −1296n −64n(n−1)−8n².
```
The cost 98 or 70 is twice (7²−0²) or (6²−1²), because E counts unordered pairs. This already gives E≥611 uniformly, and E≥804,849,895 when M=3 and n=51,52,53. Its weighted form can remain useful alongside the stronger total below.

## Centered separately in four classes

Within class i let u_i be the squared norm of the actual centroid of its n representatives. Set U=Σu_i, and let P=I−J/n. Apply blockwise centering to G, obtaining the positive semidefinite Gram matrix G' of the vectors after subtracting their own class centroids. It still has rank at most d, and tr(G')=n(72−U).

For a within-class block B, off-diagonal entries g satisfy g²=g+12. Thus tr(B²)=294n+(12+u_i)n². Expanding tr((PBP)²) and using ||B1||²≥(1ᵀB1)²/n gives
```
tr((PBP)²) ≤294n+(12+u_i−u_i²)n².
```
For a cross-class block B subtract its constant baseline before centering (the constant vanishes under P). Its deviations are 0 or of magnitude 7; hence ||PBP||²_F≤49 times the number of exceptional pairs in this block, by orthogonal projection. Apply the trace-rank inequality to G' and use Σu_i²≥U²/4:
```
98 E/n² ≥ (72−U)²/d −48−U+U²/4−1176/n.
```
The right side is minimized at U=2(144+d)/(4+d); taking the ceiling gives the following lower bounds, for the true graph and not a formal theta series.

| M | n | lower bound for E by uncentered trace | lower bound for E by class-centered trace |
|---|---|---|---|
| 1 | 50,51,52,53,54 | 611,648,687,726,766 | **810,855,901,948,997** |
| 3 | 51,52,53 | 804,849,895 | **978,1029,1081** |

For rank 42 there is only one extension. For rank 40 each counted pair occurs in exactly two of the 50 extensions: the two original seven-classes span an anisotropic plane (norms 4,4, mutual product 0 or ±1, determinant nonzero square; minus one is a nonsquare). Its perpendicular in the original four-dimensional minus space is a split plane, containing exactly two isotropic lines. These are precisely the H retaining both labels. Conversely, when retained in either one, the pair is a cross-class exceptional pair there, since 6,7 up to sign are not same-class dot products. As the orientation choice per antipodal pair does not change absolute dot, it gives the same supports in both counts. If h extensions have M=3, there are at least **20,250+84h** graph-wide pairs, by division by two. This is stronger than simply treating arbitrary support overlaps as bound occurrences.

## Opposite-direction budgets from neutral norms 22 and 24

Let T22 and T24 count eligible oriented neutral graph fields of norms 22 and 24 in one extension, before any division by eight. A [short-shell and parity argument](two-type-n22-six-decompositions.md) shows that any norm-24 field has at most one norm-18 decomposition, while any norm-22 field has at most six. Each unordered exceptional support pair has two orientations summing to opposite resultants, so
```
2E₆ ≤ T24,             2E₇ ≤ 6T22.
```
These bounds are simultaneous with both trace inequalities; they do not alone settle the two-type case. In the usual normalized notation T22=8W022 and T24=8W024 in H.

The [standard-library checker](two-type-class-trace.py) recalculates the curvature minimum, all the ceilings and the elementary class arithmetic exactly.
