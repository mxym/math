# Charging shared norm-18 triples to actual positive-charge labels

Assume only N16=N20=0, with no restriction on (1,27), (2,30), any other selected unit, or the Seidel rank. Write B_j for the actual (positive-charge) (2,30) fields whose four positive sites span j edges, and n_1 for the actual (2,26) fields whose two positive sites have exactly one negative common neighbor. Then
```
9N18 ≤ 110,880 + 36B_0 + 37B_1 + 30B_2 + (3/2)n_1.
```
This is an upper bound for the **same oriented N18 population**, not a declaration that the populations on the right vanish. Here B_0+B_1+B_2=U230. If U230=0, the sharper [exact root theorem](norm18-triple-exterior.md) deletes the n_1 term entirely.

## Classifying triples with dot nine

Use the [local three-label result](panel-heights.md#the-three-label-exclusion-and-the-rank-38-contradiction). There are at most three markings per seed; in a triple each marks four of six pair centers, omitting its pair L_i. All paired dots are 7 or 9, with no opposite conflicts. Triple seeds number at least 9N18−110,880. A triple with exactly **two** dot-nine pairs is impossible by the [two-private-leaf argument](norm18-triple-exterior.md#partial-cores-and-the-missing-neighbors), which for this case does not require U230=0.

Let T_9 count triple seeds with either one or three nines. The [cost formula](rooted-norm18-triples.md) gives, for either endpoint i of the unique nine or for every i in the all-nine case, a signed-unit (2,30) field
```
b=w+d_x+d_y,    w=t_i−t_j−t_k,    L_i={x,y}.
```
Its nonadjacent positive pair x,y is marked. (Raw (2,30) is always signed-unit as shown in the same reference; hence four positives, 26 negatives.) No three positive sites of b induce two or more edges: subtracting their three site marks gives charge −1 and cost at most 30+53−2(21+12)=17, below the true charge-one minimum 21. Thus the four positives form a matching.

At a positive of b outside x,y, adjacency to at least one of x,y requires w≥2. No opposite conflicts are possible in the underlying triple. When t_j·t_k=7, their only common negative sites are Q, which are negative also in t_i, so this never happens. When t_j·t_k=9, there is just **one** extra common negative besides Q by the [dot-nine common-panel theorem](panel-heights.md). Only that site can have w=2, and if adjacent to both x,y it is a zero, not a positive, in b. Thus a one-nine output marks a pair of *isolated* positives; a three-nine output marks a nonedge and at most one other positive can be adjacent to the marked pair. In particular a perfect-matching B_2 field cannot arise in either construction.

For fixed b,x,y, the seed root o is negative and misses both x,y. Each positive sees at least eight negatives since d_N(p)=8+d_P(p). At most two negatives can see both. Hence at most 26−(8+8−2)=12 choices of o exist. At o the positive neighbors of w are precisely Q: each of its three markings vanishes on every other neighbor of the positive root. Thus b,x,y,o recover the seed and its (uniquely specified) group of three markings. Pay weight 1/2 per output in a one-nine triple and 1/3 per output in a three-nine triple. A B_0 field has six possible marked pairs so receives weight at most 6·12/2=36. A B_1 field has one isolated pair usable at weight at most 1/2, plus four other nonedges, each usable only at weight 1/3. Thus
```
T_9 ≤ 36B_0 + 22B_1.
```

## Charging all-seven triples through edged differences

If every oriented pair difference r=t−u of an all-seven triple has independent signs, the [38-site proof](norm18-triple-exterior.md) already refutes it: the only use of U230 absence in the all-seven core construction was to obtain this independence. In particular Farkas verification, the private incidence margins, and raw (3,37) unitarity require no shell absence. Hence every surviving all-seven triple contributes at least **two** incidences (r,o,Q) with an *oriented edged norm-22* difference, one for each choice of its sign. The oriented difference occurs at most once at a given seed: distinct differences of three equal-norm vectors cannot coincide unless their middle vector is a midpoint, making all three equal.

For such r, each sign has eleven sites; each site sees four more opposite than own-sign sites. Thus the two signs have the same number e of internal edges. Write H for the common per-sign height on its 77 complement sites, and J_P,J_N for the sums of binomial(degree,2) in each internal sign graph. Counting incidences from positives gives ΣH=110−4e; counting pair common-neighbor slots on positives gives Σbinomial(H,2)=44−9e−J_P−J_N. Thus
```
#{H=0} ≤ Σ (H−1)(H−2)/2 = 11−5e−J_P−J_N.
```
For e≥1 there are at most six such roots. Also e≤2. Any root counted below has H=0, since t,u agree and vanish on the closed root neighborhood except for their identical root and parent values.

Fix r and such a root o. Each of the eleven positive and eleven negative r-sites is represented by its two neighbors in N(o), forming 22 distinct colored edges K among fourteen vertices (any other vertex outside the closed star is the unique second common neighbor of its two parents). The red edges represent r-positive sites, blue edges represent r-negative sites. In a triple with difference r, the four parents Q contain exactly two edges of each color: the two other internal pairs represent the two shared positive centers of t,u. Once Q is fixed, the field pair is determined: a red site meeting Q is t-positive, one missing Q is u-negative; interchange t,u for blue. This uses only the exact four-center/four-singleton geometry of each marking (and negative independence), not independence of r’s own signs.

Write m for the number of such Q at fixed r,o and C for the number of unordered distinct pairs Q,Q′ sharing a colored edge. The [two-seed distance calculation](norm18-norm22-root-capacity.md) still applies. For clarity, the quantity d=||t_Q−t_Q′||² is 28−a(a+3)−2j where a=|Q∩Q′| and j counts true root mate edges crossing Q\Q′ to Q′\Q. Its derivation identifies the marks using the colored 22 edges as above and the root equation A_K1_Q=h−1+1_Q+M1_Q (h common red/blue degree, M root matching); no independence assertion on the red or blue *sites* of the true graph occurs. Since distinct norm-18 fields have distance at least 16, a≤2. A shared colored edge thus gives a=2 and j=0 (if j=1 the distance would be the absent 16; j=2 violates the distance minimum). Consequently counting repeated red and blue edge slots gives C≥4m−22, each pair counting at most one. For integer m this implies m≤5+C/2 (trivial if m≤5).

Here is a new inverse on the **colored**, rather than uncolored, shared pairs. Write Q∩Q′={p,q}, and let x be the far site of its colored edge; orient r so that x is red. Write t,u and t′,u′ for the two ordered pairs, with t−u=t′−u′=r, and z=t+u′=t′+u. Then z²=50−d=32. The field w=d_o−z has type (1,27) and is signed-unit: z has its only positive double at o (the shared pair {p,q} is colored, not a common positive of t and u), its negative doubles exactly at p,q, all other contacts from the two nonequivalent common-negative four-sets give −1 on Q△Q′, and all 22 r-sites permit only 0,±1. On N(o), d_o is −1, and elsewhere off the closed star d_o=0. In particular w takes +1 at o,p,q, an induced positive P3. By the [reversible positive-path translation](u226-positive-pair.md#what-absence-of-true-unit-127-forces),
```
b=d_o+d_p+d_q−w=d_p+d_q+z
```
is a c=1 field with positives p,q, unique common zero o and other common site x negative (equivalently z_x=1). This field recovers o,p,q,x and z. On the root neighborhood the four vertices of Q△Q′ are exactly the six b-negative neighbors of o after removing the two mates of p,q. A pair Q,Q′ with this intersection is therefore specified up to swapping by one of at most three unordered partitions into two-element sets. At either seed exactly **one** of the three markings omits x, since every pair center is used twice. For r_x=+1 these are u and u′. The sums z now give t=z−u′, t′=z−u, and hence r uniquely up to the sign chosen at x. Thus across all oriented r,o we have ΣC≤6n_1, including both possible signs and including only the actual edged differences in question.

Finally the number of positive edges summed over all oriented norm-22 fields equals B_1+2B_2. The reversible correspondence sends (r, positive edge pq) to (d_p+d_q−r, same positive edge); the latter has charge 2 and cost 36+22−28=30, and reversing sends it back to charge zero and cost 36+30−44=22. With e≥1 and at most six zero roots per r, summing the bound on m gives
```
2T_7 ≤ Σ m ≤ 30(B_1+2 B_2)+3n_1.
```
Adding T_7 and T_9 proves the assertion. All incidences are of oriented graph markings, not original seven-class averages. These are conditional count inequalities only.

## A pressure bound without excluding (2,30) or (1,27)

For rank 38 and N16=N20=0, all ten other selected units may now occur simultaneously. Write P for their actual positive-charge U127 count. The [disjoint positive path and isolated-edge transfers](u226-disjoint-transfers.md) show 20 n_1+12 n_2≤26P: for a given U127 field write q for its number of positive three-paths, l for its isolated positive edges; then q≤1, 2q+l≤3, the c=1 labels correspond bijectively to paths, and at least two distinct isolated edges are supplied per c=2 label. In particular 20q+6l≤26. With n_0≤4158, use these inequalities together with the new N18 bound in the [native scalar identity](norm18-u226-graph-cap.md). The result is
```
9 U026 +243 U121 +102 U127 +622 U230
  ≥ 200,088+6 U125+57 U228+9 U337 .
```
Indeed the n_1 term in 48N18 contributes 8n_1, the term 12G226 contributes 12(n_0+n_1+n_2), and the direct U127 coefficient is 8, so the total charge-one allowance is at most 34P. Likewise 48·37/9+10=622/3 for U230. Keeping 36B_0+37B_1+30B_2 instead of 37U230 strengthens it by the corresponding positive differences. No arbitrary-rank exclusion follows from the inequality.
