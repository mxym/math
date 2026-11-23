# The norm-18, norm-24, positive (2,26) support is impossible at rank 38

In a putative Conway graph of Seidel rank 38 suppose the twelve selected **unit** types are confined to (0,18),(0,24),(2,26). Let N=N18 be the graph-wide **oriented** norm-18 count and s=344·E_H S_H the weighted count of extra true unit (1,23) fields, where S_H=W123−99−7W014. We prove a contradiction with the same graph population N≤16,166. This excludes this support at rank 38, not the other rank-38 supports or the unrestricted graph.

Use [the triple theorem](rooted-norm18-triples.md), [the root incidence and distance formula](norm18-norm22-root-capacity.md), and [the secondary-center accounting](norm22-root-collision-charges.md). If T denotes the number of actual three-mark seeds, 6T≥6(9N−110880). The three markers at a seed have pairwise dot seven; their common positive positions for a pair t,u are the root and exactly two shared pair labels, and their common negatives are precisely the four parents. Their six parent-pair labels each occur positively in exactly two of the three fields. We count collisions of distinct seeds Q,Q′ at the same (oriented r,o), with r=t−u an N22. After cancellation of the m=0 collisions against the exact height-four debit, we have
```
  6T ≤ 11N22 + C1 + C2,
```
where m=|Q∩Q′| and Cj counts unordered seed pairs for each **oriented** r. The original zero-height formula also has a negative height-three term which we do not use. We now show C2=0 and C1≤8s.

## The reversed dot-nine seed excludes m=2

Write t,u for the two fields at Q, and t′,u′ for their counterparts at Q′, so t−u=t′−u′. As in [the m=2 collision construction](norm22-root-collision-charges.md), b has type (2,26) with positive sites o,x, and
```
 z=d_o+d_x−b=t+u′=u+t′,      ||z||²=32 .
```
The two common neighbors Z={q,q′} of o,x are its common zeros, and Q∩Q′=Z. Recall [the c=0 profile](u226-positive-pair.md#fixed-positive-pair-when-c0): the eight negatives of b with no hub contact are split into four X_q touching q and four X_q′ touching q′. At either q, z is −2; its positive neighbors with respect to z are o,x of value +2 and X_q of value +1. Indeed each q-neighbor outside o,x not adjacent to a hub has z_y=−b_y, so among them only the four in X_q can be positive. A q-neighbor adjacent to at least one hub has z_y≤0. The two X subsets are disjoint.

Both components in *each* decomposition z=t+(z−t) are negative at q and q′, and so none can be negative at a neighbor of either (the norm-18 negative side is independent). Each component is positive at o,x, and its remaining two positive neighbors at q therefore form a two-subset of X_q, with the complementary two-subset used by z−t. The same holds at q′ and for u. The fields t,u already share positive sites o,x and have only three common positives in total. Hence at one of q,q′ their chosen two-subsets are disjoint. There t and z−u have identical four positive neighbors: o,x and that two-subset.

But t and z−u also share a *positive* seed at x. For clarity: z on N(x) is −2 on Z, −1 on the four x-exclusive b-zeros V, zero on the remainder. Since all four sources are positive at x, none can be positive on N(x). The negative neighbors of t,u there other than Z are disjoint (their only common negatives are Q and x meets Q just at Z). Thus these two-subsets are complementary within V, and the negative x-neighbors of t and z−u agree. Their dot is 16−7=9 since t·z=16. By [the rooted dot-nine panel theorem](panel-heights.md#the-three-label-exclusion-and-the-rank-38-contradiction), two norm-18 fields with a common positive seed and dot nine have **four common positives and five common negatives**. Negating both fields reverses the counts, so the negated pair cannot have another positive seed. Yet the common four positive neighbors at the selected q give exactly such a seed for −t and −(z−u). Contradiction.

## The m=1 cost and the original six-dimensional residue space

Every m=1 collision gives the signed-unit w=d_o−z of type (1,23), with z=t+u′=u+t′ of norm 28. It has a positive edge at o. A unit (1,23) has at most one edge among its six positives (the standard [short-field edge budget](../short-shell-moments.md)); explicitly, if that edge count is e, its 17 negatives need at least 4·6+2·6+2e=36+2e cross edges. The 6 positives supply at most 30−e common-neighbor slots for positive pairs, and Jensen on the 17 negative cross degrees yields at least 29 slots if e≥2 (40 divided across 17 contributes 6 C(3,2)+11 C(2,2)=29); for e≥2 this exceeds 30−e. Thus w has at most two positive edge endpoints o.

For a fixed such w,o, consider all **unordered** decompositions z=t+v into two oriented norm-18 fields (no root restriction). Every component has dot 14 with z. Choose one endpoint from each decomposition. For two distinct decompositions, the two dots against the second pair are d and 14−d. The unconditional norm-18 distance bound gives each at most 10. Dots 10,8,5 would give respectively a forbidden N16,N20,N26 difference. Here raw N26 is absent: a doubled site would translate to charge one of cost at most 21, and all (1,21) labels are unit; the neutral unit (0,26) type is also absent. Of the integers between 4 and 10 only d=7 has both values allowed. Consequently the selected components have pairwise orthogonal **original** seven-residues, each of square 4 (evaluation norm 18 mod 7). They are linearly independent in the rank-38 six-dimensional nondegenerate residue space. Each is orthogonal to z there. If the residue of z is nonzero, it is isotropic (28 mod 7) and its orthogonal hyperplane modulo its radical line has dimension four, still with these pairwise orthogonal vectors of nonzero norm. Hence there are at most four decompositions in this case and six when z has residue zero. No uniformity of populations among classes is being assumed.

Each contributing unordered partition {Q,Q′} in N(o) uses two different decompositions of z. Other partitions cannot use them, since the negative neighborhoods of the two positive-at-o components give their two seeds. Three decompositions associated to a single partition are impossible: they would occupy all three sources at both seeds. At the far-site label of any pair in Q\Q′ (there are three vertices to choose from), the three fields of Q sum to 2, whereas those of Q′ sum to 0 or −1. The latter holds because this far site has zero Q′ contacts so cannot be positive in a Q′ triple; any two such markings share no negative outside Q′. This would give 3z_y=1 or 2. There are therefore at most two unordered collision partitions for nonzero residue, or three for zero residue, each giving just two r orientations. Accounting for the at most two positive-edge roots o gives C1≤8S_nz+12S_0, where the S's count graph-wide extra **unit positive-charge** w of nonzero or zero original seven-class. Ordinary d_o has zero class, so z=d_o−w is zero in the original residue space precisely for zero-class w.

The weight is s=S_nz+344S_0. Indeed (1,23) is isotropic; an eligible H-label lies in the maximal isotropic subgroup itself as H-perp/H is anisotropic. In the [original nonsplit six-space](../affine-witness.md) an isotropic line belongs to a proportion 1/344 of the maximal isotropic planes (there are (7³+1)(7+1) lines overall and 7+1 in each plane). Zero residues belong to all planes. S_H subtracts exactly the ordinary and Fano translates from that unit count. Thus C1≤8s.

## Contradicting the oriented shell count

The [verified norm-22 row](norm18-norm22-root-capacity.md) includes the nonnegative slack and gives N22≤3N−36120−s/4. The [second norm-18 row](norm18-u226-graph-cap.md), with the actual graph bound G226≤4158, gives 11s≤48N−658056. Combining,
```
   6(9N−110880) ≤ 11(3N−36120−s/4)+8s,
   21N−267960 ≤ 21s/4,
   44(21N−267960) ≤21(48N−658056).
```
This forces 84N≥2,028,936, hence N≥24,154 even before any rounding, contrary to N≤16,166. All comparisons are necessary counts on the same rank-38 hypothetical graph.

The [six-type extension](norm18-six-type-pressure.md) retains the graph argument and rules out the entire four-type superset obtained by permitting (2,28) as well.
