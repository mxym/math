# The graph's ternary −4 code has minimum Hamming weight at least eleven

For a putative strongly regular graph with parameters (99,14,1,2), let A be its adjacency matrix and B=A+I modulo three. Its kernel C is a ternary linear code. The coefficients of every integral neutral −4 marking reduce to a codeword, as −4≡−1 modulo three. Distinct unit markings reduce to distinct codewords. A weight bound on C does not by itself bound the norm26 population enough for the remaining palettes.

The adjacency identity gives B²=B−J and BJ=JB=0 modulo three. The characteristic polynomial is x^45(x−1)^54 by reduction of the ordinary adjacency spectrum. On the generalized zero summand of dimension 45, B²=0 (indeed B²(B−I)=0 globally, so B² vanishes there), and B=J by the identity. The rank-one J annihilates the eigenvalue-one summand, as JB=0, and hence has rank one on the generalized zero summand. Thus dim C=44, and every t in C satisfies ∑t=0 modulo three, since Bt=0 implies Jt=0. The all-one vector is in C. This dimension statement is not needed in the minimum proof.

## A universal signed pair budget

Represent a nonzero codeword by t with coordinates in {−1,0,+1}. Write S for its support, s=|S|, p and n for its positive and negative counts, e for the number of graph edges in S, and e_c for the edges crossing the signs. Let d_z be the number of S-neighbors of z. For z∈S one has d_z≥1 (At≡−t), and when d_z=1 the sole neighbor has opposite sign. At z outside S, d_z=1 is impossible and when d_z=2 the two neighbors have opposite signs.

Let W be the number of common-neighbor witnesses of pairs in S with the same sign, counted across the entire graph. At a vertex z outside S, the number of such witnessed pairs is at most d_z(d_z−2): this is zero if d_z=0 or 2, and for d_z≥3 use choose(d_z,2)≤d_z(d_z−2), strict for d_z≥4. Equality at d_z=3 requires a monochromatic triple. At z∈S, the witness count is at most (d_z−1)² by choose(d_z,2)≤(d_z−1)², with equality possible only for d_z=1 or 2 (and at degree two both neighbors must have the same sign).

Total witnesses of all sign pairs are ∑choose(d_z,2)=2choose(s,2)−e. Also ∑d_z=14s. Summing the pointwise previous bounds therefore yields
`W ≤ 2[2choose(s,2)−e]−(14s−s)=2s²−15s−2e.`
But directly W=p(p−1)+n(n−1)−(e−e_c). Rearranging,
`s²−14s+2pn ≥ e+e_c.`
Since e≥s/2 and 2pn≤s²/2, this requires s≥10.

## Weight ten forces two C4s and an isolated cross edge

If s=10, the coordinate sum condition gives (p,n)=(2,8),(5,5),(8,2). Only (5,5) can satisfy the preceding inequality. Let L count degree-one vertices of the induced S graph. The degree sum gives 2e≥20−L and each of these leaves is incident to a cross edge, so 2e_c≥L. Consequently e+e_c≥10, putting every inequality at equality. All support degrees are 1 or 2. Every cross edge pairs two degree-one vertices; the degree-two sites induce monochromatic cycles. There are k=5−e_c cycle vertices per sign, equally many as each leaf-pair uses one vertex per sign. By the earlier equality case, every exterior contact is empty, an opposite-sign pair, or a monochromatic triple.

For the positive sign the total common-neighbor witness demand is 20−k (there are k internal positive edges). The positive cycle sites supply k and neither a support leaf nor a negative support site adds a positive-pair witness. Thus outer positive triples supply 20−2k, divisible by 3. The only possible k∈{0,3,4,5} is 4. The support therefore has one positive C4, one negative C4 and a single opposite-sign edge between the two other sites, all three components pairwise anticomplete in S.

## The two opposite cap sets cannot exist

Every positive exterior monochromatic triple must consist of the positive leaf and an adjacent pair in the positive C4. Indeed any 3-subset of C4 contains an opposite pair whose two common-neighbor slots are already consumed by the other two C4 vertices. A mixed exterior pair cannot witness any same-sign edge, so the four adjacent positive C4 pairs must have exactly these four exterior triangle caps, all distinct. Similarly there are four negative caps. Consecutive positive caps already share the positive leaf and a C4 vertex. Thus they have exactly two known common neighbors and cannot share any outside these two sites.

Set u=(A+I)t/3 over the integers. Its values are 1 on the positive C4 and the four positive caps, −1 on the corresponding negative sets, and zero at the leaves and other sites. Since t is balanced, the exact identity (A+I)^2=(A+I)+12I+2J gives Au=4t. Thus t+u is an actual +3 eigenvector. At a positive cap its own value is 1; the signed contribution of neighbors in S is 1+2+2=5. All other nonzero possible neighbors are caps, so the +3 equation forces at least two negative caps adjacent to every positive cap (exactly two more negative-cap than positive-cap neighbors). Consecutive positive caps cannot share a negative cap, so their sets of negative cap neighbors are disjoint subsets of a 4-set, each of size at least two. They must be complementary 2-sets. Opposite positive caps therefore have the same two negative-cap neighbors, as well as their common positive leaf: at least three common neighbors, impossible. This excludes weight ten and proves the claim.



## Dual minimum and the exact weight-nine grid dictionary

Since B is symmetric, C^⊥=im B. For x=By one has Ax=(B−I)By=−Jy modulo three, a constant vector. Conversely A has rank45 modulo three (it is invertible on the B generalized zero summand and zero on the eigenvalue-one summand); 1 lies in its image as A1=−1. Thus the preimage {x: Ax is constant} has dimension55, equal to im B. It automatically satisfies ∑x=0 modulo three, by summing Ax and using 14≠0 mod3. The kernel of A within C^⊥ has dimension54.

Write a unit representative t of a nonzero dual word as before. If its constant At residue is zero, all sites (both inside and outside S) have no support degree one, and at degree two have mixed signs. The same witness bound now applies to all sites with no interior exemption: W≤2s²−16s−2e, giving s²−15s+2pn≥e+e_c. Thus s≥10. If s=10, the only possible p,n are 5,5 and equality forces e=0. All witnesses of positive pairs must then come from monochromatic triples, in batches of three, but their demand is exactly 20. So the zero-residue subcode has minimum at least eleven.

If the constant residue is nonzero, negate to make At≡1. All 99 sites have at least one S-neighbor; since their total S-incidence count is 14s, s≥8. Put L=14s−99, the sum of the support-degree excesses over one. A vertex with a negative neighbor in S has at least two S-neighbors (degree one would have residue −1), and sites with at least two S-neighbors carry at most 2L incidences in total: there are at most L such sites, each contributes its excess plus one. If there are n negatives then their 14n incident edges have endpoints in these sites, giving n≤floor(2L/14). In conjunction with p−n≡0 mod3, at s8 this leaves n=1; at s9 it leaves n=0 or 3.

For completeness, if each site has q≤3 neighbors in the negative support, then its support-degree excess is at least 2q−3choose(q,2). At q0 the bound is zero; at q1 the positive contacts must be 2 mod3 so degree≥3; at q2 the degree is at least two; at q3 the proposed bound is negative. Summing gives L≥28n−3∑choose(q,2)≥28n−6choose(n,2), since each negative pair has at most two common neighbors. It rules out n=1 at s8 (28>13) and n=3 at s9 (66>27). The remaining weight-nine word is all positive, with support S of size9.

For this word put z=(A1_S−1)/3 over the integers. It is nonnegative and has sum9. The adjacency identity yields Az=4·1_S−z+1, so z≤1 outside S. Inside S, z≤2 because the S-degree is at most8. If some x inside S has z=2, then x has seven S-neighbors, leaving one other site y in S not adjacent to x. Each of the seven has at most one neighbor among the other six (the graph neighborhood of x is a matching), and at most one more neighbor in y. Its degree in S is therefore at least 1 and at most 3, but congruent 1 modulo3. All seven degrees must equal 1, making y isolated, impossible. Thus z is 0/1 everywhere, an indicator 1_T with |T|=9.

A vertex of T∖S has degree zero into T by Az=4·1_S−z+1. A vertex of I=S∩T has degree four into T, and hence into I. The I set is nonempty since degrees in S are either 1 or 4 (At=1 or 4 on S) and their sum cannot be 9. An induced 4-regular graph on m vertices here must have 6m internal common-neighbor witnesses, and there are at most 2choose(m,2)−2m=m(m−3) total slots; hence m≥9. It follows S=T=I. The induced 4-regular graph occupies every common-neighbor slot internally, so is an SRG(9,4,1,2), the standard 3×3 rook graph. Thus every dual weight-nine word is ±1_S for an induced rook grid. Conversely any such grid saturates the common-neighbor slots inside itself, so an exterior vertex has at most one grid neighbor; there are 9(14−4)=90 such incidences at 90 exterior vertices, hence every one has exactly one. Therefore A1_S=3·1_S+1 and ±1_S are dual words.

In particular d(C)≥11 and d(C^⊥)≥9 are lower bounds, not claims of equality. The latter is an equality exactly when there is a grid, and the oriented number of dual weight-nine words is exactly 2G, G the number of actual rook grids. This yields an honest finite code constraint usable alongside grid bounds; it does not by itself exclude any Seidel rank.

## Prior-work check

The closest retrieved ternary Conway analysis was the [Wave 36 ternary polar-graph audit](https://github.com/YesterdaysLemon/conway-99-research/blob/main/verification/wave36-ternary-polar-bound/audit.md), which concerns the F3 rank of a 231-row triangle-reflection matrix on the conditional n3=4158 endpoint, not this 99-coordinate adjacency code or its weight distribution. The [forced-structure preprint](https://arxiv.org/abs/2608.11211) and [99-graph automorphism paper](https://arxiv.org/abs/2308.02978) do not give these code claims in their stated results. Targeted public queries for Conway SRG with ker(A+I), ternary minimum weight, and the weight-nine grid correspondence did not locate a direct duplicate. This is a bounded comparison, not a priority assertion.
