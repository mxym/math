# A doubly singular five-label component needs two disjoint mutual pairs and two heavy rows

Let A be the integral exponent matrix of a five-label [Bożek exceptional autonomous component](https://arxiv.org/abs/1909.09900) at even N. If both det A and det(I−A) vanish, the component has **two vertex-disjoint mutual pairs** and **at least two distinct complementary rows with Ω≥3** (multiplicities counted). At least one of the two disjoint pairs has a larger endpoint whose row has Ω≥3. This excludes the all-semiprime and one-heavy-row cases from the doubly singular branch at every height; it does not exclude arbitrary five-label EACs. Combining with the two [order-divisor](EACNonsingularSquareRoot.md) and [Jacobian](EACJacobianSquareRoot.md) bounds, the five-label centers with at most one heavy row are at most X^{1/2+o(1)} up to X.

### The two-pair condition

Orient p → its complementary prime factors. The graph is loopless, with nonnegative arc weights A_{pq}. Let C_j denote the sum of weights of simple directed j-cycles, with weight the product of arc weights; C_{ij} sums the product of weights of vertex-disjoint i,j cycle pairs, each pair counted once. Permutation expansion gives
     
    det(I−A)=1−C₂−C₃−C₄+C₂₂−C₅+C₂₃.

At five vertices the last two terms are the constant coefficient of det(λI−A), so det A=0 gives C₅=C₂₃. Singularity of I−A forces two disjoint directed cycles by the opposite-sign eigenvector argument in the linked papers: positive and negative supports are both nonempty, and each contains a directed cycle. These cycles have total length at most five and individual lengths at least two, hence contribute at least two to C₂+C₃+C₄. Consequently C₂₂=C₂+C₃+C₄−1>0. This supplies two disjoint directed 2-cycles, or mutual pairs.

We recall the [semiprime emission lemma](EACReciprocalEdgeEmission.md). A mutual pair x<y satisfies N=x+y+hxy for an even h≥2, since x|N−y, y|N−x and the two rows are composite. If the larger endpoint's complementary row is semiprime, the additional prime t=(N−y)/x=1+hy exceeds √N and is isolated in the mutual graph. Distinct such pairs give distinct isolated labels. In particular one of our two upper endpoints must have a heavy row, otherwise their four endpoints and two emitted labels would exceed five.

### One heavy row is still impossible

Suppose there is only one heavy row, necessarily at a larger endpoint s. Name the disjoint pairs (p<q) and (r<s), with q semiprime. The label t=(N−q)/p=1+hq is the sole vertex outside these pairs and has no mutual neighbor. There are no further mutual edges: an edge with semiprime upper endpoint must emit a second isolated label unless it is the pair (p,q); and the heavy upper s cannot have two smaller mutual neighbors, since each would be the least nonnegative residue of N modulo s. Thus exactly these two mutual edges occur.

Write u=A_{pq}A_{qp}, v=A_{rs}A_{sr}. Then C₂=u+v and C₂₂=uv, so the determinant equation reads
     
    (u−1)(v−1)=C₃+C₄.

Both u,v exceed one. Otherwise there would be no 3- or 4-cycles, so also C₂₃=0 and C₅=0. The label t, which is in no 2-cycle either, would lie on no simple cycle, contrary to strong connectivity. Here arc weights are nonnegative so none of these zero totals conceals cancellations.

The exact semiprime row N−q=p·t gives A_{qp}=1, and u>1 forces the other semiprime row N−p=q². Reciprocity gives q≡1 modulo p since p divides q(q−1) and p≠q. At the other pair N−r=s·w with w prime. It cannot be s²: the first square complement q² and this second s² would lie in [N−√N,N), since p<q<√N and r<s<√N in that case. This interval has at most one square for the centers in question (two distinct positive square roots here differ by ≥1 and sum to more than √N, since N−√N>N/4 for N≥4).

By the reciprocal formula w=1+h′r>r and s≠w. If w=t then the smaller input r whose complement is divisible by t would have to equal q=N mod t. If w=q then its smaller input r would have to equal p=N mod q (because N−p=q² and p<q). Hence neither is possible; the only remaining label is w=p, with r<p. But both N−r=s p and N−q=p t are divisible by p, giving r≡q≡1 modulo p. This contradicts 1<r<p and finishes the proof.

The [related August 2026 exponent-matrix record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) advertises low-dimensional counterexample exclusions including five vertices, but the full text remained inaccessible for audit. This note makes the distinct, limited claim for doubly singular *actual* components, including represented centers, and does not infer their nonexistence for every signature.
