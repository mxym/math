# Fixed double-cover cubic section incidence

This is a divisor-geometric refinement of the interpolation setup in [Guido Lido, §6](https://arxiv.org/html/2206.10327v2#S6). The uniqueness of interpolation at three points is not a new result. This note does not give a discrete-logarithm algorithm or an estimate for a sampler that varies the covers.

Let k=F_Q contain F_q, q odd, E/k elliptic. Fix two degree-two maps f,h:E→P¹ with distinct deck involutions, and write P_f,P_h for their pole divisors and D=P_f+P_h. For example, taking two distinct translates of a double covering can provide different involutions.

## Exact cubic-to-numerator bijection

The four functions 1,f,h,fh lie in the Riemann–Roch space L(D). Any linear dependence would give h=−(a f+b)/(c f+d) with not both c,d zero and nonzero determinant (otherwise h is constant). This implies the two maps have identical deck involutions, impossible. On a genus-one curve deg D=4 gives dim L(D)=4, so the four functions form the entire space.

Let C be an irreducible degree-three divisor over k (one Frobenius orbit). The subspace L(D−C) is of dimension one by Riemann–Roch, as deg(D−C)=1. Thus exactly one projective section has C in its zero divisor. The fourth zero, with multiplicity counted, is rational; as a point of E it equals the group-law sum of D minus the group-law sum of C. This follows because degree-one divisor classes identify with E, and div(N)+D=C+P. The coefficient matrix of the section N=(cf+d)h+af+b must have nonzero determinant: a rank-one matrix factors the section into one factor in ⟨1,f⟩ and the other in ⟨1,h⟩, each with a degree-two effective zero divisor as a section. Their product cannot contain C. Conversely a degree-four section zero divisor cannot contain two different irreducible cubics. The pole divisor D has no cubic component, so containment here is actual rational-function vanishing on C. Consequently exactly (#E(F_(Q³))−#E(F_Q))/3 projective invertible matrices are used, one per cubic. The number is Q³/3+O(Q^(3/2)) by Hasse–Weil; among all Q(Q²−1) matrices the fraction is 1/3+O(Q^(-3/2)).

Consequently any predetermined family of (m) projective sections can meet at most (m) distinct irreducible cubic orbits. This is a fixed-cover incidence bound and says nothing about an extra splitting condition on the selected section. See [the residual-fiber follow-up](EllipticResidualPencils.md).
