# Every rooted Conway graph gives a rank-32 even-unimodular gluing

Let A be the adjacency of an SRG(99,14,1,2). Fix an arbitrary vertex o with its 14 neighbors N and 84 nonneighbors X. No coclique, automorphism, grid, or sparse marking assumption is made. There is an even rank-30 lattice T, determinant 392, whose dual injects into the integral minus-four eigenfields vanishing on the whole closed neighborhood of o. For its dual vector x the graph field has ordinary squared norm 56(x,x). Moreover T and the binary lattice K of Gram diag(14,28) glue to an even unimodular lattice U of rank 32. These give necessary structures, not nonexistence of a graph.

## The projected frame
On N the adjacency is a perfect matching, with matrix M. A point in X sees precisely two sites of N, necessarily nonmates: a mate pair already has o as its unique common neighbor. Conversely each nonmate pair in N already has o as one common neighbor and requires exactly one further common neighbor in X. Thus the 14-by-84 incidence D has exactly the indicators of the 84 nonmate pairs as its columns. Let A_X be the graph on X.

Use the negative-eigenspace marks (u_i,u_j)=3I-A+J/9 and frame constant 7. Their sum is zero and Au=−4u; in particular u_o is in the rational span of the N marks. Their N-Gram is H=3I-M+J/9, whose eigenvalues are 4 on the seven mate differences, 2 on the six nonconstant mate sums, and 32/9 on constants. H is nonsingular everywhere rationally, and
```
H^-1=(3I+M)/8-J/64,       det H = 2^25/9.
```
The pairing to an X-site with N-column d is −d+1/9. Project orthogonally off N by P and put m_b=√8 P u_b for b∈X (a rational similarity by factor eight on the form). Substituting H^-1, using sum d=2, gives the residual Gram
```
Q = 24I-8A_X+2J-3D^T D-D^T M D,      diag Q=20,     Q²=56Q.
```
In particular Q is even integral, of rank 44−14=30, and these marks generate an even lattice L. Every x∈L* evaluates integrally on them; those evaluations extended by zero on N[o] are the actual graph evaluations of √8 x and therefore are a neutral integral minus-four field. Conversely the tight frame gives the inverse of this map on all such fields. The sum of their squared evaluations is 56(x,x). For x∈L*, 56x=Σ_b(x,m_b)m_b belongs to L; its discriminant thus has only the primes 2,7 and exponent dividing 56.

## Odd local structure and rational determinant
At seven start with the level-seven graph lattice of the [rank-44 construction](../maximal-marked-lattice/README.md). The mark index at three is a unit here, so it is generated over Z7 by all graph marks. Its nonsplit seven-discriminant space has dimension 44-r; each maximal isotropic extension has anisotropic discriminant plane. Since H has seven-unit determinant, the N-mark span splits off unimodularly, and the orthogonal complement is generated locally by the projected X marks (u_o also belongs to the N span here). Scaling the form by eight changes no seven-discriminant isometry class: eight is a square in Z7^× since it is 1 modulo seven. Consequently the seven-primary discriminant group of L is elementary of dimension 44-r, and a maximal isotropic extension leaves exactly an anisotropic plane of order 49. The choice of maximal extension is arbitrary; fields lying in the saturated dual must satisfy that extension's compatibility.

Rationally the full graph eigenspace equipped with the mark pairing has square determinant (the rank-44 graph lattice has determinant 7^(44−r)). Removing the N span of determinant 2^25/9 therefore leaves discriminant square class 2. Rescaling by eight has no effect on a determinant square class in even dimension 30.

## Dyadic maximal extension
After the seven extension, pass to a maximal even extension at two. Its finite nonsingular discriminant quadratic form F is anisotropic, has odd order valuation (by rational determinant square class), and has Brown invariant 30−4=2 mod 8 by Milgram's formula since the anisotropic seven-plane contributes a minus sign. Its exponent is at most four: an element x of order eight would have 16q(x)=0 mod 1, making 4x isotropic.

Here are the elementary options. If F has exponent two, split off order-two quarter-norm lines whenever possible. The leftover has q-values 0 or 1/2, its nonsingular alternating bilinear form has even dimension, and its Gauss sum has even Brown invariant. The dimension of F over F2 is odd, so the number of quarter-lines is odd, making the total Brown invariant odd, impossible.

Thus F has an order-four x. Its q-value is u/8 for odd u (otherwise 2x is isotropic), so the cyclic subgroup splits off nonsingularly. Any other order-four generator in its orthogonal complement would make the sum of the doubles nonzero isotropic. That complement is elementary and contains no element of q-value 1/2, since we could add 2x. Thus it has dimension at most one (two independent quarter-lines have a sum of value zero or 1/2). Odd total order valuation requires one line, and the Brown invariant says u+s=2 mod8 for its sign s=±1 (the cyclic-four Gauss sum is exp(2πiu/8)). The cases (u,s)=(1,+1),(3,−1) are isometric by sending generators x,y to x+y,2x+y. The remaining group is Z/4⊥Z/2 with q-values 1/8,1/4, of order eight.

The resulting T is an even overlattice of L with determinant 8·49=392. In K=⟨14⟩⊥⟨28⟩ the order-two and order-four primary generators at two have q-values 7/4,7/8, respectively; these give the opposite form. At seven, K gives an anisotropic plane (its bilinear unit coefficients 2 and 4 are squares mod 7); in dimension two the negative of the other anisotropic plane is isometric to it. The discriminant forms are anti-isometric, so adjoining the graph of any anti-isometry of them in T*⊥K* produces an even unimodular U of rank 32.

## Literal graph-shell dictionary and scope
Write a U-vector as (x,p e/14+q f/28) with e²=14, f²=28, orthogonal, and integer marked coordinates p,q. If its squared norm is 2j, the corresponding integral field on X has
```
sum_b t_b² = 112j - 4p² - 2q².
```
Use only residue pairs compatible with the chosen gluing; no reverse surjectivity onto every unrestricted graph field is asserted. For example, if R is the number of roots in U then its shell of squared norm 4 has 146880+216R vectors (E4^4+(R−960)ΔE4). This is not a lower bound on any one graph norm, because both p,q and multiplicities matter. A nonzero such U-vector at squared norm 2 or 4 has nonzero graph part, since K has minimum squared norm 14. Any two lifts of the same field at squared norm 4 differ by a K vector of norm ≤16, hence by ±e if distinct; there are at most two. In that double-lift case p=±7 and the ordinary graph norm is 28−2q². Thus every vertex has at least 73,440 distinct oriented nonzero integral minus-four fields of ordinary squared norm at most 224 that vanish on its closed neighborhood. The main point is the low-dimensional exact lattice and its dual dictionary; the broad cumulative count alone does not solve a Seidel rank.

Run `python3 rooted_rank32.py` for the exact frame, discriminant, and scalar Fourier arithmetic checks.

[Two marked moments](rooted-rank32-moments.md) reduce the shortest guaranteed graph norm to 174 and give a companion span bound in the rootless gluing.

[The all-gluing bounded harmonic identities](rooted-rank32-norm136.md) further reduce the guaranteed squared norm **in the chosen saturated dual** to 136. If the chosen dual has no shorter nonzero field, exactly 240 oriented norm-136 fields occur in that dual.

[Before dyadic saturation](rooted-unsaturated-dyadic.md), the universal rank-30 lattice has a fixed local Smith profile, empty norm-two and norm-four primal shells, and a norm-six primal shell controlled by rooted Fano fields and at most 22 checkerboard directions.

[Conflict-free rectangles](rooted-rectangle-fields.md) separately give a graph-only spanning family of actual fields of squared norms 56, 70 and 84 in the entire rooted residual space. These fields need not satisfy the dyadic restrictions of the chosen saturated dual.
