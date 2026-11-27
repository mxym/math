# An exact coefficient-projection threshold for wrapped canonical ellipses

**Question.** If low-dimensional marginals of an anisotropic canonical Gaussian error on a cyclotomic torus are close to uniform, can they certify that the full error is close to uniform? No. We give an explicit family in dimension four for which **every pair of coefficients converges to uniform in total variation, whereas every triple tends to total-variation distance one**. Even the full law converges *weakly* to uniform, showing why fixed Fourier modes are not enough here. The construction extends in independent quartets to every power-of-two dimension d≥4.

This is a counterexample about a standalone, deliberately varying error law. It uses no public samples, keys, ciphertexts, or real cryptosystem. In particular it gives no security conclusion for the full Ring-LWE problem, a specified parameter set, or the noise widths in a hardness reduction.

## Family and statement

Let d=4h be a power of two, S=Z[Y]/(Y^d+1) and identify the compact torus (S⊗R)/S with (R/Z)^d via coefficients (here R denotes the real numbers). Multiplication by Y is a signed shift J with J^d=−I. Define A=J^h−J^{3h}=J^h+J^{−h} and M=I+A. It is multiplication by the cyclotomic unit 1+Y^h−Y^{3h}. In the canonical embedding this element is real in each complex embedding plane. The two possible multipliers are 1+√2 and 1−√2. Put λ=1+√2. The same family in codifferent coordinates is obtained by scaling both the error and lattice by 1/d, since S^∨=(1/d)S as an ideal; the coefficient torus description is unchanged.

For fixed d let ε_n>0 satisfy ε_n→0 and ε_n λ^n→∞. Let G_n have independent real N(0,ε_n²) coordinates and let P_n be the law of M^n G_n modulo the coefficient lattice. The power basis is orthogonal up to a common scalar in the full canonical metric of a power-of-two cyclotomic, since the conjugate-root sums of each nontrivial coefficient difference vanish. Thus the initial noise is spherical up to scale. The image is a centered canonical Gaussian ellipse, with equal covariance eigenvalues within each conjugate plane. This does **not** mean its coefficients remain independent.

Partition the d integer coordinate positions into h quartets by their residues modulo h. For any fixed set K of coefficient positions, write P_{n,K} for its marginal and U_K for Haar probability on its coordinate torus. Then
```
TV(P_{n,K}, U_K) → 0   if K uses at most two positions in every quartet;
TV(P_{n,K}, U_K) → 1   if K uses at least three positions in some quartet.
```
In the first case this includes joint, not just pairwise, convergence on K. Up to half of all coordinates may be observed and look jointly uniform; yet a triple in a single quartet behaves entirely differently. The full laws P_n converge weakly to Haar. No statement about dimension growing with n is required.

## Proof

**Integral structure.** The signed shift is orthogonal, so A is symmetric. Since J^{2h}+J^{−2h}=0, A²=2I. It follows that M²=2M+I and M⁻¹=M−2I is integral. In particular M acts bijectively on the torus. Both A and M preserve each quartet. In each quartet the diagonal of A is zero, and each off-diagonal entry is 0 or ±1. In the ambient Euclidean metric, the orthogonal spectral projectors of A are Π_±=(I±A/√2)/2. The real covariance is
```
Σ_n=ε_n² [λ^{2n} Π_+ + λ^{−2n} Π_−].
```

**Up to two per quartet.** For any such coordinate restriction K, the principal submatrix of Π_+ has smallest eigenvalue at least c=(1−1/√2)/2. Indeed it is block diagonal by quartets, with one-coordinate blocks 1/2 and two-coordinate blocks having diagonal entries 1/2 and off-diagonals of magnitude at most 1/(2√2). Therefore Σ_{n,K}≥c ε_n² λ^{2n} I. On the coordinate torus the squared Fourier magnitude at k∈Z^{|K|} is exp(−4π² kᵀΣ_{n,K}k). Summing over k≠0 bounds χ² against Haar by a Gaussian theta tail tending to zero, since ε_n λ^n→∞ and |K| is fixed. TV tends to zero as well.

**A triple in one quartet.** Restrict to three of its coordinates. With j the omitted fourth coordinate, let a be the coordinate unit vector at the opposite position j+2h modulo d. Then a_j=(Ma)_j=0. All M^l a, l∈Z, stay within the same quartet and in the rational span of a,Ma, by M²=2M+I and M⁻¹=M−2I. Thus k_n=M^{−n}a is a nonzero integer vector supported on the chosen triple. The pushforward of the wrapped Gaussian by its circle character k_n has the law of aᵀG_n modulo one, using symmetry of M. This is a wrapped centered N(0,ε_n²) variable. The pushforward of Haar on the triple is Haar on the circle because k_n is nonzero. These scalar laws have distance tending to one: the interval of radius √ε_n around zero has Gaussian probability tending to one and Haar measure tending to zero. TV cannot increase under projection, giving the conclusion for the triple and any larger K containing it.

**Why weak convergence gives the wrong answer.** For every *fixed* nonzero integer k, Π_+ k≠0: otherwise Ak=−√2 k, impossible since Ak is integral and some k-coordinate is a nonzero integer. Hence kᵀΣ_n k≥ε_n² λ^{2n}‖Π_+k‖²→∞. Every nontrivial fixed Fourier coefficient tends to zero. Trigonometric polynomial approximation proves weak convergence to Haar on the full torus. The triple calculation used *varying* integer characters, so there is no contradiction.

## Scope, relation to folds, and prior art

For the sum of w_n independent copies with arbitrary signed-monomial multipliers, commutation with M and orthogonality of signed shifts give exactly the same family with ε_n replaced by √w_n ε_n. The conclusions hold whenever this effective width goes to zero while its product with λ^n grows. This is consistent with the full joint theta criteria in [the preceding overlap bound](overlapping-fold-basis-packing.md); replacing an ellipse by independent errors with the same scalar coefficient marginals generally is not.

[Lyubashevsky, Peikert and Regev](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf) expressly distinguish canonical ellipses from the spherical power-of-two case. Fourier behavior under hyperbolic integral toral automorphisms is classical; for related background in a *different*, noisy discrete-torus setting see [Dubail and Massoulié, Accelerating Abelian Random Walks with Hyperbolic Dynamics](https://arxiv.org/abs/2106.10079). The exact arbitrary-coordinate threshold here relies on the particular signed-shift quadratic unit and its rational invariant planes, not on a dynamical mixing theorem or a new claim of cryptographic insecurity.

[The finite checker](verify-canonical-ellipse-projections.js) checks the signed-shift identities, the two-coordinate projector inequalities, and the preserved omitted coordinates for small dimensions. The limits themselves are proved analytically above.
