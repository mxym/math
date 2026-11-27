# When a spherical lattice Gaussian can have independent integral coordinates

A continuous spherical Gaussian is independent in any orthonormal real coordinates. This does **not** imply that a discrete Gaussian on a lattice becomes an independent-coordinate law after an arbitrary integral change of basis, even at very large width. We classify exact factorization for full modules over cyclotomic integer rings in the standard canonical metric, and prove a wide-Gaussian total-variation gap that is uniform over all integral bases of a fixed lattice.

This is a standalone noise-model criterion, not a sampler, an attack, or a claim about the hardness of a deployed cryptosystem. In [Lyubashevsky–Peikert–Regev, Introduction and Definition 3.1](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf), the power-of-two spherical case gives an isometry with the coefficient metric, in contrast to general canonical ellipses. [Peikert, An Efficient and Parallel Gaussian Sampler for Lattices, §4.1](https://web.eecs.umich.edu/~cpeikert/pubs/pargauss.pdf) distinguishes the standard orthonormal case from independent randomized rounding in a general basis, which gives a different covariance. The results below give a converse across **all** integral bases of standard canonical cyclotomic modules, not just the power basis. They do not apply to arbitrary twisted embeddings, e.g. [The Ring-LWE Problem in Lattice-Based Cryptography: The Case of Twisted Embeddings](https://pmc.ncbi.nlm.nih.gov/articles/PMC8465940/).

## Exact factorization and all-conductor classification

For a fixed full lattice Λ in a Euclidean space and a center c, let D_(Λ,s,c) have masses proportional to exp(−π‖x−c‖²/s²). In an integral basis B of Λ, let G=BᵀB be its Gram matrix and let μ=B⁻¹c. The log of the mass of coordinate vector z∈ℤ^D, up to a constant, is −π(z−μ)ᵀG(z−μ)/s². This distribution is exactly a product of independent coordinate laws in that basis **if and only if** G is diagonal. Sufficiency follows by factoring normalization. For necessity the mixed finite difference at z,z+e_i,z+e_j,z+e_i+e_j of the log mass is −2πG_ij/s², while a product law has every such mixed difference zero. All masses are positive, so the argument holds for every center and width; if factorization holds at even one center and width, the basis is orthogonal.

Now let m>1, K=ℚ(ζ_m), n=[K:ℚ], R=ℤ[ζ_m]. Let M be a full R-lattice in K^t, with the ordinary canonical Euclidean structure, namely trace of the Hermitian form
```
h(v,w)=Σ_(j=1)^t v_j overline(w_j),  ⟨v,w⟩=Tr_(K/ℚ) h(v,w).
```
Full means the underlying integral lattice has rank nt; (t) is the module rank, not the width. Then a spherical discrete Gaussian on this lattice has a product representation in some integral basis if and only if both conditions hold:
1. The conductor m is a power of two.
2. M has a free R-basis (v₁,…,v_t) whose Hermitian Gram matrix is diagonal with positive rational diagonal entries.

Indeed multiplication by ζ_m is an isometry preserving M, since it has magnitude one at every embedding, with rational characteristic polynomial Φ_m(X)^t. On an orthogonal integral basis any lattice isometry permutes its axes with signs and can permute only axes of equal lengths. One way to see this is that the shortest nonzero vectors are exactly the signed basis axes of minimum length. Their span and its orthogonal complement are invariant, and one repeats on the lattice in the complementary span. Thus the isometry is a signed permutation. A length-ℓ cycle has characteristic polynomial X^ℓ−ε with ε the product of the signs. Since m>1 the number 1 cannot be an eigenvalue, so ε=−1. The roots of X^ℓ+1 include a primitive (2ℓ)-th root, hence m=2ℓ; all the other roots must also be primitive of that order. This requires ℓ a power of two, since for any odd prime divisor of ℓ an odd exponent can fail to be coprime to 2ℓ. Hence m is a power of two, and each cycle has length n=m/2. This counts exactly t cycles and shows that the original integral basis, after changing signs and ordering, is the union of ζ-orbits `{v_i,ζ v_i,…,ζ^(n−1)v_i}`. In particular M is free over R with generators v_i.

For distinct i,j the orthogonality of all ζ-orbits gives Tr(ζ^k h(v_i,v_j))=0 for every 0≤k<n. Nondegeneracy of the trace pairing and the power basis imply h(v_i,v_j)=0. On each cycle the same equations for 1≤k<n hold with h(v_i,v_i) instead. For these exponents Tr(ζ^k)=0 in the power-of-two field; subtract Tr(h(v_i,v_i))/n from that diagonal scalar to obtain zero traces also at k=0. Hence it is rational and positive. Conversely a basis with that Hermitian Gram matrix has orthogonal ζ-orbits: inside each orbit the same trace vanishing checks different powers. This proves the classification. For m=2 the statement includes the trivial degree-one case, with no special vanishing equations needed.

## Arithmetic form in rank one

For a nonzero fractional ideal I of a power-of-two cyclotomic field, the criterion is equivalent to
```
I is principal and I·overline(I) = rR for some positive r∈ℚ.
```
Necessity follows because a generator with rational h(a,a)=a overline(a) gives the displayed product. For sufficiency write I=aR and u=a overline(a)/r. Then u is a totally positive unit of the maximal real subfield's integers. It is the square of a real unit by Weber's maximal-signature theorem for the dyadic tower, stated as Proposition 3 in [Dummit–Dummit–Kisilevsky, Signature ranks of units in cyclotomic extensions of abelian number fields](https://msp.org/pjm/2019/298-2/pjm-v298-n2-p03-p.pdf). Explicitly, a full real signature group has 2^[K⁺:ℚ] signs, the same size as units modulo squares by Dirichlet's unit theorem, so the kernel on the quotient is trivial. Replacing a by a divided by the corresponding real unit makes its Hermitian norm equal to r. For K=ℚ the criterion is immediate and the real-unit step is unnecessary.

For example, in the dyadic tower of degree n≥2, for π=1−ζ the lattice of π^k R has exact product coordinates if and only if n divides 2k, a stronger statement than just trying its displayed power basis. Indeed πR is the unique prime at 2 and π^nR=2R, so the ideal product with its conjugate is rational precisely when its exponent 2k is a multiple of n. Within 0≤k≤n these are the endpoints and k=n/2. At k=n/2 an explicit rational-norm generator is 1−ζ^(n/2), whose Hermitian norm is 2 and whose square is −2ζ^(n/2). This checks the positive half-depth case without appealing to a search for generators. By contrast, for an odd prime conductor or a non-dyadic composite conductor, no full rank ideal or higher rank module in the stated metric admits orthogonal integral coordinates at all.

## A uniform wide-Gaussian gap on any fixed nonorthogonal lattice

The obstruction persists approximately even when the integral basis is reselected for each width. Let Λ be a fixed D-dimensional lattice with D≥2, and assume it has no orthogonal integral basis. For a lattice basis (b_i) let (b_i*) be its Euclidean dual basis and define
```
ρ(B)= max_(i≠j) |⟨b_i*,b_j*⟩|/(‖b_i*‖‖b_j*‖).
```
There is a constant `ρ_* = inf_B ρ(B)>0`. To prove this, a sequence with ρ→0 would have its dual correlation Gram matrix tending to I. The product of squared dual lengths would tend to det(Λ*)², since that product times the correlation determinant is exactly the squared volume. Each length is bounded below by the positive dual minimum, so all lengths in the sequence would be bounded. A fixed lattice has finitely many vectors in a bounded set, giving a repeated orthogonal basis in the limit, a contradiction (orthogonality is equivalent for a basis and its dual).

For an optional explicit lower bound define the dual squared orthogonality defect `Δ=min_B ∏_i‖b_i*‖² / det(Λ*)² >1`. This minimum exists by the same bounded-vector argument and the strict inequality is Hadamard's inequality with its equality case. Gershgorin bounds the eigenvalues of the dual correlation matrix below by 1−(D−1)ρ(B). If this is positive its determinant, which is at most 1/Δ, is at least [1−(D−1)ρ(B)]^D; otherwise the following lower bound is automatic:
```
ρ_* ≥ [1−Δ^(−1/D)]/(D−1).
```
If all pairwise dual lattice inner products lie in J⁻¹ℤ, squared length products and determinants of dual Gram matrices lie in J^(−D)ℤ. Thus in the nonorthogonal case `Δ≥1+ J^(−D)/det(Λ*)²`. This applies for a rational Gram lattice in its normalization, and is only a possibly small positive bound, not one uniform over growing dimensions.

We claim that as s→∞ the distance between the coordinate distribution of D_(Λ,s,c) and any product law on ℤ^D obeys
```
TV ≥ e^(−1/π) ρ_* /(12π) − O_Λ(1/s),
```
uniformly in the center c and in the (possibly s-dependent) basis. For this, under the true law X∈Λ, the characteristic function of (X−c)/s tends to that of a spherical Gaussian with density proportional to exp(−π‖x‖²), uniformly on frequencies with norm at most two and uniformly in c. One may get the O_Λ(1/s) error by writing it as a normalized lattice Riemann sum: tile with translates of a fixed bounded cell of Λ/s and compare the numerator function exp(−π‖x‖²+i⟨w,x⟩) and denominator function exp(−π‖x‖²) to their cell-center values. The derivative is uniformly bounded by a polynomial times a fixed Gaussian envelope at ‖w‖≤2, so the total error is O(1/s); shifting the cells changes neither the diameter nor the uniform envelope comparison. The denominator integral is 1 with this convention.

Let i,j realize ρ(B), and normalize their dual basis directions to unit vectors u_i,u_j. The test phases exp(i⟨u_i,(X−c)/s⟩) and exp(i⟨u_j,(X−c)/s⟩) are separate functions of the respective integral coordinates, up to constants depending on c. Under any product law their covariance (using a product of the two phases, not a complex conjugate) vanishes. Under the spherical limit that covariance has absolute value
```
e^(−1/(2π)) · |e^(−⟨u_i,u_j⟩/(2π))−1|
≥ e^(−1/π) |⟨u_i,u_j⟩|/(2π).
```
The bound follows from the characteristic function exp(−‖w‖²/(4π)) and the mean-value theorem on [−1,1]. The approximation error is uniform in the directions by using frequencies of norm at most two, so this covariance bound minus O(1/s) also holds for the lattice law. If its TV to a product law is δ, the covariance absolute value is at most 6δ: each of the joint expectation and the two marginal differences costs at most 2δ when tested by a bounded phase. This proves the uniform gap.

Therefore high width alone cannot justify replacing a true spherical discrete Gaussian by an arbitrary product noise law on any integral basis of a fixed nonorthogonal lattice. The distance statement is about the **unwrapped lattice coordinates**. Reducing modulo a quotient or adding a hidden signal is a data processing step and may erase the gap. This result does not obstruct correlated Gaussian algorithms, a different covariance chosen to make a basis exact, or theoretical Ring-LWE reductions that do not make an independent-coordinate replacement.

[The exact checker](verify-cyclotomic-product-coordinates.js) audits toy signed-cycle root orders, the Hermitian Gram and middle-depth ramification identities in small dyadic examples, and mixed square-mass exponent identities. It contains no sampling or key-recovery routine.
