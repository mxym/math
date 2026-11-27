# A sharp one-sided norm and unbounded two-sided distortion for cyclotomic codifferents

In standard Ring-LWE formulations the secret module can be the codifferent. Multiplication by a generator of the different identifies that lattice exactly with the ring of integers, but changes the canonical Gaussian widths coordinate by coordinate. [Lyubashevsky–Peikert–Regev, §3.3](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf) and [Peikert, dual and non-dual forms](https://eprint.iacr.org/2016/351.pdf) explain this distinction; [LPR's toolkit](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf) gives the standard cyclotomic generators. Here the question is whether choosing a *different unit multiple* can remove the distortion without changing the lattice map. The answers below concern abstract lattice geometry, not the security of an instantiation, and do not apply to arbitrary transformations of samples. The [log-unit lattice analysis of Cramer et al.](https://web.eecs.umich.edu/~cpeikert/pubs/logunit.pdf) studies shortest generators of arbitrary principal ideals; the specific uniform lower bound and exact optimizer here use an integral Fourier constraint of the ramified prime in the cyclotomic different.

## Results

Let K be a cyclotomic field of normalized conductor m, R its ring of integers, and D its different, so R∨=D^{-1}. Give K⊗R its canonical Euclidean norm. For any R-module lattice isomorphism R∨→R, the map is multiplication by a generator γ of D, and its singular values are |σ(γ)| with the usual embedding multiplicities. This follows from extending the map to rank one over K; each complex embedding acts as scalar multiplication on a real plane. A field automorphism before multiplication does not alter the range of singular values.

1. There is a similarity, meaning condition number exactly one, if and only if the only primes in m are 2 and 3.
2. For every odd prime p and every a≥1, put m=p^a, ζ=ζ_m, ξ=ζ_p and J=(1-ξ)R. The choices of γ correspond exactly to generators α=m/γ of J. Set G=p^{1/(p-1)}, the common geometric mean of the embedding magnitudes of α, and define

       A=max_σ |σ(α)|/G,       B=G/min_σ |σ(α)|.

   Both are at least one, and AB is the condition number of either multiplication. The smallest possible max_σ |σ(α)| is exactly 2 cos(π/(2p)). Its minimizers are precisely root-of-unity multiples of conjugates of 1-ξ. Indeed, **every** generator with max_σ |σ(α)|≤2 is of this form and has condition number 1/(2 sin(π/(2p))). Any other generator has max_σ |σ(α)|≥2 sqrt(p/(p-1)).
3. For every such generator, with absolute constants independent of a,

       log(p-1) ≤ 3 A² log(1+2π sqrt(3) A² B).

   Consequently the infimum condition number over all lattice isomorphisms is Ω(sqrt(log p/log log p)), uniformly over a as p→∞. The standard generator gives O(p); the optimal order between these bounds is open here. More precisely, if A≤C for any fixed C, then B grows at least as a positive power of p, with constants depending only on C. The growth of AB does not on its own assert unbounded inflation in either prescribed direction alone.

The volume-normalized maximum width expansion of γ is B; that of the inverse map is A. Thus there is a genuine two-way tradeoff, stronger than observing that the standard generator happens to be anisotropic.

## Similarities for arbitrary conductors

Write p^a||m and e_p=φ(p^a). At every prime P|p the p-primary exponent in D is

       d_p = e_p (a - 1/(p-1)).

For p prime-power conductor this follows by differentiating
Φ_{p^a}(x)=(x^{p^a}-1)/(x^{p^{a-1}}-1) at ζ_{p^a}; adjoining the roots of prime-to-p order locally is an unramified base change, leaving the different exponent unchanged. Equivalently use the product formula for the cyclotomic different in the LPR toolkit. A multiplier is a similarity precisely when all |σ(γ)|² coincide. Since cyclotomic conjugation commutes with embeddings, then γγ̄ is a rational element (all conjugates coincide). Its P-adic valuation is 2d_p, so e_p must divide 2d_p. In turn p-1 must divide 2. If the conductor only involves 2 and 3, its different really does have an equal-modulus generator: the 2-power factor is rational, and the 3-power factor is rational times (1-ζ_3)^{-1}. The two factors may be multiplied by the unramified base-change calculation. Each has constant embedding magnitude. The field Q gives the trivial case.

This is an exact statement for lattice isomorphisms, not for all torus maps. In the p^a case, multiplication by the rational integer m maps R∨ into R with image J. It has condition number one and torus covering degree [R:J]=p^{p^{a-1}}. On residues modulo q it induces an isomorphism if and only if p∤q: Smith normal form shows the inclusion J→R is invertible after reducing modulo q precisely when its index is coprime to q. Relative to the same-volume lattice isomorphism benchmark, its scalar width inflation equals G. This type of covering map is already allowed in Peikert's general syntactic conversion; it does not contradict the exact-lattice lower bound.

## Integral Fourier proof

Since Φ_{p^a}'(ζ) is a unit times m/(1-ξ), α=m/γ ranges exactly over generators of J. Set h=p^{a-1}. The m powers of ζ are grouped into h blocks of p powers:

       α = sum_{j=0}^{h-1} ζ^j sum_{k=0}^{p-1} c_{j,k} ξ^k,
       c_{j,k} ∈ Z.

The ring R is free over Z[ξ] with basis (1, ζ,...,ζ^{h-1}); this follows by grouping a monomial basis with deg Φ_{p^a}=h(p-1). The kernel in each length-p coefficient block is precisely the constant coefficient vector, because Φ_p=1+x+...+x^{p-1}. An element lies in J exactly when each block's sum is divisible by p, since Z[ξ]/(1-ξ)=F_p. For α in J choose the unique integral representative with each block summing to zero by subtracting the block mean.

Let E=sum_{j,k} c_{j,k}², L=sum |c_{j,k}|, and s be the number of nonzero coefficients. Thus s≤L≤E and E is even (squares and integers coincide mod 2). On primitive m-th roots, Parseval gives the exact identity

       (1/φ(m)) sum_σ |σ(α)|² = (p/(p-1)) E.

Indeed the all-root Fourier sum is m E, and the nonprimitive roots are exactly the h-th roots: at each of them the k-dependent phases are one, so the Fourier value is zero by the block-sum condition. Nonzero α has E≥2. If E=2, its only coefficients are a +1 and a -1 in the same block, so α=ζ^j(ξ^k-ξ^l) with k≠l, precisely the stated root-of-unity multiples of conjugates. The maxima and minima of their absolute embedding values are 2 cos(π/(2p)) and 2 sin(π/p) respectively. If E≥4, its max is at least 2 sqrt(p/(p-1)), which is already greater than 2. This proves the exact optimizer and gap.

To prove the two-sided bound, list the nonzero monomial indices of this representative as v_1,...,v_s modulo m. Put K0=floor((p-1)^(1/(s-1))); equivalently choose the largest positive integer with K0^(s-1)≤p-1, avoiding floating precision. Partition the (s-1)-dimensional unit cube into K0^(s-1) equal boxes. The p vectors

       ((b(v_j-v_1)/m) mod 1)_{j=2}^s,     b=0,...,p-1,

give two in the same box. Their difference produces an embedding indexed by a nonzero residue b-b' with magnitude less than p, hence coprime to p^a. After removing the common phase ζ^{(b-b')v_1}, every remaining phase is within Euclidean distance 2π/K0 of 1. Since the total coefficient sum is zero, the triangle inequality for phase differences gives

       min_σ |σ(α)| ≤ 2π L/K0.

This uses only p vectors, independent of the depth of the cyclotomic extension. Since p-1<(K0+1)^(s-1), with min_σ |σ(α)|=G/B the preceding estimate implies

       log(p-1) ≤ (s-1) log(1+2π L B/G).

Parseval gives E≤((p-1)/p)G² A². Since 1≤G≤sqrt(3), substituting L,s≤E proves the displayed bound. As A≤AB and A²B≤(AB)², it implies κ² log(1+Cκ²) ≥ c log p for the condition number κ=AB. Holding A bounded instead forces B≥c_C (p-1)^{1/(3C²)}-c'_C. No part of this argument requires the cyclotomic units to be the full unit group, a regulator estimate, or a class-number conjecture.

## Scope and checking

The orthogonality of the canonical embedding planes does not make the exact integral module conversion a similarity, and a near-minimizer in one direction can be very poor in the other. These are statements about singular values of a fixed class of maps, irrespective of samples or computational attacks. They do not prove a bound on general procedures or on arbitrary fractional ideals.

The adjacent checker verifies the exact zero-block Parseval identity by Ramanujan sums, the coprime direction in the pigeonhole lemma with integer arithmetic, and the valuation divisibility for generated small cases (72,491 checks). It also reports 92 floating illustrations of the root-sibling extremum (not used in the proof).
