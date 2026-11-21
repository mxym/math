# The zero algebra occupies one torus translate, with injective short monomials

Assume the putative five-macroscopic near-smooth six-label sequence of [the one-pole theorem](PrimeOrbitSlowCurveOnePole.md). We use its varying geometrically irreducible curve C through the physical integers, of bounded degree and height o(L), L=log N, its slow-height relation transfer (§1 there), and its rational sole pole P at infinity. Fix the nonseed chart after subselection. The degree of T is d=den(w), and the orders of the X_j at P are −d w_j with 0<w_j<1. None vanishes on the fiber T=0. Write X₀=p, B=I−A, and B′ for its five moving columns. The fixed rank-four B′ has column space col(B), hence fixed two-dimensional left null space. Take an integral primitive generator v=(v₁,…,v₅) of its right kernel and put v₀=0. Statements below hold eventually; to disprove one asymptotic restriction would give an infinite countersequence, to which we apply the stated subselections.

**Conclusion.** For any *fixed* number field K the distinct affine geometric tuples (X₁,…,X₅) above T=0 form a single Gal(Qbar/K)-orbit eventually. This wording does not identify different branches over coincident affine tuples. With an appropriate fixed K, the entire special algebra, including its multiplicities, is an algebra K[Z,Z⁻¹]/(g(Z)^e) with a single irreducible polynomial g having nonzero constant term, e deg(g)=d and e≤4. Modulo T, the six coordinates are λ_j Z^(v_j), with λ₀=p and the other λ_j roots of unity times rational powers of p of bounded denominator. In particular

* the integer map u↦u·v is injective on **all** u∈Z^5_{≥0} with u·w<1, so the five v_j are nonzero and pairwise distinct;
* for each nonzero c in the left null space of B, max_{c_i≠0} v_i−min_{c_i≠0} v_i≥d;
* if u,u′ are distinct nonnegative exponent vectors with u·v=u′·v and max(u·w,u′·w)=1, their monomials satisfy X^u−ηX^(u′)=κT as an identity on C, with η a root of unity times a rational power of p, κ≠0.

Here g, its splitting field and the scalars can vary with the center. This is a structural restriction with unlimited seed arity, not a proof that every chart fails.

## 1. A split residue fiber would overconcentrate at a fixed prime

Enlarge the prescribed fixed field K to a fixed finite Galois extension if helpful; transitivity over a larger field implies transitivity over the original. The affine coordinate ring R=K[T,X₁,…,X₅] inside the function field of C is finite over K[T]: all the X_j have no poles over any finite T, so they are integral over the polynomial ring (the integral closure is the intersection of the valuation rings above its finite points). The extension has degree d and is regular over K; R is torsion-free of rank d, and thus free of rank d over the PID K[T]. In particular dim_K R/TR=d. This is valid for the possibly nonnormal affine ring.

Suppose the affine tuples of the zero fiber fall into at least two distinct K-Galois orbits infinitely often. Choose an integral linear form Y=∑t_j X_j simultaneously primitive for the degree-d extension over Qbar(T) and separating all distinct geometric affine zero-fiber tuples. A finite list of bounded coefficient vectors suffices: a bad choice lies on a hyperplane for each pair of distinct embeddings of the characteristic-zero function field or each pair of distinct zero tuples; the total number of such hyperplanes is bounded solely by d. An integer grid of side bigger than that number cannot be covered by them. Choose one form on a subsequence. Its minimal polynomial h(T,Z) is monic in Z, of degree d, in Q[T,Z] (no finite poles), and has bounded degree and coefficient height o(L) by the projection estimate in the one-pole proof; its leading coefficient as a polynomial in Z is the constant 1, so projective and affine coefficient sizes satisfy the same bound after normalization. The roots of h(0,Z) are exactly the Y-values of the geometric fiber, with multiplicity, by finite integral extension/lying-over (or the norm determinant of Y in the normalization). Thus over K there is a monic factorization

    h(0,Z)=A(Z)B(Z),   gcd(A,B)=1,    1≤deg A,deg B<d.

Pass to fixed degrees. The coefficient heights of A and B are o(L): all their roots have bounded degree and height o(L), from those of h(0,Z). For each *fixed* integer R₀, lift this factorization modulo T^R₀ to monic factors A*(T,Z),B*(T,Z) of the same Z-degrees, in K[T,Z], with T-degrees <R₀. At each new T-degree solve B·ΔA+A·ΔB=error with deg_Z ΔA<deg A, deg_Z ΔB<deg B; the Sylvester linear operator is invertible by coprimality. This finite recursion has coefficient heights o(L), and

    h−A*B*∈T^R₀ K[T,Z].

There is some ℓ∈F with log ℓ·v_ℓ(N)≥cL for fixed c>0 (since log N_F∼L); fix ℓ and one place ν of K above it. Use the extension of the ordinary ℓ-adic norm, with v_ν(ℓ)=1 before local/global normalization. All individual nonzero slow coefficients in K have absolute ν-valuation o(L), because K is fixed. Evaluating at T=N and y=Y(physical)∈Z gives

    v_ν(A*(N,y)B*(N,y)) ≥ R₀ v_ℓ(N)−o(L).

The same is true in the extended sense if the product is zero. The Z-resultant of A*,B* at N has valuation o(L): its constant term at T=0 is Res(A,B)≠0 of height o(L), and all terms with positive T-degree have valuation ≥v_ℓ(N)−o(L). A Sylvester Bézout identity for this resultant has coefficients of height o(L) before inserting N,y, so the two values cannot both have valuation larger than o(L). Each has valuation ≥−o(L) by integrality of N,y. One factor H*(T,Z) of fixed degree t<d therefore has

    v_ν(H*(N,y)) ≥ R₀ v_ℓ(N)−o(L).

Fix which of the two factors on a subsequence. No residue does or needs to lie in a predetermined splitting field.

For fixed J consider b=d(J+1) rational integer physical coordinates N^j y^i, for 0≤j≤J, 0≤i<d. They include 1,N^J; their heights are O_J(L) since |y|≤const·N. On every infinite subsequence their linear independence over slow moving coefficients (in the sense required by the moving Subspace Theorem) follows as in the one-pole proof: a nonzero such relation transfers by Bézout to the physical curve, impossible since 1,Y,…,Y^(d−1) are independent over Qbar(T). In particular y≠0 eventually (indeed a zero conflicts with the same transfer; the constant Y case would contradict primitivity unless d=1, in which case the fiber cannot split).

Take R₀>b+1. For a linear combination G of these monomials with K-coefficients, divide G(T,Z) by the monic H* in Z. Requiring the remainder to vanish mod T^k imposes at most tk linear scalar conditions, nested as k grows, all slow. Order the condition rows by T-degree and then by Z-degree. As in §3 of the one-pole proof, choose an independent basis of b linear combinations, the r-th of which satisfies the first r conditions, 0≤r<b. Gaussian elimination gives coefficients of height o(L), with one nonzero coefficient normalized to one. The division has bounded degrees/slow coefficients for fixed J. At the physical point the r-th form consequently has valuation ≥⌊r/t⌋v_ℓ(N)−o(L), including the contribution of the multiple of H*. This is a simultaneous basis with potentially different bounds, not one linear condition counted several times.

At ν use that basis; at every other place of K over F, and all archimedean places, use the coordinate basis. Compared to the coordinate basis at ν, the gain in the log-product bound is at least

    ([K_ν:Q_ℓ]/[K:Q]) log ℓ · [∑_{r=0}^{b−1}⌊r/t⌋−dJ(J+1)/2] v_ℓ(N) − O_J(L).

Here the O_J(L) from the i powers of y can in fact be bounded by O_d(J+1)L uniformly in J, since v_ν(y)≤O(L) for the nonzero integer |y|≤const N and ∑_{i,j}i=O_d(J+1). Equivalently, sum the displayed r-th bounds directly and keep baseline j costs only. The bracket is (d/2)(d/t−1)J²+O_d(J+1), positive quadratic. Over all the places in question the coordinate-basis log-product is at most O_d(J+1)L+o_J(L) since the N^j archimedean factors cancel against their F-parts and y is integral. As t<d and ℓ-mass ≥cL at this one fixed place, take J large then fixed. The total log-product is at most a strictly negative multiple of L. All physical coordinates are integers with one coordinate 1, so outside-S max norms are one; all form heights are o(L). The independent-system moving Subspace Theorem [Vojta, Thm 7.7](https://library.slmath.org/books/Book37/files/vojta.pdf), with nondegeneracy just checked, contradicts this as in the one-pole proof. This proves the claimed single affine Galois orbit.

## 2. One translate through the whole thickened fiber

All X_i are invertible near the fiber, including the seed p. For a row u in Z⁵ perpendicular to v, the fixed row lattice of B′ contains a positive multiple Du, and the multiplier and row combination for any fixed u can be chosen fixed. On C the row equations read

    (X₁,…,X₅)^(B′_i) = −p^(a_i−1_{i=0})/(1−T/X_i).

It follows that in the whole algebra R/TR the unit X^u satisfies (X^u)^D= ±p^k, k integral depending on the row combination and a. Choose ω∈Z⁵ with ω·v=1, put Z=X^ω (well-defined as a unit in the fiber ring), and apply this to the five fixed vectors e_j−v_jω. Enlarge the fixed field K once to contain all roots of the several fixed-degree equations W^D=±p^k as k varies, e.g. a field containing p^(1/D) and all 2D-th roots of unity for the lcm of the finitely many multipliers. By §1 all geometric affine tuples form a single K-Galois orbit. For each j there is therefore a *single* root λ_j∈K taken by X_j Z^(−v_j) at every geometric point of the fiber. Every other linear factor of W^D−(±p^k) is invertible in R/TR, since nonvanishing on all maximal ideals implies invertibility in this finite algebra. As the D roots in characteristic zero are simple, the identity upgrades to X_j=λ_j Z^(v_j) in R/TR itself, not merely its reduced quotient. Include j=0 with λ₀=p. Each λ_j is a root of unity times a rational power of p of bounded denominator.

The algebra R/TR is generated by the images of the X_j and hence is a quotient of K[Z,Z⁻¹]; conversely the monomial Z and its inverse exist there by invertibility. Its K-dimension d and unique geometric Galois orbit imply a presentation by one nonzero polynomial g(Z)^e with g monic irreducible over K, g(0)≠0 and e deg g=d. This is an affine scheme statement, not an assertion that the normalized curve has one analytic branch at each Z-root.

## 3. Two obstructions of different kinds

For equal-index monomials X^u,X^(u′), their images in R/TR have ratio η=λ^(u−u′). Thus X^u−ηX^(u′)=T·H for H∈R. If both weights are <1, H has no finite poles and vanishes at the unique point at infinity; it must vanish identically. The physical x^u/x^(u′) cannot be a fixed-field root of unity times a pure rational power of p for u≠u′: raising to a common bounded denominator and the root-of-unity order contradicts unique factorization at whichever of the five distinct nonseed primes has a nonzero exponent. This uses the actual η for that point and is valid even as its p-exponent varies. The case max weight=1 gives H constant, nonzero by the same reasoning. Applying strict injectivity to 1 and the five single X_j proves that all six indices v₀,…,v₅ are distinct.

For any integral c in the left kernel of B, the actual row identities give

    ∏_{i=0}^5(1−T/X_i)^(c_i) = (−1)^(∑c_i) = 1.

The last sign follows by first specializing at T=0, where all X_i≠0. Work locally at this fiber (so all denominators are units), expand modulo T², and cancel T in the function field before reducing modulo T. The resulting identity ∑ c_i/X_i=0 in R/TR is unchanged by the localization since its inverted elements are units in that algebra. Inserting §2 gives divisibility by g^e of the Laurent polynomial ∑ c_i λ_i^−1 Z^(−v_i). For c≠0 the terms have distinct exponents, hence no cancellation, and clearing its lowest exponent yields a polynomial of degree exactly max_{supp c} v_i−min_{supp c} v_i. The divisor has degree d and nonzero constant, proving the span bound. This extends to rational c by clearing denominators.

At any nonzero root z₀ of g, every such polynomial vanishes to multiplicity at least e. Applying the Euler derivative (Z d/dZ)^r for 0≤r<e shows that each of the vectors (λ_i^−1 z₀^(−v_i)(−v_i)^r)_i annihilates the whole left kernel of B. They lie in a space of dimension rank(B)=4. If e≥5 the first five are linearly independent by the Vandermonde determinant on five of the six distinct indices. This contradiction proves e≤4. In particular a residual field of unboundedly varying arithmetic type is a genuine outstanding possibility; treating Z as a rational number without proof is not valid.

## Comparison

The underlying factor closure is that of [Bożek](https://arxiv.org/abs/1909.09900). For the nearby [Kelanemer August preprint, revised September 6](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460), see the comparison and access limitation in the [one-pole note](PrimeOrbitSlowCurveOnePole.md). The November 21 search gives no priority or comprehensive nonoverlap claim. No deduction here relies on any claimed proof of binary Goldbach.
