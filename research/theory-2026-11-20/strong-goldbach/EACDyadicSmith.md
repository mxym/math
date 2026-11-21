# A dyadic divisor forces either large Smith torsion or recurrent modes

Let C be a nontrivial [Bożek exceptional autonomous component](https://arxiv.org/abs/1909.09900) at even N. Orient arcs from p to the prime factors of N−p. The k labels are distinct odd primes coprime to N, every row is composite and all its prime factors lie in C. Put A_{ij}=v_{p_j}(N−p_i), B=I−A, D=max_i Ω(N−p_i), m=min C. All diagonal entries of A are zero. Let 2^a | N, a≥2.

**Computable dichotomy.** If B is nonsingular, its largest Smith invariant e obeys
     
    2^{v₂(e)} ≥ 2^a/(m+1) > 2^a/(√N+1),
    2^{v₂(e)} ≤ |det B| ≤ (1+D²)^{k/2}.

At N=2^a this implies k≥2 log(N/(√N+1))/log(1+D²), or else 1 is a rational eigenvalue of A. In particular along such centers with k=o(log N/loglog N) the latter alternative is forced regardless of row multiplicities, since D≤log N/log 3. The same test applies when N is not a power of two; it is only useful numerically when its dyadic divisor is large enough. If the rational eigenvalue occurs, the directed graph actually contains two vertex-disjoint directed cycles. This is a necessary condition, not exclusion of the singular case or a Goldbach proof. The known 128 example is singular.

**Proof.** Map the j-th free generator of the additive group ℤ^k to the residue p_j in the multiplicative quotient (ℤ/2^aℤ)^×/{±1}. Every row of B maps to 1 since the product in the i-th row of A is N−p_i≡−p_i modulo 2^a. The map descends through the quotient by the *integral row lattice* of B. If B is nonsingular its exponent is exactly its last Smith invariant e, so p^e≡±1 modulo 2^a for each label p.

If e is odd, v₂(p^e−1)=v₂(p−1) and v₂(p^e+1)=v₂(p+1) by the geometric quotient, which is odd in each case. If e is even, p^e≡1 modulo 4, so the negative sign is impossible for a≥2. Factoring by differences of squares gives
     
    v₂(p^e−1)=v₂(p−1)+v₂(p+1)+v₂(e)−1
              =max(v₂(p−1),v₂(p+1))+v₂(e),

since one of p−1 and p+1 is exactly 2 modulo 4. Thus always 2^a≤(p+1)2^{v₂(e)}. Apply this at m. A prime divisor of smallest size of any composite row is ≤√(N−p_i)<√N; it belongs to C, proving m<√N. The last Smith invariant divides |det B|. Hadamard gives the stated upper bound since row norms of B are ≤√(1+D²).

If B is singular, choose a nonzero real f with Af=f. If f is nonnegative then a zero at any label propagates to all successors and hence throughout the SCC; if strictly positive, at its minimum a row of total multiplicity ≥2 gives (Af)_i≥2 min f>f_i. The same rules out nonpositive f. Wherever f_i>0 there is a successor with positive f, so the finite positive support contains a directed cycle. The same holds on the disjoint negative support. This argument uses strong connectivity for the sign-change conclusion, not just closure of a union of forward paths.

The [2026 terminal-island record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) also uses exponent matrices under global counterexample hypotheses. The latest complete text was not accessible; this deduction instead uses the finite abelian group of an actual local component and makes no claim of priority. For an extension treating specified generators even in the singular case, see [the forward-orbit rank test](PrimeOrbitDyadicRank.md).
