# Prime-pool bounds for high-degree identities with a separated monomial

In the [bounded-input factor-output experiment](FactorBoundedInputShadow.md), the degree bound on a polynomial identity need not follow from its description length: a binary exponent may already give exponential degree. We prove the same sharp factor-output probability curve for a different and partly disjoint class of probes. Its complexity parameter is a *truncated divisor mass* of an integer spacing between two grades of its monomials, not the total degree.

This is a negative result about a specified abstract observation model. It neither computes factors of conventional integer inputs nor gives an unconditional lower bound for doing so.

## General prime-pool summation lemma

Take the input model, frozen arithmetic shadow and prime-pool success baseline A(K) from the linked note. There are M distinct primes, a uniform pair without replacement, uniform independent hidden vectors at the two primes, and at most K=2^b shadow leaves after fixing the observer's coins. Only a global zero bit is returned per arithmetic probe. The auxiliary binary predicates of N can be freely chosen and interleaved. For a fixed polynomial f on a frozen path and prime ℓ in the pool let a_ℓ(f) be its local zero probability under the uniform vector at ℓ. The entire hidden vector may be reused across probes. Suppose the nonzero integer polynomial at position i on any shadow path satisfies Σ_ℓ a_ℓ(f)≤L_i (constant nonzero padding is allowed). Then, without any restriction on formal degree,
```
success ≤ A(K) + K/[M(M−1)] Σ_i L_i².
```
Indeed, for any fixed candidate path and test, the unconditional joint probability that a uniform pair's two local values vanish equals
```
[(Σ_ℓ a_ℓ)²−Σ_ℓ a_ℓ²]/[M(M−1)].
```
Discard the condition that it is the path selected by the input pair, and sum this upper bound over ≤K paths and all positions. This is legitimate because on the shadow path the test selection is frozen independently of the hidden vector once the pair and coins are given; we union over all possible frozen choices. A successful run either guesses correctly on the shadow or departs from it. The baseline bounds the former. When K≤M the relative increment over the exact attainable baseline is at most Σ_i L_i²/(M−1), since A(K)≥K/M. For K≥M−1 the baseline already equals one. This lemma can be replaced by its version retaining the subtracted square sum if an exact pool is known.

## Two-grade identity

Use an integer P≥2 and any pool S of M primes in [P,2P). Terms of f are first combined to distinct exponent vectors and zero coefficients dropped. Assume there is a nonzero coefficient A at an exponent u_* and an integer vector v with gcd(v_1,…,v_m)=1 such that
```
v·u = c for every other term,   v·u_* = c+g,   g≠0.
```
The integer c need not be nonnegative. A monomial alone may be handled separately. Let h be the number of distinct variables actually appearing in f, let s be the number of candidate primes dividing **A** (not merely dividing the coefficient content), and let
```
W_P(g)= Σ_{j | |g|,  1≤j<2P} φ(j)/j.
```
Then a valid bound on the summed local root probabilities is
```
Σ_(ℓ∈S) a_ℓ(f) ≤ s + h M/P + [3P/(P−1)] W_P(g).
```
The h M/P term may be omitted if the hidden entries are sampled uniformly from the multiplicative tori at both primes instead of from the additive Cartesian spaces. For a single nonzero monomial, the first two terms alone suffice.

To see this, on the torus (F_ℓ^×)^m use the one-parameter subgroup t↦(t^v_1,…,t^v_m). Primitivity of v gives integers t_j with Σt_j v_j=1, hence the parameterization is injective for every ℓ, and each coset has ℓ−1 points. At a fixed coset representative the restriction of f is t^c(C t^g+D) with C nonzero if ℓ does not divide A. It has either zero or gcd(|g|,ℓ−1) torus roots by cyclicity, including the case D=0, which has none. Points outside the torus in the h relevant variables have probability at most h/ℓ; alternatively condition on these h nonzero and average over the remaining, unused, uniform nonzero coordinates. The latter step uses that the polynomial does not see unused coordinates, so its probability on those lifts is identical to a full torus average even if the displayed grading involves them. Exceptional coefficient primes have probability at most one apiece.

Finally gcd(|g|,ℓ−1)=Σ_{j|g, j|ℓ−1} φ(j). For j<2P the interval [P,2P) has at most P/j+1≤3P/j integers congruent to 1 modulo j. Since 1/(ℓ−1)≤1/(P−1), summing the fraction of torus roots gives the displayed bound. This argument requires no equidistribution of primes in those residue classes.

## Exponential-degree consequence

For the pool of all n-bit primes choose P=2^(n−1), so M∼P/log P. Suppose the number of probes, their variable counts and bit lengths of the selected coefficients A are polynomial in n. If each grading gap has O(n) bits with a uniform constant, then W_P(g)≤τ(|g|)=P^o(1) uniformly. One elementary proof is that for every ε>0 there is a constant C_ε such that τ(m)≤C_ε m^ε: for primes ℓ≥2^(1/ε) bound a+1≤2^a≤ℓ^(ε a); absorb the finite suprema sup_a (a+1)/ℓ^(ε a) for smaller primes into C_ε. The number s is at most log|A|/log P, interpreted as zero for |A|=1. Thus all L_i≤P^o(1), and the full Σ_i L_i²/M tends to zero. The optimal success of the restricted experiment is consequently (1+o(1)) A(2^b), **uniformly even when b=0**. These identities can have exponential total degree. More generally only Σ_i L_i²=o(M) is required; if g is a power of two then W_P(g)=O(log P), no matter how large the exponent of that power is.

Examples of the supported family:
* Two distinct monomials: choose a coordinate where their exponents differ and take v to be the corresponding coordinate vector. In the genuine multivariate-binomial case the exact torus kernel fraction is gcd(ℓ−1,all exponent differences)/(ℓ−1); the grading bound suffices even without this refinement.
* Any bivariate trinomial with **noncollinear** exponents: use the primitive perpendicular to the line joining two exponents. If all coordinates are ≤E, its height gap has magnitude ≤2E², so exponents of O(n) bits give a gap of O(n) bits. Collinear trinomials do not follow from this argument.
* Many terms may share the single grade of the nonexceptional monomials. Neither their degrees within that grade nor their coefficients affect the torus bound beyond their possible effect on the number of relevant variables.

There is no conclusion for general short circuits, arbitrary dense polynomials, arbitrary univariate trinomials, local CRT indicators, or ordinary unrestricted integer encodings. This merely extends the previously established restricted-model success barrier to a concrete family that a low formal degree assumption does not cover. [Kelley's finite-field sparse-polynomial work](https://doi.org/10.1112/S1461157016000334) gives related bounds on nonzero roots in a given field in terms of sparsity and cosets. The cyclic-group root count, divisor identity, and geometric orbit argument are standard ingredients; no general sparse-root novelty is claimed. For distinct broader oracle and generic-ring contexts see [Maurer](https://crypto.ethz.ch/publications/Maurer96.html) and [Aggarwal–Maurer](https://crypto.ethz.ch/publications/AggMau09.html).

The [toy checker](verify-factor-graded-prime-pool.js) exhaustively counts roots for generated two-variable polynomials over small prime pools, including positive and negative grading gaps, one-sided exceptional coefficients and high exponents; it compares both field and aggregate bounds by exact integer arithmetic.
