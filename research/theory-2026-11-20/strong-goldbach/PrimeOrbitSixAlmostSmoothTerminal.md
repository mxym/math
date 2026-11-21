# A six-label fixed-seed orbit is terminal even with a growing unrestricted cofactor

Fix a finite set F of primes, an odd prime p, and 0<η<1/4. Write N=N_F V, where N_F is the full F-part. For all sufficiently large even N coprime to p with

    log V ≤ (log N)^(1/4−η),

every six-label all-composite forward factor orbit from p is a single terminal strongly connected component. The primes dividing V need not be bounded, and V need not be a perfect power. This excludes the whole nonterminal 2+4 alternative on the stated larger class; in contrast to the [fixed-smooth theorem](PrimeOrbitSixSmoothExclusion.md), **it does not exclude a terminal six-label component** here. Neither result gives a general Goldbach representation.

## The two relevant corrections

Let L=log N and K=(1+log V)(1+log L). Thus K≥1+log L and K⁴=o(L). Assume an unbounded countersequence, discarding p from F. The [six-label fork](PrimeOrbitSixLabelFork.md) applies because N_F≥N^(1/2+δ) for some fixed δ>0. In its 2+4 alternative write p,q for the source pair and r<s<R<J for the terminal primes. The four-by-four exponent matrix M of the terminal rows is invertible, I−M has nullity one, r,s→∞ are subpower, R,J have positive limiting weights, and all four terminal labels as well as q are ≤N/r. We always pass to weight-convergent subsequences. [Section 1 of the terminal proof](PrimeOrbitSixSmoothTerminal.md) uses no smoothness beyond these fork facts: its disjoint-support permutation contradiction or the auxiliary two-label Bożek component rules out both R,J having weight one. In particular R≤N^(1−δ') along this subsequence for some δ'>0. Only q and J can be within a subpower factor of N.

As in §2 of that proof, N−q=p times a monomial in the four terminal primes. Multiplying its exponent row by D M^(-1), D=|det M|, gives integral coefficients b_i, and j=D−Σ b_i, with D, |b_i|, |j|≪(1+L)^4. The exact identity is

    D log p−j log N = D log(1−q/N) − Σ_i b_i log(1−x_i/N).              (1)

Its nonzero left side has magnitude O((1+L)^4/r). Expand log N over F and, if V>1, the *one* rational base V, not its individual factors. Matveev's positive-rational logarithm lower bound [original paper](https://doi.org/10.1070/IM2000v064n06ABEH000314), e.g. [Theorem 2.1 in multiplicative form](https://doi.org/10.1007/s12188-025-00293-9), bounds its log absolute value below by −C K: the fixed-base coefficients and the V coefficient are polynomial in L. It follows log r≪K. The one-dimensional cokernel of I−M gives the nonzero supported relation r^u s^v≡1 mod N with (u,v)≠(0,0) and |u|,|v|≪(1+L)^4 in §2 of the linked proof. At an ℓ∈F with v_ℓ(N) log ℓ≫_F L (available since log V=o(L)), [Yu's bound in Bugeaud, Theorem 1.3](https://arxiv.org/pdf/2209.00275), or LTE for a single base, gives

    log s ≫_{p,F} L/[K(1+log L)].

In particular log s exceeds every fixed multiple of K², since K³(1+log L)≤K⁴=o(L).

Order t_y=log(N/y) for the two labels y=q,J as t₁≤t₂. Whenever one is declared close below, t_y≤C K². Its cofactor is <exp(t_y)<s. For q this gives N−p=r^α q. For J, its mutual partner cannot be R since both have positive weights and t_J=O(K²)=o(L), whence RJ>N. The partner is small; its row containing J has cofactor ≥3 and <s, so the cofactor is a positive power r^β. The partner must be s rather than r since r∤N. These claims use only the two mutual pairs from §1 of the linked proof. For either close y=(N−z)/u with z=p or s, u≥3 the appropriate power of r, replace log(1−y/N) by log γ_y with γ_y=1−1/u. Its logarithmic height is ≤t_y and the error log(1+z/((u−1)N)) is O(N^(−1+o(1))). For nonclose labels put γ_y=1, and the unmodeled error is O(exp(−t_y)) since q,J≤N/r and r→∞.

We now force the exact equality

    D log p−j log N−D log γ_q+b_J log γ_J=0.                            (2)

For any selected corrections Matveev bounds the log absolute value of a *nonzero* left side by at least −C K∏close(1+t_y), with the same kind of constants as above; extra bases are the at most two specified rationals of heights ≤t_y. The error from (1) is bounded by O((1+L)^4) times the sum of exp(−t_y) over unmodeled labels and exp(−δ''L) for some fixed δ''>0, after including r,s,R and the modeled correction errors. Choose a fixed C₁ larger than the no-correction lower-bound constant plus, say, 10 to absorb the logarithm of the polynomial error. If t₁>C₁K no correction is needed. Otherwise model the first correction. If t₂>C₂K² for a fixed C₂ larger than its O(K²) lower-bound constant plus 10, no second correction is needed. Otherwise model both. In this last case the lower-bound cost is O(K⁴)=o(L), whereas only exp(−δ''L) errors remain. In every case (1) contradicts the relevant nonzero lower bound for large L, proving (2).

## A divisibility argument that needs no smoothness of N

If neither correction survives in (2), p^D=N^j contradicts D≥1 and (p,N)=1. The valuation at r forces both corrections to occur with Dα=b_J β (otherwise the only possible J coefficient is zero, returning to the same contradiction). Set g=gcd(α,β), x=r^g→∞ odd, a=α/g, b=β/g. Cancelling powers of r in (2) gives

    Z^D=N^(jb),              Z=p^b (x^b−1)^a/(x^a−1)^b,    gcd(a,b)=1.     (3)

Crucially the positive rational Z is either an integer or the reciprocal of an integer, regardless of the primes in N. We show (3) impossible along x→∞. Put E_m=(x^m−1)/(x−1). Then gcd(E_a,E_b)=1, since gcd(x^a−1,x^b−1)=x−1.

If Z is integral and b≥a, then E_a^b divides p^b E_b^a, so E_a divides p. This forces a=1 for large x. Now (x−1)^(b−1) divides p^b E_b. The part of E_b supported on primes dividing x−1 divides b(x+1): at odd primes use LTE, while at 2 its valuation is 0 for odd b and v₂(x+1)+v₂(b)−1 for even b. Hence (x−1)^(b−1)≤p^b b(x+1). If b≥3 this bounds x uniformly since (x−1)^(b−2)≤2 p^b b for x≥3, and (2p^b b)^(1/(b−2)) is bounded over b≥3. Thus b is bounded.

If Z is integral and a>b, when a>2 the [Bang–Zsigmondy theorem](https://doi.org/10.1007/BF01692444) supplies a prime of order a for x. It divides x^a−1 and not x^b−1, so integrality forces it to equal p, hence a≤p−1. The possible exponent-two exception is already bounded; the exponent-six/base-two exception is irrelevant for odd x. Thus again both exponents are bounded.

Finally, if Z<1 and 1/Z is an integer, then a>b: if a≤b, (1−x^(−b))^a≥(1−x^(−a))^b and Z≥p^b. The expression for 1/Z and gcd(E_a,E_b)=1 give E_b^a|E_a^b, so b=1. Now (x−1)^(a−1) divides E_a, and the same LTE estimate gives (x−1)^(a−1)≤a(x+1), bounding a for x→∞.

Pass to fixed a,b. Since Z→p^b>1 and is an integer or reciprocal integer, Z=p^b eventually. This contradicts (3) by coprimality of p and N, proving the claimed nonterminal exclusion. The preceding integrality step is valid for arbitrary integer N>1; the growing-cofactor bound was only used to reach (2).

**Dated comparison.** [Kelanemer, August 12, revised September 6, 2026](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) studies related exponent matrices. The landing and delivery endpoints did not provide the full manuscript. Unlike the existing fixed-smooth exclusion, this statement controls only the nonterminal branch but allows an unrestricted cofactor in the displayed size range. No priority or Goldbach-proof claim is made.
