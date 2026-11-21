# A six-label orbit from a fixed seed must be terminal at large smooth centers

Fix an odd prime p and a finite set of primes F. For all sufficiently large even F-smooth N coprime to p (in particular for all sufficiently large powers of two), suppose the full prime-factor forward orbit from p has exactly six labels and all complementary rows are composite. Then **the orbit is itself a single terminal six-label exceptional autonomous component**; in particular p belongs to that component. Equivalently the nonterminal 2+4 case is impossible at these centers. No conclusion is asserted on existence of the terminal case, on larger orbits, or on Goldbach for all smooth centers.

Remove p from F if necessary. Work by contradiction on an infinite 2+4 sequence from the [six-label fork](PrimeOrbitSixLabelFork.md). Use p,q for the source unit cycle, r<s<R<J for its four terminal primes, and L=log N. We have N−p=q U, N−q=p V, with U,V entirely supported on the terminal primes and not equal to one. The primes r,s tend to infinity but have logarithmic weights zero (x has weight lim log x/L on a convergent subsequence); R,J have weights bounded below by a fixed positive number. Every input in the orbit is o(N). The four-by-four terminal exponent matrix M is invertible, while I−M has nullity one. These statements are all from the linked theorem, where they were shown with the weaker large smooth-part assumption.

## 1. The terminal cannot have two weight-one labels

The sign of a nonzero real vector f with Mf=f gives two disjoint mutual pairs. Namely f changes sign by irreducibility and Perron–Frobenius (the Perron eigenvalue is ≥2); each positive label has a positive successor, and likewise each negative label has a negative successor. Each sign group contains a directed cycle, requiring at least two labels. At four labels this gives two groups of exactly two and a 2-cycle on each. A mutual pair y,z satisfies N=y+z+h yz with an even h≥2: divide N−y−z by each coprime prime y,z, and note that the composite complements preclude h≤0. In particular yz<N.

Suppose both R,J have weight one. They cannot be mutual since RJ>N. Thus they have distinct small mutual parents, r and s; relabel the two big primes temporarily so R' is paired with r, J' with s. Write n_x=N−x. Then n_r=v R', n_s=w J', where v,w≥3 are N^{o(1)}. Their prime factors must be terminal small primes, excluding their own row's input. Hence v=s^β,w=r^α with α,β≥1.

For x=r,s, the two integers n_R' and n_x have gcd dividing
     
    v n_R'−(v−1)n_x = r+(v−1)x >0,

so the gcd is N^{o(1)}. Likewise n_J' has subpower gcd with each small row. Also gcd(n_r,n_s)≤s−r=N^{o(1)}. The remaining gcd gcd(n_R',n_J') divides the integer
     
    (w−1)v n_R' − (v−1)w n_J' = (w−1)r−(v−1)s.

If this last integer were nonzero on an infinite subsequence, all six pairs of complementary rows would have subpower gcd. As in the [macroscopic rank argument](PrimeOrbitMacroscopicRank.md), pass to limits P_{ij}=lim M_{ij}log x_j/L, W=diag(lim log x_j/L). P has nonnegative row sums one, and distinct rows have disjoint supports by the gcd bound. With four rows and four columns, P is a permutation matrix. The two big columns are assigned to the small rows because each big prime occurs in its own small parent row with weight one. The matrix P−W is invertible: if Px=Wx, any cycle of that permutation that meets a zero diagonal of W forces its x-values to vanish, and every cycle does meet one (no big-to-big permutation edge). But P−W is a limit of singular (M−I)diag(log x_j/L), a contradiction.

Consequently (w−1)r=(v−1)s for all sufficiently large members of this subsequence. Thus
     
    s^{β+1}−s = r^{α+1}−r,

and the even center s^{β+1}+r=r^{α+1}+s has a terminal two-label all-composite EAC on {r,s}. By [Bożek, Theorem 3.7](https://arxiv.org/abs/1909.09900), the only such center is 2200 with labels 3,13. This contradicts r→∞. We may therefore take subsequences on which R has a limiting weight strictly below one: R≤N^{1−δ} for some fixed δ>0 along each convergent weight subsequence.

## 2. Only one terminal prime can fit in a small cofactor

Let D=|det M|, v₀ the column of exponents in V, bᵀ=D v₀ᵀ M^{-1}, j=D−Σ b_i. Then b_i,j are integers. Entries of M,v₀ are O(L). Row-replacement determinants give D,|b_i|,|j|=O((1+L)^4). In the following identity indices i range over the terminal inputs x_i:
     
    D log p = j log N + D log(1−q/N) − Σ b_i log(1−x_i/N).             (1)

Indeed M(log x_i)_i=(log n_i)_i and pV=N−q. The four terminal primes and q are each ≤N/r, as proved in the fork. Hence |D log p−j log N|≪L^4/r.

Use the standard positive rational [Matveev bound](https://doi.org/10.1070/IM2000v064n06ABEH000314), e.g. [the precise positive-real multiplicative version, Theorem 2.1](https://doi.org/10.1007/s12188-025-00293-9): for fixed n, a nonzero sum of integer multiples (absolute coefficients ≤B) of logarithms of n positive rationals of log-heights h_i has log absolute value ≥−C_n(1+log B)∏max(1,h_i), up to an absolute additive constant. This follows from the multiplicative form by |exp z−1|≤3|z| for |z|≤1, with larger z immaterial. Expand log N over the fixed primes F. The form D log p−j log N cannot vanish since p∤N and D≥1. Its coefficients are O((1+L)^5), so r≤L^C for some fixed C.

For the second prime s, the terminal quotient by row(I−M) has dimension one, so the two standard classes of r,s are dependent. Choose a nonzero supported *integral row combination* on r,s with coefficients of absolute value O((1+L)^4) by the signed-minor construction in [the single-seed proof](PrimeOrbitMovingSeed.md). Squaring gives r^u s^v≡1 mod N with the same polynomial coefficient bound and (u,v)≠(0,0); this rational product is not equal to one. Pick ℓ∈F with v_ℓ(N)log ℓ≥L/|F|. The fixed-place rational p-adic logarithm estimate [Yu, in the formulation of Bugeaud, Theorem 1.3 first bound](https://arxiv.org/pdf/2209.00275) gives
     
    L ≪_F (log r)(log s)(1+log L).

For a one-term product use LTE as in the single-seed proof, yielding the same displayed bound; r,s are ℓ-units. In particular log s≫L/(log L)^2. Thus s exceeds exp((log L)^K) for every fixed K when N is large.

## 3. A gap among just two corrections

Only q and J in (1) can have nonnegligible ratio to N: the other terms r,s,R are ≤N^{1−δ'} on this subsequence. Put T₀=(log L)^2 and T_{i+1}=T_i^4 for i=0,1,2. Among the three disjoint intervals (T_i,T_{i+1}] at least one contains neither log(N/q) nor log(N/J). Write T=T_i there. Of q,J call a label y close if log(N/y)≤T, otherwise log(N/y)>T^4. All close cofactors used below are <exp(T)<s and T is bounded by a fixed power of log L. All nonclose corrections are O(exp(−T^4)); for r,s,R this holds since δ'L>T^4 eventually.

If q is close, U=(N−p)/q≥3 has only the terminal prime r available; write U=r^a₀. If J is close, J cannot be mutual with R as their product exceeds N. Its mutual partner is small and is its unique parent (two distinct inputs <J cannot have difference divisible by J). In its parent row J occurs with a cofactor <s, entirely on r, so the parent cannot itself be r. Therefore n_s=r^b₀ J with b₀≥1. In each case y=(N−z)/u with u the indicated power of r and z=p or s. Replacing log(1−y/N) by log(1−1/u) incurs an error
     
    log(1+z/((u−1)N))=O(N^{−1+o(1)}).

Let γ_q=1−r^{−a₀} if q is close and 1 otherwise; similarly γ_J=1−r^{−b₀} if J is close and 1 otherwise. The corrected form
     
    Λ = D log p − j log N −D log γ_q + b_J log γ_J

now has |Λ|≪(1+L)^4 exp(−T^4), absorbing the other smaller errors. The heights of the at most two nontrivial extra rational bases are ≤T, and all exponents after factoring N over F are O((1+L)^5). If Λ≠0, Matveev above gives log|Λ|≥−C_{p,F}(1+log L)(1+T)^2. Since T≥(log L)^2, this is incompatible with the upper bound for large L. Hence Λ=0 exactly. This finite gap argument makes no assumption on the speed at which r tends to infinity.

## 4. Exact-zero elimination

The equality is p^D γ_q^{−D} γ_J^{b_J}=N^j. Neither p nor N is divisible by the growing prime r. If just the q correction is present its r-valuation is Da₀>0; if only the J correction is present its r-valuation forces b_J=0. With no surviving correction the equality p^D=N^j is impossible. Thus both are present and Da₀=b_J b₀. Let g=gcd(a₀,b₀), x=r^g and a=a₀/g,b=b₀/g. The exponents a,b are positive and coprime. Raising the equality to b and cancelling equal powers of r gives
     
    Z^D = N^{jb},      Z = p^b (x^b−1)^a/(x^a−1)^b.

In particular the positive rational Z is an F-unit (every prime in its numerator and denominator belongs to F). This assertion does not require jb/D to be a rational integer. When F={2}, Z is in fact an integral or reciprocal integer power of 2.

If d=max(a,b)>2, the [Bang–Zsigmondy primitive divisor theorem](https://doi.org/10.1007/BF01692444) supplies a prime t of order d for x modulo t: its two classical exceptions are d=2 with x+1 a power of 2, and (x,d)=(2,6), neither applicable since x is odd and d>2. If a≠b the primitive prime cannot divide the other x-power minus one (the other exponent is strictly smaller). Since Z is an F-unit, the prime must be in F∪{p}. Therefore d≤max(F∪{p})−1, using d | t−1. If a=b then both equal one; if d≤2 the exponents are already bounded, including the x+1 power-of-two possibility. Thus after passage to a subsequence a,b are fixed.

Now Z/p^b=(1−x^{−b})^a/(1−x^{−a})^b=1+O_{a,b}(1/x) as x→∞, but Z≠p^b because Z is an F-unit and p∉F. The height of this rational Z is O_{p,a,b}(log x), so the exponents of the fixed primes in F in its numerator and denominator are O(log x). Applying the same fixed-base Matveev estimate to the nonzero log(Z/p^b) gives |log(Z/p^b)|≥(log x)^{-C}, contradicting O(1/x). In the dyadic case discreteness of {2^m:m∈ℤ} near p^b gives the contradiction without this last estimate (m is bounded since Z→p^b). This rules out the entire nonterminal branch at all sufficiently large F-smooth centers, as claimed.

**Comparison through November 21, 2026.** Bożek supplies the unconditional two-label classification, not the smooth-center six-label exclusion. [Kelanemer's terminal exponent-matrix preprint](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) was posted in August and revised in September. Its abstract is adjacent, but the full text was unavailable for comparison; no priority claim is made. The smooth-center restriction here is stronger than the large-smooth-part assumption of the linked six-label fork, while the conclusion excludes its entire nonterminal branch under that restriction.
