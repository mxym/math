# Ambiguity of the Carmichael value on balanced semiprimes

The Carmichael value below is treated as a statistic of a random balanced semiprime. This is a counting and entropy theorem, not a method to compute the statistic, reconstruct the integer, or produce any factor efficiently.

## Statement

Let P=2^(n−1), let S contain all primes in [P,2P), and choose an unordered pair of distinct primes p,q uniformly from S. Put N=pq and Λ=lcm(p−1,q−1), the Carmichael value of N. Write C=binomial(|S|,2), and let F(ell) be the number of balanced semiprime products in this same pool having value ell. With all entropies in nats, unconditionally as n grows:
```
E F(Λ) = O(n²);
Pr[Λ = Λ'] = O(n²/C) for an independent copy Λ';
H(N | Λ) ≤ 2 ln(2) · ln n + O(1);
F(Λ) ≤ n^(2 ln 2 + o(1)) with probability 1−o(1).
```
In particular the collision entropy of Λ is at least ln C−2 ln n−O(1), and the number of distinct values on this balanced family is at least a constant times C/n^(2 ln 2). These are upper bounds on ambiguity, not assertions that a typical fiber is a singleton or that its entropy has this exact asymptotic.

We use the prime number theorem, the classical [Brun–Titchmarsh inequality](https://doi.org/10.1112/S0025579300004708), and, for the sharper Shannon and typical statements, [Bombieri–Vinogradov](https://doi.org/10.1112/S0025579300005313). No distribution result about large prime factors of the predecessor is required.

## Arithmetic fiber bound: keep track of the true gcd

Write a=p−1, b=q−1, k=gcd(a,b), and ell=lcm(a,b). For another pair of shifted factors in the balanced pool with the same ell, write its gcd as d. The identity product = gcd times lcm and the interval [P,2P) imply
```
d ≤ 4k,   d | ell.
```
Indeed every shifted prime in the pool is between P and 2P, since P is even. For fixed d, after removing that common gcd the ordered coprime factors have product ell/d. Each prime-power component is assigned wholly to one of the two factors, so there are exactly 2^ω(ell/d) possibilities before enforcing balance, primality and distinctness. Thus, counting ordered choices as an upper bound,
```
F(ell) ≤ Σ_(d≤4k, d|ell) 2^ω(ell/d) ≤ 4k·2^ω(ell).
```
An independent bound valid for every ell is F(ell)≤τ(ell²): at a prime-power component r^e of ell, the pair of exponents can be any two numbers in [0,e] whose maximum is e, exactly 2e+1 choices. In particular F(ell)≤P^o(1) uniformly for ell≤4P², by the standard bound τ(m)≪_ε m^ε for every ε>0. For completeness, that bound follows from the product of local factors a+1, applying a+1≤2^a≤r^(ε a) for large primes r and absorbing the finite per-prime suprema at small primes.

## Mean fiber bound

In the following computations let a=p−1 for p uniform in S. Write m_d=Pr[d|a]. The prime number theorem gives |S| ∼ P/ln P. The Brun–Titchmarsh estimate yields m_d≪_c 1/φ(d) for d≤P^c, any fixed c<1, and trivial counting gives
```
m_d ≪ (ln P)/d   for d≤2P,
```
with m_d=0 for d>2P. To use independent copies a,b below and then condition on their parent primes being distinct costs at most a factor |S|/(|S|−1).

A useful weighted bound is, for any T≤P^(1/4),
```
E[τ(a) · 1_(T|a)] ≪ (ln P) τ(T)/φ(T).
```
Pairing divisors above and below the square root bounds τ(a) by twice the number of divisors r≤sqrt(2P). Joint divisibility by T and r requires their lcm, at most sqrt(2)P^(3/4), so Brun–Titchmarsh bounds the corresponding probability by a constant times 1/φ(lcm(T,r)). Put c=gcd(T,r) and s=r/c; then lcm(T,r)=Ts. Since φ(Ts)≥φ(T)φ(s), summing over c|T and s≤sqrt(2P) proves the display using
```
Σ_(s≤x) 1/φ(s) ≪ ln(2x).
```
One elementary verification of this last estimate expands s/φ(s)=Σ_(e|s) μ²(e)/φ(e) and uses convergence of Σ_e μ²(e)/(eφ(e)), whose Euler factors are 1+1/[r(r−1)] for primes r. Similarly
```
Σ_(s≤x) τ(s)/φ(s) ≪ (ln(2x))²
```
by writing s as a product of two factors and using the same inequality for φ. All estimates bound averages over shifted primes via classical upper bounds; no higher-order Titchmarsh asymptotic is needed.

First treat true gcd k≤P^(1/10). The condition d|ell=lcm(a,b) allows its prime-power components to be partitioned into a coprime d_1,d_2 with d_1d_2=d, d_1|a, d_2|b. If both sides contain one component, any one assignment suffices; summing over all assignments is an upper bound. Also 2^ω(ell/d)≤τ(a)τ(b). For a fixed k, replace the exact condition gcd(a,b)=k by k|a and k|b to upper-bound, obtaining for its total contribution to the expectation a constant times
```
Σ_(d≤4k) Σ_(d_1 d_2=d, gcd(d_1,d_2)=1)
 E[τ(a)·1_(lcm(k,d_1)|a)] E[τ(b)·1_(lcm(k,d_2)|b)].
```
Each T_i=lcm(k,d_i) is at most 4k²≤P^(1/4) for large P, so the weighted bound applies. Split c_i=gcd(k,d_i), s_i=d_i/c_i so T_i=k s_i. Use τ(k s_i)≤τ(k)τ(s_i) and φ(k s_i)≥φ(k)φ(s_i). Overcount the choices of c_1,c_2 by τ(k)² and allow each s_i≤4k separately. The fixed k contribution is therefore at most
```
O((ln P)²) · [τ(k)^4/φ(k)²] · (ln(8k))^4.
```
This is summable over k after factoring out (ln P)²: k/φ(k)≤τ(k), and the subpower divisor bound gives convergence.

For the rest, the true gcd exceeds P^(1/10), an event of probability at most a constant times
```
Σ_(d>P^(1/10)) m_d² ≪ (ln P)² P^(−1/10).
```
Use F(ell)≤τ(ell²)≤P^o(1) there. The entire expectation is O((ln P)²)=O(n²), as claimed. Conditional on ell the observed balanced product is uniform over its F(ell) possible antecedents. In addition Σ_ell F(ell)²/C² = E[F(Λ)]/C, proving the collision bound.

## Shannon and typical ambiguity

First, E ln k = O(1). Expand ln gcd(a,b) as the sum of ln r over prime powers r^j dividing both. Distinct sampling still costs at most a fixed factor over the independent average. For r^j≤P^(1/2), the sum of (ln r)/φ(r^j)² is bounded by its convergent infinite series. For r^j>P^(1/2), trivial counting bounds the sum by a constant times (ln P)² Σ_(d>P^(1/2)) (ln d)/d² = o(1). This also gives ln k=o(ln n) in probability by Markov's inequality.

For completeness, the classical first and second moment argument for shifted primes in this dyadic interval gives
```
E ω(p−1) = ln ln P + O(1),
ω(p−1) = (1+o(1)) ln ln P in probability.
```
To see this, truncate the prime divisors at P^(1/6), losing at most a bounded number per input. The first moments of the indicators are 1/(r−1) up to a total o(1) error by Bombieri–Vinogradov in [P,2P). Second moments for distinct r,s are 1/[(r−1)(s−1)] up to a total o(1) error by the same theorem at moduli rs≤P^(1/3), since each such modulus has at most two ordered decompositions into distinct primes. In this application one may use its prime-counting form with error O_A(P/(ln P)^A); the normalization by |S| instead of the logarithmic integral changes the sums by o(1) using its modulus-one term. Mertens' prime reciprocal estimate gives Σ 1/(r−1)=ln ln P+O(1), and hence the variance of the truncated count is O(ln ln P). Chebyshev proves the in-probability statement.

Applying the arithmetic fiber bound gives
```
ln F(Λ) ≤ ln 4 + ln k + ln(2)·[ω(p−1)+ω(q−1)].
```
The asserted typical bound and the mean log bound follow (ln ln P=ln n+O(1)). Since H(N|Λ)=E ln F(Λ) and Λ is a function of N, H(Λ)=ln C−H(N|Λ); entropy never exceeds the log of support size. This yields the claimed image-size lower bound on the balanced family. The large-gcd split was essential only to control an ordinary mean of F, not to derive the sharper coefficient for its mean logarithm.

## Literature and scope

[Ford–Luca–Pomerance](https://arxiv.org/abs/1408.6506) study the full image of the Carmichael function over arbitrary integers, rather than the size-biased fibers induced by two independent equal-bit-length primes. Recent primary work on shifted primes includes [the Poisson–Dirichlet law for prime predecessors](https://github.com/openai/math/tree/main/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026) and [higher-order Titchmarsh estimates](https://arxiv.org/abs/2611.12756); neither result is used here. The elementary hyperbola estimate is in the classical [Titchmarsh](https://doi.org/10.1007/BF03021203) setting; the prime number theorem and reciprocal sums are classical (see [Rosser–Schoenfeld](https://projecteuclid.org/download/pdf_1/euclid.ijm/1255631807)). The bounds are a collision and information accounting for one specified statistic, not an assumption transfer to another computational model or an efficient recovery mechanism.

[The exact checker](verify-factor-carmichael-fibers.js) checks fiber bounds, prime-power assignments, and the elementary weighted divisor inequalities on generated tiny pools only. The replay covers 13,357 generated pairs, including 477 repeated-value fibers, plus 18,982 arithmetic inequalities. It neither factors supplied numbers nor performs an inversion of the Carmichael statistic.
