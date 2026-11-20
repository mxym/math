# Exponential absolute tail in the actual factor count

Let L=log N, η=3/2−√2, m=N−p, K(m)=Σ_{k|m}μ(k)min(0,log(k/√m)). As M→∞ through fixed integers one has, with absolute C,

    limsup_{N→∞ even} [1/(NS(N))]
        Σ_{p<N, ω(m)≥M} (log p) μ²(m) |K(m)| ≤ C exp(−0.0154 M).      (1)

Thus the very high even-Ω negative tail in the one-sided identity is exponentially small in M, **after** limsup in N. No small effective value of M at which the tail drops below a specific cutoff is asserted. Related concentration of smoothed sieve weights over unrestricted integers is studied by [Granville–Koukoulopoulos–Maynard, Theorem 1.2](https://arxiv.org/abs/1606.06781); here the sum is over actual reflected primes at every even target, with its variable relative center.

**Elementary proof with exponent 0.012.** Put τ=exp(−0.14M) for sufficiently large M that τ≤τ₀, and y=N^τ. Complements with P⁻(m)≤y cost O(τ^η NS(N)) in the limsup by FixedPowerStoppingSieve.md (1), with an absolute constant. On P⁻(m)>y use |K(m)|≤L τ_d(m), where τ_d is the divisor count, and 1_{ω(m)≥M}≤2^{ω(m)−M}. For squarefree m, split divisor pairs m=kd restricting k≤√N and multiplying by two, with 2^ω(m)=2^ω(k)2^ω(d). Removing squarefreeness after this factorization gives an upper bound. Omit p≤N^0.00002 and p|N at negligible cost for each fixed M and τ by the divisor bound (discard these cases before inserting the positive majorant).

For fixed rough k≤√N, (k,N)=1, put X=N/k≥√N. The biased divisor truncation for t=2 gives

    2^ω(d) ≤ 3 Σ_{a|d, a≤X^(3/4)} μ²(a)

since a uniformly randomly chosen subset of d's distinct prime factors has E(log a)=½log rad(d)≤½log X, and Markov excludes at most 2/3 beyond (3/4)log X. For a counted d all such a are y-rough. Write d=a b; for an upper bound keep P⁻(b)>y and p=N−kab prime. Since X/a≥N^(1/8), the two-condition upper sieve used in FixedPowerStoppingSieve.md gives

    Σ_{b≤X/a, P⁻(b)>y, p=N−kab>w prime} log p
        ≪ [NS(N)h(ka)]/(ka τ L),

where w=N^0.00002 and the tiny CRT error is absorbed into the main bound. This is uniform for all large N in terms of a fixed τ≤τ₀. A noncoprime ka,N contributes nothing once p|N is removed. For y-rough ka≤N, h(ka)≤2 for all sufficiently large N depending on τ: each prime factor exceeds N^τ and their number is at most 1/τ. The elementary Euler estimates

    Σ_{a≤N, μ²(a)=1, P⁻(a)>y} 1/a ≪ τ^(−1),
    Σ_{k≤N, P⁻(k)>y} 2^ω(k)/k ≪ τ^(−2)

have absolute constants in the limsup for every fixed τ: the products over y<r≤N use Σ1/r=log(1/τ)+o_τ(1) and Σ_{r>y}1/r²=o_τ(1). Thus the entire y-rough, high-count part has bound ≪ NS(N) 2^(−M)τ^(−4). Here the extra L from the kernel cancels the L in the rough prime sieve. Combining the two parts gives an absolute constant times exp(−0.14η M)+exp(−(log 2−0.56)M); since 0.14η>0.012 and log 2−0.56>0.13, (1) follows. This controls actual weighted absolute values rather than deriving a sign from the degree count.

The positive rough counting step uses established sieve ideas. See [Aquila, 10 November 2026, credits and Lemmas 11–13](https://hexagonmath.org/pdf/2611.00415v1) for related factor counts and further references; that manuscript counts plain almost-prime representations rather than the centered log-weighted kernel. The separate [largest-factor note](OneSidedLargestFactor.md) gives the exact negative chamber when only three primes enter the cutoff. The low even-factor signed terms still require individual bounds at the main-term scale.

### Exponent 0.0154 via a multiplicative sieve

[Pollack, Theorem 1.1](https://www.pollack-math.net/brunmultiplicative4.pdf) gives a short independent rough estimate and slightly improves the rate in (1). Take the full interval (0,N], w=N^0.00002, and the nonnegative multiplicative weight f(m)=μ²(m)6^ω(m)1_{P⁻(m)>N^τ}, with f(1)=1. Its growth-class constants are uniform in N and τ since 6^ω(m)≪_ε m^ε. For each prime r≤w not dividing N, forbid the nonzero residue N mod r in m; impose no conditions at other primes. Every p=N−m>w prime passes this sieve. The exponential of the f-prime sum in Pollack's bound is O(τ⁻⁶) in the limsup for each fixed τ, by Mertens. The excluded-residue factor is O(S(N)/L) since exp(1/r)≤(r−1)/(r−2) for r>2, and r=2 divides N. Thus the sifted sum of f is O(NS(N)τ⁻⁶/L²), with an absolute constant in the normalized limsup.

On squarefree m with ω(m)≥M, (log p)|K(m)|≤L²·2^ω(m)≤3^(-M)L²·6^ω(m). The rough part is therefore O(NS(N)3^(-M)τ⁻⁶) after the same negligible exclusions. Use τ=exp(−0.18M), then apply the fixed-power stopping sieve to the nonrough part. The two exponents are 0.18η>0.0154 and log(3)−1.08>0.0186. This proves (1) as stated. Pollack also records the earlier Barban–Levin treatment of the conjugate sum over reflected primes; the specialized kernel estimate on the nonrough part is the extra input here.
