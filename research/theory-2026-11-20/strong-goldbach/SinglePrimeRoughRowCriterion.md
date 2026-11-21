# A one-sided single-prime-row criterion for eventual binary Goldbach

**Scope.** The cutoff identities, reference estimates, presieve removal and thin-sector upper bounds below are unconditional. The resulting single signed inequality (1) for the actual shifted primes has not been established. This is not a proof of binary Goldbach or a claim that the inequality is logically weaker than every other sufficient conjecture.

Write x=N/2 for an even N, I=(x/2,x]∩Z, L=log x, S(N)=2C_N for the ordinary binary singular series, and M_N=S(N)x/(2L). For a fixed sufficiently large s, take ε=e^(−s/2) and set

    y=x^ε,    z=x^(1/3−2ε),
    J={p prime : x^(1/3+5ε)<p≤x^(1/2−(s+2)ε)}.
    a(n)=(log(N−n))·1_{N−n prime},
    Z=exp(L^(1/4)), V_0=∏_{ℓ<Z}(1−1/ℓ),
    b(n)=V_0^(−1)·1_{P⁻(N−n)≥Z},     w(n)=a(n)−b(n), n∈I.

Use P⁻(1)=+∞, and write ω_J(v)=Σ_{p∈J}1_{p|v} (distinct factors, including on prime powers). Define the **actual** signed statistic

    R(N) = Σ_{y≤r<z; r prime} Σ_{rv∈I; P⁻(v)≥r}
                          (1−ω_J(v)) w(rv).

For this fixed pair s,ε, the hypothesis

    R(N) ≤ ½ M_N for every sufficiently large even N                    (1)

implies that there are at least M_N/(5 log N) prime pairs with one member in (N/4,N/2], for all sufficiently large even N. Only this upper side and this single combined sum are needed: the test is not uniform in individual rows or in arbitrary bilinear coefficients. Every n=rv tested by R is composite (r≤z while n>x/2); the comparison b has no occurrence of prime pairs as an input. The conclusion is eventual. A fully effective bound and a gap-free finite verification would still be needed to turn an eventual result into one for every N.

## 1. Actual prime extraction with only narrow composite remnants

Let H_u(n)=1_{P⁻(n)≥u}. Because every marker p∈J exceeds z, removing p does not change H_z(n). Hence the exact factor weight is

    B(n) = H_z(n)−Σ_{p∈J,p|n} H_z(n/p)
         = H_z(n)(1−ω_J(n)).

For z-rough n∈I, n has at most three prime factors counted with multiplicity because z^4>x. If a marker p divides n, then Ω(n) cannot be at least three: p z²>x. Two marked factors (including equal ones) cannot multiply to n∈I because their product is at most x^(1−2(s+2)ε)<x/2. Thus B(n)=1 on primes, 0 on marked semiprimes, 0 on non-z-rough integers and 1 on the remaining z-rough composites. This includes prime powers and finite endpoints. If r≤q is the least factor of a surviving semiprime, it must lie in one of the two strips

    (1/3−2ε) ≤ log_x r ≤ (1/3+5ε),   or
    (1/2−(s+2)ε) ≤ log_x r ≤ 1/2.

For a surviving ternary n=rqt, r≤q≤t, its least factor has exponent in [1/3−2ε,1/3]. Here and below classification rather than distinctions at shared strip endpoints matters.

**Upper sieve for the true loss.** The total shifted-prime weight of these remnants is

    C_a(N):=Σ_{n∈I composite} a(n) B(n)
       ≪ ((s+2)ε + o_s(1)) M_N.                                      (2)

To see this, condition on r in the semiprime branch, or on r,q in the ternary branch. Write h=r or h=rq and v for the last factor, so v∈(x/(2h),x/h]. If (h,N)>1 then N−hv is divisible by a prime divisor ℓ of h, and lies at least x, whereas ℓ≤h<x; it cannot be prime. Otherwise apply the two-dimensional upper sieve to v and N−hv in that interval. Its length Y=x/(2h) ≫ x^(1/3−2ε) whenever the fixed factors admit a candidate (because the last factor is at least z). For definiteness use sieve cutoff Y^(1/16) and level Y^(1/4), so all actual candidates have v≥z and N−hv≥x above the cutoff. The prime factors of h are at least z and all exceed the sieve cutoff. Thus at the sieved ℓ the two excluded residues coincide exactly when ℓ|N; the local factor is the ordinary one for S(N). Counting the prescribed residue classes mod d gives remainder at most 2^ω(d); their sum through Y^(1/4) is O(Y^(1/4) log Y), negligible. The dimension-two upper sieve therefore bounds the number of v by O(S(N) x/(h L²)), uniformly in h,N,s as long as ε is small. One can use the classical two-form sieve as in [Salazar, arXiv:2611.10059v1, §5.2](https://arxiv.org/html/2611.10059v1#S5.SS2) (the local factors here agree on all sieved primes). This also follows directly by the dimension-two fundamental lemma at a fixed sufficiently large ratio of level and cutoff; taking an even smaller fixed cutoff, if desired, does not affect the conclusion. The possible equality endpoints cost O(1) inside each such sieve interval and are absorbed by the stated bound.

Multiply by a(n)≤log N. On each compact positive exponent strip [α,β] for the smallest r, Mertens gives Σ1/r=log(β/α)+o(1)=O(β−α)+o(1), with an absolute bound in our ranges. In the ternary case the unrestricted sum over q≥z is O(1). This proves (2), even if repeated factors occur.

## 2. A classical Type I statement for both sequences

For d≥1 put g_N(d)=1_{(d,N)=1}/φ(d), and X_I=x/2. For every fixed δ>0,B>0,C≥0 and t=a or b,

    Σ_{d≤x^(1/2−δ)} τ(d)^C |Σ_{n∈I,d|n} t(n)−X_I g_N(d)|
       ≪_{δ,B,C} x L^(−B).                                             (3)

For a on reduced classes this is ordinary Bombieri–Vinogradov on the fixed-length prime interval [N−x,N−x/2), endpoints arbitrary, with proper prime powers removed. There are O(√x) such powers up to 2x and their total log weight per modulus is O(√x L²); summing τ(d)^C through x^(1/2−δ) is harmless. If (d,N)>1 then no contributing prime N−n≥x can divide d<x. The usual arbitrary fixed divisor weight follows by Cauchy–Schwarz using the unweighted Bombieri–Vinogradov estimate with enlarged log saving, the trivial per-modulus bound O(x L/d), and Σ_{d≤x} τ(d)^(2C)/d≪_C L^(O_C(1)).

For b, apply even and odd Bonferroni ranks J_0 near L^(1/4) to exclude primes ℓ<Z. If an ℓ<Z divides (N,d), b is identically zero in the class. Otherwise the conditional congruence counts on multiples of d have density 1/ℓ exactly for ℓ∤d; primes dividing d cannot cause exclusions. CRT error for the truncated sums is O((1+Z)^(J_0+1))=x^o(1) per d; the error in the main finite product is at most (Σ_{ℓ<Z}1/ℓ)^J_0/J_0!, smaller than every power of 1/L. Before division by V_0, the density is exactly

    (1/d)∏_{ℓ<Z, ℓ∤d}(1−1/ℓ).

For (N,d)=1 its normalized value differs from 1/φ(d) by at most O(L/Z) relatively, since at most O(L) distinct primes dividing d exceed Z. For the remaining nonreduced d some ℓ|N, ℓ≥Z divides d; since τ(ℓm)≤2τ(m), Σ_{d≤x,ℓ|d}τ(d)^C/d≪_C L^(O_C(1))/ℓ. Summing over those primes and using V_0^(−1)≪log Z proves (3). For clarity, the CRT floor error times all d is O(x^(1/2−δ+o(1))) even with the divisor weights.

Finally the actual prime sum of the reference has the usual lower main term:

    Σ_{p∈I prime} b(p)=(1+o(1)) M_N, uniformly in the even N.              (4)

Apply the same Bonferroni ranks, now to primes p in I and exclusions p≡N mod d. For d coprime to N use the prime-count form of ordinary Bombieri–Vinogradov (all d involved are x^o(1)); nonreduced classes contain at most O(log N) exceptional primes per d, negligible. The local sieve density is 1/(ℓ−1) for ℓ∤N and 0 for ℓ|N (including 2|N). Its rank tails are bounded as above with Σ 1/(ℓ−1) in place of Σ1/ℓ. Multiplication by V_0^(−1) leaves the truncated singular series S_{<Z}(N), from the exact identity on each local prime

    (1−1/ℓ)^(-1) (1−1_{ℓ∤N}/(ℓ−1)) =
        (1−ν_ℓ(N)/ℓ)/(1−1/ℓ)^2,  ν_ℓ(N)=1+1_{ℓ∤N}.

The prime interval contributes (1+o(1))x/(2L). The missing factors have log tail O(1/Z+L/Z)=o(1), uniformly through even N, proving (4).

## 3. The presieve error is unconditional

Use the ordinary dimension-one fundamental lemma at y=x^ε and level D=y^s; for example use the Rosser–Iwaniec linear sieve of [Iwaniec’s primary paper, *A new form of the error term in the linear sieve*](https://bibliotekanauki.pl/articles/1393119.pdf), or its explicit modern formulation [Bordignon–Johnston–Starichkova, arXiv:2207.09452v6, §2](https://arxiv.org/html/2207.09452v6#S2). We use just the usual dimension-one \(F(s),f(s)=1+O(e^{-s})\) bound as s gets large, and an o_s(1) coefficient error as x tends to infinity at fixed s. The dimension constant is uniform in N: deleting primes dividing N from g_N only reduces the Mertens upper product, and 2 was already excluded. Put

    V_N(y)=∏_{ℓ<y}(1−g_N(ℓ)) ≍ S(N)/log y.

This follows from the exact local identity above and Mertens, losing at most a uniform relative O(1/y+L/y) for these fixed powers. The estimate applies to each nonnegative sequence t=a,b on I, both unmarked and separately on the subprogression p|n for p∈J; the main term is \(X_I V_N(y)\) or \(X_I g_N(p)V_N(y)\). Sums of the sieve remainders over all marked p are covered by (3), since

    pd≤(max J)y^s≤x^(1/2−2ε),

and p is the unique J-factor of pd: every prime factor of d<y^s is below min J. The condition (p,N)>1 causes a zero main and is already handled by (3). The unmarked weights also lie below this Type I level. The sum of the marked main weights satisfies Σ_{p∈J}g_N(p)=O(1), uniformly. Comparing the upper and lower enclosures for t=a and t=b for each nonnegative sequence and taking the sum of the absolute discrepancy bounds proves

    |E_y(N)|:=|Σ_{n∈I} w(n) H_y(n)(1−ω_J(n))|
       ≪ (e^(−s) ε^(−1)+o_s(1)) M_N.                                 (5)

In (5) all limits in x precede choosing a large fixed s. No distribution beyond one half and no signed Type II estimate was used here.

## 4. Exact one-sign residual

Buchstab's one-step identity, by the least prime factor (equality at y included and at z excluded), is

    H_z(n)=H_y(n)−Σ_{y≤r<z; r prime; r|n}1_{P⁻(n/r)≥r}.

The indicator includes repeated r without double-counting; only the least factor can qualify. No marking prime belongs to the r-range, so ω_J(rv)=ω_J(v). Therefore

    Σ_{n∈I} w(n) B(n)=E_y(N)−R(N)                                     (6)

exactly. Using B≥0 and B=1 on primes gives

    Σ_{p∈I prime} a(p)
       = Σ_{n∈I} b(n) B(n)+E_y(N)−R(N)−C_a(N)
       ≥ (1−o(1))M_N−|E_y(N)|−R(N)−C_a(N).                           (7)

With ε=e^(−s/2), the terms proportional to e^(−s)/ε and (s+2)ε tend to zero as s increases. Fix s sufficiently large that (2) and (5) combine to at most M_N/4 eventually. Substitution of (1) in (7) gives at least M_N/5 eventually; dividing by log N proves the assertion. The same proof leaves an open range of sufficient one-sign constants below 1 if s is made larger.

## Relation to nearby approaches

- [Ford–Maynard](https://arxiv.org/pdf/2407.14368), Theorems 2.4–2.5 and 8.2–8.3, identify Type I/II geometry and show how a thin exceptional exponent sector can be paid for with a pointwise divisor bound. Their bounded-sequence theorem as stated also assumes \(\sum_p b(p)\gg x/\log x\) at fixed pointwise divisor bound; the unweighted shifted-prime sequence instead has reference scale \(S(N)x/\log^2 x\). The direct upper-sieve payment (2) is scale-correct without imposing that bounded-sequence theorem's full hypotheses. Here a specific exact subtraction replaces the abstract general dual certificate.
- The prior fixed-power stopping-sieve reduction asks for Möbius-twisted all-moduli progression information, and the AA route asks for cancellation with two independent divisor rows near square-root size. This reduction leaves only a single prime row below exponent 1/3, its long rough complement, and a fixed positive/negative marker. It does not assert that bounds sufficient in one method imply all those in another. No proposed step uses the bound on λ(N−p) from the Chan audit.
- The comparison of a supplied rough family with upper bounds for losses at each new prime already appears in [Salazar, arXiv:2611.10059v1, §§5,7](https://arxiv.org/html/2611.10059v1). The criterion here instead subtracts a marked branch exactly, pays only thin composite strips, and compares the remaining signed *collective* rough-row discrepancy to a prime reference. [Li–Liu’s \(1+1.9\) paper](https://arxiv.org/html/2606.05224v2) and [Wu’s double sieve](https://www.impan.pl/shop/publication/transaction/download/product/82961) estimate positive switched branches; such separate unsigned majorants do not prove (1). A uniform estimate of (1) is the unresolved step, not an observed consequence of ordinary distribution.

## Independent check and 2026H2 comparison

The unconditional steps were checked separately: exact extraction of the prime term including multiplicities, the scale-correct thin sectors with a two-form sieve, the shifted-prime/rough-reference Type I estimate, presieving each nonnegative marked sequence, and the exact Buchstab sign. None supplies the upper bound (1). The needed one-sided estimate is restricted to this combined prime-row statistic, not to arbitrary weights, nor claimed equivalent to previously studied Type II inputs.

The separate July–21 November pass checked [Salazar, arXiv:2611.10059v1](https://arxiv.org/html/2611.10059v1#S5.SS2), 6 November, the classical two-form local factors and distinct prime-cover loss, and [Li–Liu, arXiv:2606.05224v2](https://arxiv.org/abs/2606.05224v2), updated 8 August, for switched positive terms. [Nelson, arXiv:2611.14580v2](https://arxiv.org/abs/2611.14580v2), updated 16 November, studies relations in the binary Goldbach ring rather than this analytic inequality. The [available AMRAL report index](https://amral.evemisslab.com/en/links/) records another fixed-residue Type II program and its open gaps; linked full notes were not accessible in this comparison. The older Ford–Maynard framework and repository's previous stopping and square-root sections are explicit antecedents. Exact repository and targeted literature searches did not locate this specific signed statistic and threshold, a bounded observation rather than a priority claim.
