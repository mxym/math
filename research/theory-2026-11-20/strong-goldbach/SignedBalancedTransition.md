# A signed individual-target estimate throughout the balanced transition

This is an estimate for **actual primes**, including the middle factor-count band left open by BalancedTwistFactorCounts.md. The point is to sum over **all allocations of the small prime factors before taking absolute values**. It saves a fixed power of log N over an entire balanced, signed divisor block for every target; it does not control the full divisor switch.

Let L=log N, ℓ=log L, and η=3/2−√2=0.0857864…. For fixed 0<β<1 put z=exp(L^β). Fix A>0. Let 1≤H≤L^β, and suppose H=o(L). Consider any k-interval [K₁,K₂] in [√N exp(−AH), √N exp(AH)] and α in the same latter interval. N is even. Define

    B = Σ_{K₁≤k≤K₂,(k,N)=1} μ(k)
        Σ_{n<N−αk, n≡N mod k} Λ(n) μ(N−n) log(αk/(N−n)).

Then uniformly in this data, as N→∞,

    |B| ≪_{β,A} N L^(−βη) (1+H)^(3/2) ℓ^C + O_{β,A,J}(N L^(−J))       (1)

for every fixed J, with a fixed C (allowed to depend on β,A). The same bound holds for the **centered** sum, subtracting 1/φ(k) times the unrestricted prefix with the identical weight, by Mertens cancellation as below. In particular, for polylogarithmic multiplicative windows (H=O(ℓ)), |B|≪_{A,κ}N/L^κ for every κ<η. If H=L^δ, there is still some fixed log-power saving whenever δ<(2/3)η. This is one-sidedly usable, but in fact bounds both signs.

## 1. Freeze the moving weight without losing a power of L

Remove proper prime powers n at cost N^(1/2+o(1)), since each N−n has at most N^o(1) divisors. Terms with a prime n|N have the same negligible bound, so on the remaining prime sum (N−n,N)=1 and the coprimality restriction on k is automatic. Terms with μ(N−n)=0 vanish. Write m=N−p=kd squarefree.

Take v from v₀=log(αK₁) to log N (if v₀≥log N the sum is empty). Its range has length O_A(H). The factor −log(αk/m) on m>αk is exactly

    ∫_{v₀}^{log N} 1_{m>exp(v)} 1_{log k<v−log α} dv.

For each v the k condition is an interval I (in the log variable), with |I|≤2AH; endpoints on a set of v of measure zero are immaterial. Crucially, the other indicator is a function of m alone and does not affect reallocations of a fixed m's prime factors.

Let a be the product of the prime factors of m up to z; m=ab with b z-rough (no prime factors ≤z). We may assume a≤N^(1/20) with error O_J(N L^(−J)), even before using any Möbius cancellation. Indeed for squarefree m the total number of possible divisors k of m is at most τ(a)τ(b), and Σ_{b≤N/a}τ(b)≪(N/a)log(2N). With h=1/log z,

    Σ_{a>N^(1/20), a squarefree, p|a⇒p≤z} τ(a)/a
      ≤ exp(−L/(20 log z)) ∏_{r≤z prime}(1+2r^h/r)
      ≪ exp(−L^(1−β)/20)(log z)^O(1).

The suppressed factors L and H from the prime and log weights do not matter.

Now write k=e k₀, d=(a/e)d₀, with e|a and k₀d₀=b. The sign μ(k)μ(m)=μ(d)=μ(a)μ(d₀)μ(e). The prime p=N−ak₀d₀, the condition m>exp(v), and the log p weight are **identical for every allocation e|a**. Define

    F_a(u)=Σ_{e|a} μ(e) 1_I(u+log e).

For fixed a,k₀,d₀,v the sum of interest has this factor at u=log k₀; this is where the proof uses the actual sign. Only now take absolute values, drop the condition m>exp(v), and enlarge the sum to rough k₀,d₀ (the other squarefreeness conditions may be dropped). When F_a(log k₀)≠0, K₁/a≤k₀≤K₂. Consequently k₀≥N^(2/5) and Y=N/(ak₀)≥N^(2/5) for sufficiently large N (since H=o(L)). Always ignore primes p dividing N. We can also ignore p≤w=exp(L/ℓ²), at total cost N^o(1) before regrouping, since there are at most w such p and at most N^o(1) divisors per complement.

## 2. Two rough cofactor estimates, with the prime still present

Uniformly for admissible a,k₀ with (ak₀,N)=1 we have

    Σ_{d₀≤Y, P⁻(d₀)>z, p=N−ak₀d₀>w prime} log p
       ≪ Y ℓ^C/log z.                                                   (2)

Here P⁻(1)=∞; if (ak₀,N)>1 the prime sum with p∤N is empty. To prove (2), sieve d₀ on its interval of length Y. For each r≤w with r∤ak₀, forbid the single class N/(ak₀) mod r. For r≤z forbid also 0 mod r; a duplicated class counts once. For large N, z≤w. Away from r|Nak₀ the local factors are 1−2/r for r≤z and 1−1/r for z<r≤w. Treat 2 separately. Mertens shows that the product is ≪[log z log w]^(−1) times ∏_{r|Nak₀,r>2}(1+O(1/r))≪ℓ^C/[log z log w]. Indeed Σ_{r|Nak₀}1/r≤log ℓ+O(1) by splitting at 4L. For precision, truncate the elementary upper Bonferroni sieve at even J₀≈C₀ℓ. Every modulus is ≤w^{J₀}=N^o(1) and total CRT counting error ≤Σ_{b≤w^J₀}2^ω(b)=N^o(1). The model expansion tail is ≤Σ_{j>J₀} S^j/j!, S≤(2+o(1))ℓ; C₀ can make it ≪L^(−10). Since Y≥N^(2/5) and log w=L/ℓ², multiplying by log p≤L proves (2).

A second application, merely forbidding 0 mod r for r≤z, gives on every interval J' in the k₀-range

    # {k₀ in J': P⁻(k₀)>z} ≪ |J'|/log z + N^o(1).                     (3)

The additive error is independent of the interval: use the same even order and at most z^J₀=N^o(1) moduli. For fixed a, F_a(u) is piecewise constant with ≤2τ(a)+1 intervals and height ≤τ(a). Partial summation of (3) with weight 1/k₀ on each such interval yields

    Σ_{k₀ rough} |F_a(log k₀)|/k₀ ≪ (1/log z) ∫_R |F_a(u)|du
                                       + N^(−2/5+o(1)) τ(a)^2.         (4)

Indeed the prefix of each interval begins at ≥N^(2/5), and integrating the additive error and its endpoint gives O(N^(−2/5+o(1))) per constant unit of weight per interval. This controls point masses at single endpoints as well. After (2), followed by (4), the whole fixed-v sum is at most

    N ℓ^C/(log z)^2 · Σ_{a squarefree,z-smooth} ||F_a||₁/a
       + O(N^(3/4))                                                     (5)

for sufficiently large N: the additive error in (4) is summed only over a≤N^(1/20), with Σ τ(a)^2/a=N^o(1). The main sum is safely extended to all products of distinct primes ≤z; all terms are now nonnegative.

## 3. A strict saving from the signed divisor Fourier product

The function F_a is supported in an interval of length ≤log a+|I|. For fixed λ>0 the support bound, followed by weighted Cauchy–Schwarz, gives

    [Σ_a ||F_a||₁/a]²
       ≤ [Σ_a λ^ω(a)(log a+|I|)/a]
         [Σ_a λ^(−ω(a)) ||F_a||₂²/a].                                  (6)

The first bracket is ≪ (log z)^λ(log z+|I|)≪_A(log z)^(λ+1), by factoring ∏_{r≤z}(1+λ/r) and using Σ_{r≤z}(log r)/r≪log z.

For the second bracket, Plancherel and finite Euler factorization give exactly (up to the Fourier normalization 1/(2π))

    ∫ |hat 1_I(t)|² ∏_{r≤z} (1+|1−r^(it)|²/(λr)) dt.                  (7)

Only primes occur in the product. For |t|≤L^D (any fixed D), uniformly

    ∑_{r≤z} cos(t log r)/r ≥ −O_D(log ℓ),
    ∏_{r≤z}(1+|1−r^(it)|²/(λr)) ≪_{D,λ} (log z)^(2/λ) ℓ^C.

For the first inequality split at u₀=exp(ℓ^4), eventually below z. The primes up to u₀ can cost only O(log ℓ) by Mertens. By the classical prime number theorem with error O(x exp(−c√log x)), partial summation from u₀ to z replaces the remaining sum by ∫_{log u₀}^{log z}cos(tv)dv/v with O((1+|t|)exp(−c'ℓ²)) error. This integral is ≥−O(1) uniformly: the portion |t|v≤1 is nonnegative, and the rest has bounded primitive after the substitution w=|t|v and an integration by parts. The second inequality follows by |1−r^(it)|²=2−2cos(t log r) and log(1+x)≤x. Outside |t|≤L^D just bound the product by O((log z)^(4/λ)); there |hat 1_I|≤2/|t| and the resulting tail is negligible for D large. Since ∫|hat 1_I|²=2π|I|, the second bracket of (6) is ≪(1+|I|)(log z)^(2/λ) ℓ^C.

Combining (5)–(7) and taking λ=√2 bounds the fixed-v contribution by

    N (1+H)^(1/2) ℓ^C · (log z)^((1+2√2)/2−2) + O(N^(3/4)).

The exponent of log z is **−η<0**. Integrate over v of length O(H) to obtain (1). The centered reference contributes less than N/L^J for every fixed J: for each m, the interval in k has endpoints ≥N^(1/3), and the Mertens bound Σ_{k≤u,(k,N)=1} μ(k)/φ(k)≪exp(−c√L) from [Huang–Li Lemma 1](https://arxiv.org/html/2005.03811v2) applies throughout. Partial summation with the logarithm costs O(1+H); elementary Σ_{n<N}Λ(n)≪NL suffices. This last argument is independent of the sign estimate for the actual part.

## Consequence: the square-root endpoint and slightly below

Let 0≤δ<(2/3)η and Q_N=√N exp(−L^δ). Assume **only the twisted** centered all-moduli prefix discrepancy E(N,Q_N)≪_J N/L^J for every fixed J as in AnnihilatingModuli.md. There is no assumed ordinary EH and no known proof here of this twisted conjecture. For every κ<η−3δ/2 one obtains, for all sufficiently large even N,

    Σ_{p₁+p₂=N} log p₁ log p₂ = N S(N) + O_{δ,κ}(N/L^κ).             (8)

For clarity on parameters, choose β<1 so βη>κ+3δ/2. In CenteredDivisorSwitch.md use B=L² and α=√N/L^D, where D is a sufficiently large **fixed** constant. The proofs there are uniform when log α/log N stays in a compact subinterval of (0,1): the Brun–Titchmarsh slack, the divisor-sum exponential estimates, and the endpoints with power separation all remain uniform (or repeat those proofs with θ fixed between 0.49 and 0.51 as a bound). The original small-divisor truncation costs O(N/L²); the retained ordinary moduli ≤αB²=√N/L^(D−4) are handled unconditionally by classical Bombieri–Vinogradov. Only one fixed strong saving is needed on that side: e.g. take unweighted error O(N/L^30), then use the weighted Cauchy–Schwarz calculation of that note; select D after this exponent. For k≤min(Q_N,N/α), apply the twisted hypothesis and partial summation with its true triangular endpoint. For the omitted band Q_N<k<N/α, (1) controls the centered remainder with H=O_D(ℓ+L^δ). Finally the annihilating p² modulus forces the global mean T(N)=ΣΛ(n)μ(N−n) to be smaller than N/L^J for every fixed J under this literal all-modulus hypothesis. This proves (8). If instead a BV-form twisted conjecture grants the bound at √N/L^{B(J)} for *some* fixed B(J) at each requested accuracy, the same proof uses one sufficiently large fixed J (including for the zero-class step); the uncovered block then has H=O(ℓ), and (8) holds for every κ<η. No inference that this conjectural signed distribution follows from the **ordinary** Bombieri–Vinogradov theorem is justified.

Compare [Huang–Li, Corollary 1](https://arxiv.org/html/2005.03811v2), which gives eventual positivity from a twisted level N^σ with σ>1/2 once ordinary BV is used. Changing the size of this signed block is not a mere global rescaling of the ordinary EH hypothesis: the twisted sequence changes with N, and in (8) the only input not proved here is at the same fixed target. The unconditional estimate (1) itself is independent of that hypothesis. It handles only the balanced transition, not the many smaller squarefree twisted moduli. Without control there one cannot infer a uniform Goldbach lower bound. No priority claim over all sieve literature is made.
