# Individual-target localization of the signed squarefree transition sum

**Conclusion and limits.** For every large even N, in a fixed polylogarithmic window around the balanced modulus √N, the actual reflected-prime divisor sum on squarefree complements is negligible on the N scale outside a band around **2 log log N prime factors**. At the finer N/log N scale we can still exclude both ω(N−p)≤0.37 log log N and ω(N−p)≥4.32 log log N. These are bounds even for the *absolute* contribution of the excluded terms; the sign on the surviving terms remains unresolved. This is a fixed-N estimate, not an assertion that the surviving terms must attain the predicted order, nor an estimate of the whole divisor switch.

Let L=log N, ℓ=log L and fix A>0. Set K₋=√N L^(−A), K₊=√N L^A. Let α satisfy √N L^(−A)≤α≤√N L^A. For a set U of positive integers (*complements*, permitted to depend on N) define the actual block

    B(U) = Σ_{K₋≤k≤K₊,(k,N)=1} μ(k)
           Σ_{n<N−αk, k|N−n, m=N−n∈U} Λ(n) μ(m) log(αk/m).

Take U={m: ω(m)≤cℓ} if 0<c<2, and U={m: ω(m)≥cℓ} if c>2. With I(c)=2−c+c log(c/2), for every such fixed c

    |B(U)| ≤ Σ of the absolute values of its individual terms
            ≪_{A,c} N L^(−I(c)+o(1)).                                (1)

The o(1) is in the exponent of L, uniformly in N and admissible α. Indeed on the support m>αk and m≤N, so |log(αk/m)|≤2Aℓ. The same result holds with arbitrary coefficients of modulus ≤ℓ^C for fixed C, and with subwindows. Proper prime powers n=p^j, j≥2, cost at most N^(1/2+o(1)) using τ(N−n)=N^o(1). For primes p and squarefree m=kd, k and d are coprime squarefree and μ(k)μ(m)=μ(d). Thus (1) controls a portion of the actual signed k-discrepancy in CenteredDivisorSwitch.md. The subtraction of the centered reference in the same block changes B(U) by less than N/L^H for every fixed H (proof below).

The two positive roots of I(c)=1 are approximately 0.3733646177 and 4.3110704070. The values 0.37 and 4.32 lie strictly outside. For the coarser scale N one may use any fixed band (2−ε)ℓ < ω(m) < (2+ε)ℓ, with 0<ε<2, since I(c)>0 for c≠2. This exceptional-set statement is for the *divisor-weighted* transition block. It does not assert that most primes p have ω(N−p) near 2ℓ.

## 1. An exponential moment uniform in the target

For fixed positive s,t, put

    M(s,t) = Σ_{K₋≤k≤K₊,(k,N)=1} Σ_{d≤N/k, p=N−kd prime, μ²(kd)=1}
                         (log p) s^ω(k) t^ω(d).

We claim

    M(s,t) ≪_{A,s,t} N L^(s+t−2+o(1)).                              (2)

All estimates below are upper bounds; after factoring s^ω(k)t^ω(d) the squarefree and coprimality restrictions on d may be dropped.

For k in this window and Y=N/k we first establish

    Σ_{d≤Y, N−kd prime} t^ω(d) ≪_t Y L^(t−2+o(1))                 (3)

uniformly in k coprime to N. At t=1 it is ordinary Brun–Titchmarsh (or the elementary sieve below). The factor implied by N and k's own prime divisors is at most a power of log L and so is absorbed in L^o(1).

**Case 0<t<1 (elementary fractional upper-bound sieve).** Put z=exp(L/ℓ²). Apart from p≤z (at most 1+z/k admissible d, negligible), pass only those d avoiding r|N−kd for every prime r≤z. Charge the factor t for any such r dividing d; leaving out factors r>z only gives an upper bound. For each r≤z define x_r(d)=1 if r|N−kd, x_r(d)=1−t if r|d but r∤N−kd, and zero otherwise. The weight under consideration is bounded above by ∏(1−x_r(d)). The total sum X_r of x_r over residues mod r is 2−t if r∤kN, 1 if r|N (necessarily r∤k), and 1−t if r|k. This deals also with the prime 2. Each x_r has at most two supported residues.

For completeness, truncate inclusion/exclusion from above at the even integer J nearest above Cℓ, with C sufficiently large fixed. The Bonferroni upper inequality for 0≤x_r≤1 follows by independent Bernoulli trials of probabilities x_r. CRT shows that the sum over d≤Y of a term with squarefree modulus b is Y∏_{r|b}(X_r/r)+O(2^ω(b)); all such b≤z^J=N^o(1), so the aggregate counting error is N^o(1) (use Σ_{b≤u}2^ω(b)≪u log(2u)). The absolute tail of the *model* expansion is bounded by Σ_{j>J} S^j/j!, S=Σ_{r≤z}X_r/r≤(2+o(1))ℓ. Choose C large in terms of any desired fixed H to make this tail O(L^(−H)), by Stirling. No large-modulus equidistribution is assumed. Finally

    ∏_{r≤z}(1−X_r/r) ≪ (log z)^(−(2−t)) ∏_{r|kN}(1+O_t(1/r))
                      ≪ L^(t−2+o(1)).

Here Mertens' theorem and Σ_{r|kN}1/r=O(log log log(10N)) suffice: split r at 3L, handle smaller r by Mertens, and the larger ones using log(kN)≪L. All products at the finitely many small primes can be treated separately. This proves (3) below 1.

**Case t>1 (biased divisor truncation).** Write η=t−1. The factorization t^ω(d)=Σ_{a|d} μ²(a)η^ω(a) corresponds to independently choosing each prime divisor of d with probability η/t to put it into a. Under these normalized weights, E(log a)=(η/t)log rad(d)≤(η/t)log Y. If η/t<γ<1, Markov gives

    t^ω(d) ≤ [1−η/(γt)]^(−1) Σ_{a|d, a≤Y^γ} μ²(a) η^ω(a).

For (ka,N)=1, Brun–Titchmarsh on primes up to N in the reduced class N mod ka gives ≪_t N/[φ(ka)L] contributions for the inner d≡0 mod a; indeed N/(ka)≥Y^(1−γ), and log Y∼L/2. When (a,N)>1 any counted p divides N. Before expansion all such exceptional primes p|N together contribute N^o(1) for each k (t^ω(d)=N^o(1) uniformly); remove these p first. Use φ(ka)≥φ(k)φ(a), and

    Σ_{a≤Y^γ} μ²(a)η^ω(a)/φ(a) ≤ ∏_{r≤Y}(1+η/(r−1)) ≪_t L^η.

Since k/φ(k)≪log L this proves (3) for t>1. This argument uses classical prime upper bounds only, not distribution of twisted sequences.

For s>1 the mean over K<k≤2K of s^ω(k) is ≪_s L^(s−1) using the divisor expansion and Σ_{k≤2K,a|k}1≤2K/a, followed by the Euler product. For 0<s<1 apply the same elementary fractional upper-bound sieve, now with x_r(k)=(1−s)1_{r|k}, X_r=1−s, on an interval of length K=N^(1/2+o(1)); it bounds the mean by L^(s−1+o(1)). At s=1 it is trivial. There are O_A(1+ℓ) dyadic intervals covering the k window, so Σ s^ω(k)/k ≪ L^(s−1+o(1)). Combining with (3) and log p≤L proves (2). All uses of classical estimates are one-sided and individually uniform in this target. For related general upper-bound sieve methods, compare the independent [Friedlander–Iwaniec asymptotic sieve](https://arxiv.org/abs/math/9811186); we do not invoke its unverified bilinear hypothesis here or assert methodological priority.

## 2. Excluding the tails and centering

For squarefree m=kd one has ω(m)=ω(k)+ω(d). Set s=t=c/2 in (2). In the lower tail t<1 and in the upper tail t>1; in both cases the indicator is ≤ t^(ω(m)−cℓ). Multiplication by the permitted ℓ-powers proves (1). The bivariate moment (2) can also track ω(k) and ω(d) separately if desired; no independence of Möbius signs follows.

The centered reference, with the same restriction m∈U imposed in its full target prefix, is

    Σ_{m=N−n∈U} Λ(n) μ(m)
       Σ_{K₋≤k≤min(K₊,m/α),(k,N)=1} μ(k) log(kα/m)/φ(k).

For any endpoints A₀≤B₀ of such a block, A₀≥N^(1/3) for N large. [Huang–Li Lemma 1, citing Goldston–Yıldırım](https://arxiv.org/html/2005.03811v2) bounds the partial sum Σ_{k≤u,(k,N)=1} μ(k)/φ(k) by O(exp(−c√L)) uniformly throughout the block. Partial summation against log(kα/m), of supremum and total variation O_A(1+ℓ), gives the same exponential saving up to this factor. Rounded boundaries including or excluding a single term are harmless (a boundary term is O(N^(−1/3+o(1)))). Summing against |Λ(n)μ(m)| costs O(N L), which gives the asserted O_H(N/L^H). This conclusion is valid for every set U independent of k, in particular for all the factor-count cutoffs above. Restrictions with a k-dependent sign weight may use (2) for the actual arithmetic but do not automatically share this Mertens cancellation of the centered reference.

## Precisely what remains

The bound removes a large class of real terms from a genuinely signed, individual-target estimate, including all bounded-Ω complements at the finer scale. It does not bound the band of surviving factor counts, and it does not estimate the many other sizes of k in the global divisor switch. In particular the argument cannot replace the unresolved signed distribution of Λ(n)μ(N−n) at every even target. No Goldbach proof follows.
