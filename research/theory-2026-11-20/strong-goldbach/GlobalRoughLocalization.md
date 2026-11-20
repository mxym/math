**Stronger cutoff:** [rough-layer iteration](RoughLayerIteration.md) extends the fixed stretch exponent to every `0<δ<1` with a positive, δ-dependent log-power saving.

# Unconditional localization of the entire signed Goldbach switch to rough complements

This is an **individual-target** result for the full logarithmically weighted Möbius divisor switch, not merely its balanced block or its unweighted primitive. It does not estimate the remaining signed sum on rough complements. In particular it does not prove Goldbach positivity.

Let N be even, L=log N, ℓ=log L, and fix 0<δ<1/9. Put Y=L^δ and y=exp(Y); P⁻(1)=∞. Let ε₀>0 be fixed and N^ε₀≤α≤N^(1−ε₀). Define the full triangular kernel

    K_α(m)=Σ_{k|m} μ(k) min(0,log(αk/m)).

For every 0<κ<[3(1−δ)−2√(2(1−δ))]/2, uniformly at each sufficiently large even N,

    Σ_{p<N, p prime, P⁻(m)≤y} (log p) μ²(m) |K_α(m)|
       ≪_{δ,κ,ε₀} N/L^κ,                     m=N−p.                  (1)

The absolute value is taken *per complement* after its small-prime allocations, not after summing over targets. This permits bounded extra weights depending on m. The same bound holds with Λ(n) for n<N, with a negligible proper-prime-power correction.

In particular, let R(N) count ordered prime pairs with their two log weights and S(N) denote the usual Goldbach singular series. For some sufficiently large **fixed** D choose α=√N/L^D. Then, without any conjectural input,

    R(N) = N S(N) +
           Σ_{n<N, P⁻(m)>y} Λ(n) μ(m) K_α(m) + O_{δ,κ}(N/L^κ),
              m=N−n.                                                   (2)

This is a signed remainder, not a positive lower bound. Its support among the n's has unconditional total Λ-weight ≪ N ℓ^C/L^δ. And when μ(m)≠0 every modulus k|m occurring there is automatically squarefree and y-rough. These statements do not make the remainder negligible: K_α can have size comparable to log N even on prime m.

## 1. Per-complement reallocation and compact support

For the sieve details invoked below see SignedBalancedTransition.md §§1–2 and SmoothSignedTransition.md §1. Choose a fixed β∈(δ,1) sufficiently close to 1 at the last optimization, Z=L^β, z=exp(Z). For squarefree m write m=a b, with a the product of its primes ≤z and b z-rough. Omit proper prime powers n, primes dividing N, and p≤w=exp(L/ℓ²) at N^(1/2+o(1)) total cost, using the divisor bound and the extra log weight. Trivially m≤N/L^D₁ has cost ≪N/L^(D₁−3) by Σ_{m≤x}τ(m)≪x log(2x). Take fixed D₁ large. The Rankin estimate of SignedBalancedTransition.md with cap a≤N^(ε₀/4) removes larger a at O_J(N/L^J) for every fixed J. These steps apply before any new sign cancellation.

Let θ=log(m/α), f_θ(u)=min(0,u−θ). For k=e k₀ with e|a, k₀|b, write

    F_{a,θ}(u)=Σ_{e|a} μ(e) f_θ(u+log e),
    |K_α(m)| ≤ Σ_{k₀|b} |F_{a,θ}(log k₀)|.                          (3)

If ω(a)≥2, both Σ_{e|a}μ(e)=0 and Σ_{e|a}μ(e)log e=0, the second identity being the vanishing of Λ(a) for squarefree composite a. Thus F is compactly supported in [θ−log a, θ]: outside, its terms either all vanish or agree with a single affine function. It is piecewise linear, with O(τ(a)) pieces, and has height O(L τ(a)) in the present ranges. With m≥N/L^D₁, the support ensures k₀≥N^(ε₀/2), and X=N/(ak₀)≥N^(ε₀/2) also holds.

Partition log m into cells of width L^(−D₂), with D₂ large and the total number polynomial in L, and freeze θ at each upper cell endpoint θ_j. Since f is 1-Lipschitz in θ, the aggregate freezing error is ≪N L^(2−D₂) by summing divisor counts times log p. Apply the relative-cell d₀ sieve to d₀=b/k₀, where p=N−ak₀d₀ and m lies in its original arithmetic cell J_j. It yields (with prime log weight) ≪ℓ^C |J_j|/(ak₀ Z)+N^o(1). Here the number of a,k₀ pairs in additive errors is at most N^(1−3ε₀/4+o(1)), since a≤N^(ε₀/4) and k₀≤N/α. Next, the rough k₀ sieve gives (1/Z) times the integral in u of |F_{a,θ_j}(u)| with additive O(Lτ(a)^2 N^(−ε₀/2+o(1))) as in the earlier notes. Summing this last error with 1/a divisor weights remains negligible. Since Σ_j |J_j|≤N and θ translates F without changing any of its norms, (1) on ω(a)≥2 reduces to

    (Nℓ^C/Z²) Σ_{a squarefree,z-smooth, ω(a)≥2, P⁻(a)≤y} ||F_{a,0}||₁/a
       +O_J(N/L^J).                                                     (4)

Translation does not permit dropping the initial m-cell constraint without counting its length; the relative-cell estimate is used before (4).

## 2. At least one small prime kills the low-frequency singularity

The Fourier transform satisfies, for t≠0,

    |hat F_{a,0}(t)|=|t|^(−2) ∏_{r|a}|1−r^(it)|.

Indeed the distributional second derivative of each translated min(0,u) is a signed unit point mass; F is compactly supported, so there are no polynomial/delta terms to add to its Fourier transform. The support bound and weighted Cauchy–Schwarz give a first bracket ≪ Z^(λ+1) for fixed λ>0 as before. Choose 1<b=2/λ<3. The second bracket, up to normalization, is

    ∫ |t|^(−4) Σ_{a in (4)} ∏_{r|a} [|1−r^(it)|²/(λr)] dt.

Let P(t) denote the unrestricted Euler product ∏_{r≤z}(1+|1−r^(it)|²/(λr)). From SmoothSignedTransition.md (5), for |t|≤L^D this is ≪ℓ^C(1+Z min(1,|t|))^b. Write x_r=|1−r^(it)|²/(λr). The restricted sum in the integral is at most P(t), and also at most P(t) Σ_{r≤y}x_r, by marking one small prime. Since ω(a)≥2, it is further bounded by P(t)(Σ_{r≤y}x_r)(Σ_{s≤z}x_s): mark a small prime and one *different* prime, then enlarge the outer sums. Whenever |t|≤1/log u, Σ_{r≤u}x_r≪_λ t²(log u)² by |1−r^(it)|≤|t|log r.

* For |t|≤1/Z, P(t)≪1 by the direct quadratic estimate. The restricted sum is O(t^4Y²Z²), so this range contributes O(Y²Z)≪Z^bY^(3−b), using b>1 and Y≤Z.
* For 1/Z<|t|≤1/Y, the small-prime marking and (5) bound the integral by ≪ℓ^C Z^bY² ∫_0^(1/Y) t^(b−2)dt≪ℓ^C Z^bY^(3−b).
* For 1/Y<|t|≤1, integrate t^(b−4), and for 1≤|t|≤L^D integrate t^(−4). Beyond use P(t)≪Z^(2b) and choose D large. These ranges satisfy the same bound.

Consequently (4) is ≪ Nℓ^C Z^((λ+1+2/λ)/2−2)Y^((3−2/λ)/2)+O_J(N/L^J).

## 3. The sole small-prime part a=r

If ω(a)=1 and P⁻(a)≤y, then a is a prime r≤y. Although F_{r,θ}(u) need not be compactly supported below θ, the Lipschitz property gives |F|≤log r, and F=0 for u>θ. In particular k₀≤N/α. Sum directly over the z-rough k₀,d₀: X=N/(rk₀)≥α/r≥N^(ε₀/2), so the rough d₀ plus prime sieve bounds its log-weighted count by ≪Nℓ^C/(rk₀ Z), without needing k₀ itself large. Mertens gives

    Σ_{k₀≤N, k₀ z-rough} 1/k₀ ≤∏_{z<s≤N}(1−1/s)^(−1) ≪ L/Z,
    Σ_{r≤y prime} (log r)/r ≪ Y.

Thus this part costs ≪N ℓ^C YL/Z². If a=1 no small prime divides m and there is no contribution to (1).

## 4. Consequences and residual barrier

Take λ=√(2(β−δ)/β), so 1<2/λ<3 when β is sufficiently close to 1. The exponent from §2 is −[3(β−δ)−2√(2β(β−δ))]/2. The exponent from §3 is 1+δ−2β, which tends to −1+δ and is smaller than the desired negative exponent. Fix β close enough to 1 to absorb ℓ^C and obtain (1).

For (2), the centered divisor decomposition in CenteredDivisorSwitch.md gives R=S₁+Σ Λ(n)μ(m)K_α(m)+negligible terms; this identity does not use any twisted distribution. With B=L² and D large fixed, the O(N/B) tail and ordinary Bombieri–Vinogradov unconditionally give S₁=NS(N)+O(N/L²). Estimate (1) then gives (2). To bound the remaining support, sieve n so that n avoids 0 mod r for r≤w (apart from n≤w) and N−n avoids 0 mod r for r≤y. The same elementary two-condition Bonferroni/CRT argument yields the total Λ-weight ≪Nℓ^C/Y, including the factors from primes dividing N and negligible proper prime powers. Since y=exp(L^δ), the actual weighted proportion tends to zero, although the critical signed sum over it remains unbounded on the required scale.

For an optional precise restricted sufficient hypothesis, choose any fixed 0<δ'<1/9, Q=√N exp(−L^δ'). It suffices for eventual positivity that for some fixed η'>0 the sum over **y-rough squarefree k≤Q coprime to N**, including k=1, of the maximum over x<N of

    |Σ_{n≤x, n≡N mod k, P⁻(N−n)>y} Λ(n) μ(N−n)|

is O(N/L^(1+η')). Indeed partial summation against the triangular log on the 1−g(k) part costs O(L); the g(k) part is o(N) unconditionally by SmoothSignedTransition.md, whose reallocation estimates permit any bounded complement-only mask (here P⁻(m)>y). Unlike the global centered all-modulus hypothesis, this is an *uncentered* bound on the sparse sequence in (2). No implication in either direction between this restricted hypothesis and a differently centered EH conjecture is being asserted. The formal restriction may be useful, but (1) and (2) are the unconditional results; the restricted parity estimate is not proved.
