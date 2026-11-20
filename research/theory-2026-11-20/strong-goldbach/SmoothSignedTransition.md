# The smoothed signed transition to square-root times exp(−(log N)^δ), δ<1/9

This companion extends SignedBalancedTransition.md. The new estimate is unconditional for the signed **smooth** cutoff. Reduction to a Hardy–Littlewood asymptotic remains conditional on a specific Möbius-twisted distribution estimate at smaller moduli. We make no first-in-literature claim.

Use L=log N, ℓ=log L, 0<β<1 fixed, Z=L^β, z=e^Z. Let 1≤H≤Z, H=o(L), and fix A≥1. Let log Q and log α both lie within AH of (log N)/2. Define ψ(x)=0 for x≤−1, ψ(x)=1+x for −1<x<0, ψ(x)=1 for x≥0. Set g(k)=ψ((log k−log Q)/H), so g vanishes below Qe^(−H) and equals one for k≥Q. The centered and uncentered signed triangular block with weight g(k), and implicit k<N/α as in SignedBalancedTransition.md, is bounded for any fixed 2/3<λ<∞ by

    ≪ N ℓ^C Z^((λ+1+2/λ)/2−2) (1+H)^((3−2/λ)/2)
        + O_J(N/L^J)                                                   (1)

for arbitrary fixed J (choose the mesh precision in the proof accordingly). Constants may depend on λ,β,A,J. Unlike a sharp truncation at an interior boundary, the lower cutoff is continuous. Only the **complement** 1−g is subject to any hypothesized distribution, and it is supported at k≤Q.

## 1. Relative cells in the prime sieve: sum their lengths, not their number

Separate m=N−p into small and rough parts m=a k₀ d₀ as in SignedBalancedTransition.md; the prime power, p|N, small p, and excessive small part a>N^(1/20) exceptions satisfy the same negligible bounds even after multiplying by the log weight O_A(H). After allocating k=e k₀, the small divisors carry the sign μ(e). Write θ=log(m/α). For fixed θ the kernel in the log k variable u is

    f_θ(u)= ψ((u−log Q)/H) min(0,u−θ).

Whenever nonzero its support is [log Q−H,θ], of length O_A(H) and height O_A(H). This is piecewise quadratic with a bounded number of pieces. Its first derivative has total variation bounded by O_A(1): on the ramp the second derivative is bounded by 2/H, and every corner has a bounded derivative jump. Hence uniformly

    |hat f_θ(t)| ≪_A min(H², |t|^(−2)).                              (2)

Ignore targets m with θ<log Q−H since they contribute nothing. Partition the remaining m by log m into intervals of width at most ε=L^(−D), where D can be arbitrarily large fixed. Their number is O_A(1+H/ε). In each replace θ by its value θ_j at the upper endpoint, keeping m in the **same arithmetic interval** J_j. Pointwise the replacement changes f by at most ε. The resulting error summed over all individual prime/divisor terms is ≪ε N(1+H) by Brun–Titchmarsh and Σ_{a<k≤b}1/φ(k)≪1+log(b/a) in the admissible k-range. The single possible sliver beyond k=N/α is harmless: at every frozen upper endpoint θ_j≤log(N/α), the kernel is still zero past that endpoint. Alternatively, retaining only p∤N throughout removes all nonunit residue classes.

For fixed a,k₀,j the admissible d₀ lie in the interval J_j/(ak₀). The Bonferroni-sieve proof of (2) in SignedBalancedTransition.md counts that interval, not necessarily an initial segment. It therefore gives, with the same uniform constants,

    Σ_{d₀ in J_j/(ak₀), d₀ z-rough, N−ak₀d₀>w prime} log(N−ak₀d₀)
       ≪ ℓ^C |J_j|/(ak₀ Z) + N^o(1),                                (3)

where |J_j| denotes its ordinary length in m, not in log m; log factors in the additive error have been absorbed. The additive term, summed over all cells, a≤N^(1/20) and k₀≤N^(1/2+o(1)), costs N^(3/5+o(1)) or less even with the divisor/log weights. Crucially **Σ_j |J_j|≤N**.

Define F_{a,j}(u)=Σ_{e|a} μ(e) f_{θ_j}(u+log e). The k₀-rough estimate (4) of SignedBalancedTransition.md applies as well with additive error O(H τ(a)² N^(−2/5+o(1))). Indeed F is piecewise quadratic on O(τ(a)) pieces and of height O(Hτ(a)); |F| has O(τ(a)) monotonic pieces. On each, the product with 1/k₀ can instead be integrated by first using partial summation with 1/k₀ on subintervals and then using the layer-cake formula for the monotone |F|. This gives the main integral (1/Z)∫|F|du, with the stated additive bound. Combining (3) with that estimate bounds the signed sum by

    N ℓ^C/Z² · max_j Σ_{a squarefree,z-smooth} ||F_{a,j}||₁/a
      + O_J(N/L^J).                                                    (4)

The maximum comes *after* relative interval lengths are summed; there is no pointwise supremum over translations inside the norm.

## 2. The Euler product at frequencies smaller than one

The support Cauchy–Schwarz bound of SignedBalancedTransition.md gives a first bracket ≪Z^(λ+1) since H≤Z. In the second Plancherel bracket use the following refinement, uniformly for |t|≤L^D' with any fixed D':

    ∏_{p≤z}(1+|1−p^(it)|²/(λ p))
        ≪ ℓ^C (1+Z min(1,|t|))^(2/λ).                               (5)

For |t|≥1 this is already proved there. For 0<|t|<1 the integrated prime number theorem from exp(ℓ^4) gives the lower bound

    Σ_{p≤z} cos(t log p)/p ≥ log min(Z,1/|t|) − O(log ℓ).

Indeed on the part v≤1/|t| of the comparison integral ∫cos(tv)dv/v use 1−cos(tv)≪t²v²; on the rest the integral is bounded uniformly by integration by parts. Omitting the initial part v≤ℓ^4 loses at most O(log ℓ), including when 1/|t|<ℓ^4. At t=0 the product equals 1. Mertens and |1−p^(it)|²=2−2cos(t log p) prove (5).

Write b=2/λ∈(0,3). By (2), (5), the second bracket is bounded by

    ≪ ℓ^C Z^b (1+H)^(3−b).

Explicitly, for |t|≤1/Z the contribution is O(ℓ^C H^4/Z), which fits since H≤Z. For 1/Z<|t|≤1 use Z^b∫min(H^4,t^(−4))t^b dt≪_b Z^b H^(3−b) (split at 1/H). At 1<|t|≤L^D' integrate t^(−4); outside use the crude product O(Z^(2b)) and take D' large. Cauchy–Schwarz and (4) yield (1). For the centered reference, on any fixed m the weight g(k) log(αk/m) on the triangular prefix has total variation O_A(H), so the same exponential Mertens saving applies at k≥N^(1/3).

## 3. Verified range as a conditional consequence

If H=L^δ with 0<δ<β, the exponent of L in (1), ignoring ℓ^C, is

    ½[βλ − 3(β−δ) + 2(β−δ)/λ].

Take λ=√(2(β−δ)/β). This is >2/3 throughout δ≤β/9. The displayed exponent is negative exactly when δ<β/9. Thus for **any fixed δ<1/9, δ>0**, setting Q=√N exp(−L^δ), the sole conjectural input E(N,Q)≪_J N/L^J at the same even target (all moduli, all prefixes as in Huang–Li) suffices, with known ordinary Bombieri–Vinogradov, for

    R(N)=N S(N)+O_{δ,κ}(N/L^κ),
    0<κ<[3(1−δ)−2√(2(1−δ))]/2.                                      (6)

Proof: let β approach 1 but then fix it to preserve strict inequalities. Set α=√N/L^D for fixed large D and B=L² in the small-divisor truncation, as in SignedBalancedTransition.md. For large N, Dℓ≤H, so hypotheses with fixed A apply. In the twisted part apply distribution only with coefficient 1−g(k) at moduli k≤Q; this is a constant in n of absolute value at most one, so it does not increase the sum of absolute prefix errors. Formula (1) bounds the **entire** complementary g-weighted part, including its reference. The literal all-moduli hypothesis again absorbs the total twisted mean via one annihilating prime-square modulus. This gives (6). This note narrows an *unproved twisted* input, not ordinary BV or the classical Goldbach conjecture. It gives neither a power-of-N level improvement nor an estimate for all smaller twisted moduli. For BV-style fixed polylogarithmic log losses use the earlier note or H=O_D(ℓ). No unrestricted pointwise prime-pair asymptotic is claimed.
