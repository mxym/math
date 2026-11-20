# A central-window lower bound on exact periodic prime-power masks

This addendum strengthens the lower bound in [OptimalDensePrimePowerWheel.md](OptimalDensePrimePowerWheel.md). It is an obstruction for periodic masks, not for nonperiodic removal of known powers and not for strong Goldbach.

Fix 0<α<1/2, N sufficiently large, and an interval I=(U,V] contained in [αN,(1−α)N]. Let L=log N and Γ=log(V/(V−U)). Suppose a periodic mask modulo W accepts at least one unit class and rejects every actual pʲ∈I, with p prime and j≥2. There is an effective constant such that
    log(2W) ≫_α L / (√L+Γ).
In particular if |I|≥N exp(−D√log N) for a fixed D>0, log W≫_{α,D}√log N. The companion construction, which excludes even all prime powers up to N, attains the same order of log W in this entire range of window sizes.

**Primary input.** [Thorner–Zaman, Theorem 1.1 and (1.7)–(1.8), arXiv:2108.10878v2](https://arxiv.org/pdf/2108.10878v2), [published in Math. Z. 306, 54 (2024)](https://doi.org/10.1007/s00209-023-03414-3), imply that for some sufficiently small effective η>0 and large effective x₀, every reduced class modulo any 2≤q≤x^η has a prime in every (x−h,x] with x≥x₀ and x^{1−η}≤h≤x. Indeed choose ε fixed and η so (5/2)η<1−32/37−ε in (1.8), even allowing the exceptional zero. The theorem's relative error is O_ε(exp(−c_ε log x / D(x,h,q))) where
    D(x,h,q)=log q+(log(x/h))^{2/3}(log⁺log(x/h))^{1/3}
                    +(log x)^{2/5}(loglog x)^{1/5}
             ≤ η log x+o(log x).
Choose η smaller and then x₀ larger to make that relative error <1/2. The main term is strictly positive by (1.7) when an exceptional zero exists.

**Argument.** Put q=2W and P=log q, and lift an accepted unit class to any reduced class a modulo q. Let
    T=floor(c L/(P+Γ+log L))
for a sufficiently small absolute effective c>0. For a prime k≤T put x=V^{1/k}, y=U^{1/k} and h=x−y. By concavity of u^{1/k},
    h/x = 1−(U/V)^{1/k} ≥ (V−U)/(kV),
    log(x/h) ≤ Γ+log k ≤ Γ+log L.
Uniformly for k≤T, log x ≥ (P+Γ+log L)/(2c) for large N. In particular x≥x₀, q≤x^η and h≥x^{1−η} if 2c≤η. If k fails to divide φ(q), the k-th power map on the unit group modulo q is bijective; its root of a has a prime in (y,x] by the primary input. The resulting pᵏ∈I then belongs to the accepted class modulo W, a contradiction. Every prime k≤T must therefore divide φ(q). For sufficiently large T, Chebyshev gives P≥log φ(q)≥Σ_{k≤T}log k≫T, with the sum over primes. For bounded T the definition gives P+Γ+log L≫L and P≥log 2. In both cases P(P+Γ+log L)≫L. If P≥√L the claim is immediate; otherwise P+Γ+log L≤2√L+Γ for large L. In the stated shrinking-window consequence this forces P→∞ and hence the same lower bound on log W.

This proof concerns an entire filled interval of accepted positions, not a sparse set of isolated probe nodes or an arithmetic certificate that explicitly subtracts prime powers. It holds without presupposing real prime pairs or the Li–Liu spectral hypotheses.
