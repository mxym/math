# Iterated rough layers: every fixed stretched-logarithmic exponent below one

Let L=log N, ℓ=log L, η=3/2−√2. The exponent 1/9 in the single-step proofs GlobalRoughLocalization.md and SmoothSignedTransition.md is not the endpoint after stratifying the actual prime complements. For **every fixed 0<δ<1** and 0<κ<η(1−δ), the unconditional global localization (1)–(2) of GlobalRoughLocalization.md holds with y=exp(L^δ) and error O(N/L^κ). The same error controls the entire smooth signed transition to Q=√N exp(−L^δ). Thus if the literal original all-moduli, prefix-uniform EH_μ bound holds up to this Q (no ordinary EH assumed), one obtains R(N)=N S(N)+O(N/L^κ) by precisely the earlier stitching. The modulus level is still N^(1/2−o(1)), not N^(1/2−ε) with a fixed ε>0. No assertion is uniform as δ→1.

## 1. The gain from keeping preceding layers absent

Fix β<1 with δ<β, z=exp(Z), Z=L^β. Partition 0=δ₀<δ₁<⋯<δ_j=δ into finitely many layers, their number depending on δ,κ. Put Y_i=L^δᵢ and y_i=exp(Y_i), except that the first lower endpoint represents **no excluded primes**. On the layer y_{i−1}<P⁻(m)≤y_i, the small part a contains no primes up to y_{i−1} and contains at least one ≤y_i. In the first Cauchy–Schwarz bracket of GlobalRoughLocalization.md, the very same support proof now gives

    Σ_a λ^ω(a) log a/a ≪_λ Z (Z/Y_{i−1})^λ.

Indeed the Euler product includes only y_{i−1}<r≤z, with harmonic factor ≪(Z/Y_{i−1})^λ by Mertens, and the extra log a costs O(Z). At i=1 take Y₀=1. The second bracket is still at most ℓ^C Z^(2/λ)Y_i^(3−2/λ): it suffices to drop the new lower restriction from that *positive* upper bound and retain the small-prime marking at y_i. The exceptional a=r≤y_i contributes ≪Nℓ^C Y_i L/Z² by the direct calculation; it need not benefit from the new restriction. Consequently the power of L multiplying N in the main bound is

    E_i = ½[λ(β−δ_{i−1}) − 3(β−δ_i) + 2(β−δ_i)/λ].

Already the single fixed λ=√2 (so 1<2/λ<3) suffices:

    E_i = −η(β−δ_i) + (δ_i−δ_{i−1})/√2.

Given κ<η(1−δ), first fix β close enough to 1 that η(β−δ)>κ and 2β−1−δ>κ; then take the finite partition mesh small enough that E_i<−κ with strict slack. The finitely many powers ℓ^C are harmless. Summing proves the global localization for the asserted δ,κ. The proof also applies if θ=log(m/α) is replaced by θ=(log m)/2: the frozen-kernel estimates depend only on staying away from the two polynomial endpoints, and the relative m-cell argument only needs a Lipschitz function of log m. In particular the exact symmetric center is allowed; this is a proof from the relative-cell estimates, not an inference from uniformity in a scalar parameter.

## 2. Entire smooth transition with all complements retained

For the smooth block of SmoothSignedTransition.md use H=L^δ (or H bounded by a fixed multiple thereof). Its kernel f_θ has support of length O(H), is uniformly Lipschitz in u, and |hat f_θ(t)|≪min(H²,|t|^(−2)). Since H≤Z, on each layer with ω(a)≥2 the first bracket is ≪Z(Z/Y_{i−1})^λ (the previous computation also bounds the extra support length H). The same small-prime marking bounds the second bracket by ≪ℓ^C Z^(2/λ)Y_i^(3−2/λ), using only |hat f|≤O(|t|^(−2)) with the two marked factors at extremely low frequency as in the global proof. When a=r≤y_i, the Lipschitz bound gives |Σ_{e|r}μ(e)f_θ(u+log e)|≪log r and the support lies at k₀≤N^(1/2+o(1)). The direct ≪Nℓ^C Y_i L/Z² estimate again applies. The first part above now controls all marked layers of the smooth block, including arbitrary bounded complement-only masks.

For the last, unmarked layer P⁻(m)>y_j, the small Euler factors are absent from the first bracket, hence it is ≪Z(Z/Y_j)^λ. No tiny-prime marking is needed in the second bracket: use the original smooth kernel bound from SmoothSignedTransition.md, ≪ℓ^C Z^(2/λ)H^(3−2/λ). This includes a=1; its support length is O(H) and is covered by the first bracket since H≤Z. At H=L^δ this final exponent is simply −η(β−δ) for λ=√2. This proves the unconditional signed estimate for the **unmasked** smooth block for every fixed δ<1. With the original EH_μ up to Q, ordinary BV, and the original p² annihilator, the rest of the conditional argument is unchanged. A separate rough-only uncentered hypothesis, if used, must not be presumed implied by an unmasked signed bound: the actual cancellation may occur between different masks.

The proof trades a constant number of disjoint roughness layers for a log-power saving. It buys no control of the full signed residual on the final y-rough set and no actual polynomial-in-N gap below the square-root level.
