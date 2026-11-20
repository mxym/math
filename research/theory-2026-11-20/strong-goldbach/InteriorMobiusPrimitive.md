# A pointwise L¹ cancellation for the unweighted interior divisor primitive

Let N be a large even integer, L=log N, and η=3/2−√2. Fix ε∈(0,1/2). Uniformly for **one arbitrary interval** N^ε≤K₁≤K₂≤N^(1−ε), for every κ<η,

    Σ_{p<N prime} (log p) μ²(m) |Σ_{k|m, K₁≤k≤K₂} μ(k)|
       ≪_{ε,κ} N/L^κ,              m=N−p.                              (1)

In particular one need not sum dyadic upper bounds over O(log N) different modulus blocks. This includes a single interval of genuinely polynomial logarithmic width, going far below √N. Because the absolute value is inside the prime sum, any additional bounded weight depending only on m, including μ(m), is allowed. The same holds on replacing prime weight by Λ(n), with error N^(1/2+o(1)). This is not a logarithmically weighted prime detector: integrating bounds of size N/L^κ across an interval of log length comparable to L gives an insufficient bound of order N L^(1−κ).

**Proof.** Follow the small-divisor allocation and the two rough sieves in SignedBalancedTransition.md with I=[log K₁,log K₂], W=|I|≤L, Z=log z=L^β, and any fixed β<1 sufficiently close to 1. Take z=e^Z. In discarding an excessive small-prime part a, use a≤N^(ε/4) instead of N^(1/20): the same Rankin bound exp(−εL/(4Z)) handles the discarded mass. For n=p prime dividing N omit its negligible divisor-weighted contribution. For squarefree m=a b,

    |Σ_{k|m} μ(k)1_I(log k)|
      ≤ Σ_{k₀|b} |F_a(log k₀)|,
    F_a(u)=Σ_{e|a} μ(e)1_I(u+log e).

Thus the triangle inequality *per m* still preserves all small-factor signs. On the support, k₀≥N^(3ε/4) and Y=N/(a k₀)≥N^(3ε/4), so both rough-sieve steps apply with ε-dependent powers in their negligible additive errors. For the d₀ sieve the additive N^o(1) is absorbed by Y≥N^(3ε/4) before summing. No triangular moving cutoff or logarithmic weight is present. The resulting bound is N ℓ^C Z^(−2) Σ_a ||F_a||₁/a plus an error smaller than N/L^J for every fixed J, where ℓ=log L.

For a=1 the norm is W and the corresponding bound is O(N ℓ^C L/Z²). For a>1 the sum of all coefficients μ(e) is zero. Translate u in the indicator: F_a can be nonzero only within log a of one of the two endpoints of I. Indeed outside these layers the interval contains either none or all of the translated points u+log e. Hence the support measure is ≤2 log a, *independent of W*. The first Cauchy–Schwarz bracket for all a>1 is O(Z^(λ+1)). The second Plancherel bracket has Euler product **with 1 subtracted**, since a=1 has been separated:

    ∫ |hat 1_I(t)|² [∏_{r≤z}(1+|1−r^(it)|²/(λr)) − 1] dt/(2π).

For |t|≤1/Z, Σ_{r≤z}|1−r^(it)|²/r≪t² Σ(log r)²/r≪t²Z², so the bracketed difference is O_λ(t²Z²). Using |hat 1_I|≤2/|t| gives an O(Z) contribution, independent of W. For 1/Z<|t|≤1 use the low-frequency product bound in SmoothSignedTransition.md with b=2/λ>1 and integrate t^(b−2): the contribution is ≪ℓ^C Z^b. The same bound holds for 1≤|t|≤L^D, and the trivial product is O(Z^(2b)) beyond, with negligible integral for D large. Choose λ=√2. Together the two a-ranges satisfy

    left of (1) ≪ N ℓ^C (Z^(−η) + L/Z²) + O_J(N/L^J).

Choosing β<1 close to 1 proves (1). If I is a degenerate singleton one may handle its one potential divisor directly by Brun–Titchmarsh, or include the endpoint atoms in the uniform rough-sieve error as in SignedBalancedTransition.md. Finally, since the unweighted divisor sum is integer-valued, (1) gives the same log-weighted exceptional bound for actual squarefree complements on which the primitive is nonzero. This does not assert that the exceptional complements have no effect after the weight is multiplied by a factor of order log N.
