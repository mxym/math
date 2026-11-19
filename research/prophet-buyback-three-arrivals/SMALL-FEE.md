# The small-fee loss at unrestricted horizon

**Separate result; `n` is no longer fixed.** Let `α(f)` be the infimum of the optimal online expected net reward divided by the expected offline maximum over all finite independent nonnegative integrable arrival sequences in the ENNV linear-buyback model. With natural logarithms,
```
1 − α(f) = f ln(1/f) + O(f)                   (f ↓ 0).
```
Thus the leading constant in front of the natural logarithm is 1. The order `Θ(f log(1/f))`, a lower bound on `α` that already gives one side with unit leading coefficient, and the general family of indifferent instances used below are all due to [Ekbatani–Niazadeh–Nuti–Vondrák (ENNV), extended version, Lemma 3.2, Eq. (12), and Theorems 9.1 and 9.5](https://arxiv.org/html/2404.00527v3). Their §9.1 hard example has constant activation probability 1/2 and proves a loss at least `f ln(1/f)/(2 ln 2)−O(f)`. Their exact all-fee characterization via a differential equation is prior; we derive the matching small-fee asymptotic, not a new characterization over all fees.

**Upper bound on the loss (existing guarantee).** ENNV Theorem 9.5 gives, with `c=f/(1+f)`,
```
α(f) ≥ 1/[c+(2+1/f)^c].
```
Since `c ln(2+1/f)=f ln(1/f)+o(f)` and `f² ln²(1/f)=o(f)`, inversion gives `1−α(f)≤f ln(1/f)+f+o(f)`.

**Matching construction.** First fix an integer `n≥2` and choose `f=f_n=1/(n²−1)`, so `c=1/n²`. Use the following explicit independent instance, with indices `1≤i≤n`:
```
k₀=0,           kᵢ=i²/n²,            pᵢ=(kᵢ−kᵢ₋₁)/kᵢ=(2i−1)/i²,
x₀=0,           xᵢ=(n+1)i/[n(i+1)],  Xᵢ=xᵢ · Ber(pᵢ).
```
The values strictly increase to 1, `p₁=1`, and the chance that all arrivals strictly after `i` vanish is `kᵢ` by telescoping. Also
```
xᵢ₋₁/xᵢ=1−1/i²=1−c/kᵢ.
```
This is precisely ENNV's indifference condition `(xᵢ−(1+f)xᵢ₋₁)kᵢ=(1−kᵢ)fxᵢ`. Lemma 3.2 (normalization is arbitrary) gives the optimal online value `O=1−f∑_{i<n}xᵢ`. The probability that the observed maximum equals `xᵢ` is `kᵢ−kᵢ₋₁`. Writing `Hₙ=∑_{j=1}^n 1/j`, the two values are therefore exactly
```
O = 1−(n−Hₙ)/[n(n−1)],
M = (n+1)/n³ [n²−2n−3+3Hₙ₊₁].
```
The second equality follows by summing `i(2i−1)/(i+1)=2i−3+3/(i+1)`. In particular `M=1+O(1/n)` and
```
(M−O)/f_n = 2Hₙ−4+O(Hₙ/n).
```
The resulting loss is `1−O/M=f_n[2Hₙ−4+o(1)]`. Since `2Hₙ=ln(1/f_n)+2γ+o(1)`, where `γ` is Euler's constant, this proves
```
1−α(f_n) ≥ f_n [ln(1/f_n)+2γ−4+o(1)].
```

**Passage to all fees.** The offline value is fee-independent and the value of every fixed policy is nonincreasing with the fee. Thus `1−α(f)` is nondecreasing. For `f∈[f_{n+1},f_n]`, `0≤f−f_{n+1}=O(n⁻³)`; the difference between `f ln(1/f)` and `f_{n+1} ln(1/f_{n+1})` is `O(n⁻³ ln n)=o(f)`, by the derivative on this interval. Also `f_{n+1}/f→1`. Applying the last displayed lower bound at `f_{n+1}` proves the same lower estimate for arbitrary `f↓0`. Together the bounds imply the theorem. We do not determine a second-order coefficient or propose that this explicit finite instance is an exact extremizer at its fee.
