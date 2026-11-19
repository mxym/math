# How many arrivals realize the small-fee prophet loss?

**Yongxian Zhang.** Independent nonnegative integrable offers in a fixed known order, with known laws. A policy receives its final selected value minus a fee `f` times each formerly held value cancelled. Write `O` for the optimal expected net reward, `M>0` for the expected maximum, and `c_N(f)=inf O/M` over length-`N` instances. Zero padding changes neither value. A randomized policy used for a guarantee is legitimate even if the optimum is defined over deterministic policies, by averaging over its coins.

Put `c=f/(1+f)`, `L=ln(1/c)`, `m=N−1`, and `B_m=m(1−exp(−L/m))`. All logarithms are natural.

**Uniform horizon theorem.** If `N≥2` and `0<f≤1/16`, then
```
f(B_m−11) ≤ 1−c_N(f) ≤ f B_m+c.
```
In addition the leading term is a uniform **relative** equivalent:
```
sup_{N≥2} |(1−c_N(f))/(f B_{N−1})−1| → 0          as f↓0.
```

In particular, for `m=o(L)` the loss is asymptotic to `fm`, including fixed `N`. If `m/L→a∈(0,∞)`, the loss divided by `fL` tends to `a(1−exp(−1/a))`. For unrestricted finite horizon this quotient tends to 1. A horizon sequence attains this unrestricted **leading loss** in relative terms if and only if `m/L→∞`. This last assertion concerns near-extremality of the leading loss, not the least number of arrivals for an exactly tight instance at each fee. The function `a(1−exp(−1/a))` is strictly increasing from 0 to 1: its derivative is `1−(1+1/a)exp(−1/a)>0`. This also proves the necessity for sequences whose ratios `m/L` need not converge, by taking a bounded subsequence.

[Ekbatani–Niazadeh–Nuti–Vondrák (ENNV), STOC 2024](https://doi.org/10.1145/3618260.3649786) introduced this setting. Their expanded paper [§§2–3,9](https://arxiv.org/html/2404.00527v3) exactly characterizes the unrestricted guarantee for each positive fee, supplies the indifference criterion that we use, and gives both logarithmic-order small-fee loss bounds. At about `log₂(1/f)` arrivals their Theorem 9.1 gives already the corresponding hard direction at the point `a=1/ln 2`. The sharp unrestricted leading coefficient and a quadratic mesh were obtained in [the preceding note](../prophet-buyback-three-arrivals/SMALL-FEE.md). The present estimate concerns the simultaneous dependence on the horizon and fee, not a new unrestricted coefficient.

## 1. Horizon-sensitive guarantee for arbitrary laws

Write `Z=max_i X_i`. Choose a threshold `T≥0` and an independent uniform tie coin per offer so that the probability of **no pass** equals `c`. Specifically pick a quantile of `Z` with `Pr(Z<T)≤c≤Pr(Z≤T)`. An offer passes if it exceeds `T`, or if it equals `T` and its tie coin succeeds with probability `b`. As `b` runs from 0 to 1 the product of the individual failure probabilities changes continuously between the two displayed endpoints. Write `p_i` for the resulting pass probabilities. Take the first passer, and replace it by each later strictly better passer. If there is a pass then the policy finishes with `Z`, including when `Z=T`; on no pass the loss of terminal value is just `Z`. Values of `Z` on failure are no larger than those on success, so `E[Z; no pass]≤cM`.

If offer `i` incurs a cancellation fee, then it passed and was eventually replaced by something strictly larger. Thus its cost is bounded by `f 1_{i passes} max_{j≠i} X_j`. The two factors are independent; the expected fee is at most `fp_iM`. Offer `N` is never cancelled. As `∏_{i≤m}(1−p_i)≥c`, AM–GM gives `∑_{i≤m}p_i≤m(1−c^{1/m})=B_m`. This proves the upper bound on the loss. A second policy that always holds the largest value seen so far loses at most `mfZ` on every realization, so the upper bound can be reduced to
```
1−c_N(f) ≤ min(mf, fB_m+c).
```
The policies above do not need to know the arriving index, but only an order-aware worst-case objective is claimed.

## 2. A common comparison for the explicit hard instances

For any strictly increasing knots `k₁=c<k₂<…<k_N=1`, let `k₀=0`, `p_i=(k_i−k_{i−1})/k_i`, and let `X_i=x_i Ber(p_i)` independently, with `x_N=1`, `x_{i−1}=x_i(1−c/k_i)`. These scaled-Bernoulli instances and their indifference identity are ENNV's [Lemma 3.2 and (11)–(12)](https://arxiv.org/html/2404.00527v3#S3.SS2): the probability of an all-zero suffix after `i` is `k_i`, so the criterion applies, including `x₀=0,p₁=1`. Consequently `O=1−f∑_{i≤m}x_i`; summing the offline values by parts gives `M=1−∑_{i≤m} k_i(x_{i+1}−x_i)`. Write `r_i=k_i/k_{i+1}`; then
```
(M−O)/f = ∑_{i≤m}[x_i−(1−c)r_i x_{i+1}]
        ≥ ∑_{i≤m}(1−r_i)x_{i+1} − (1−x₁).
```
Here `M≤1`, and `O≤M` pathwise in the sense that every policy's realized payoff is at most the realized maximum. Thus a lower bound for `M−O` also bounds the loss `1−O/M` from below, including if the proposed lower bound is negative.

## 3. Subtracting only a constant for all horizons

First assume `N≤c^(−1/2)`. Set
```
a = (L−2 ln N)/m ≥ 0,       k_i = c i² exp(a(i−1)).
```
These are increasing and have exactly the required endpoints. Define `δ_i=ln(k_{i+1}/k_i)=a+2 ln(1+1/i)`, `λ=L/m`, and `g(t)=1−exp(−t)`. The `δ_i` have mean `λ`. On `t≥0`, `|g″(t)|≤1`. Taylor's theorem about `λ` and the least-squares property of the mean give
```
0 ≤ B_m−∑(1−r_i) ≤ (1/2)∑(δ_i−λ)²
                 ≤ (1/2)∑(δ_i−a)² ≤ 2∑_{i≥1}1/i² ≤ 4.
```
To put back the factors `x_{i+1}`, the product defining them gives
```
1−x_{i+1} ≤ ∑_{j=i+2}^N c/k_j ≤ e^(−a(i+1))/(i+1)
```
by the integral bound on the reciprocal-square tail. Also `1−r_i≤δ_i≤a+2/i`. Therefore
```
∑(1−r_i)(1−x_{i+1})
  ≤ a∑_{i≥1}e^(−a(i+1))/(i+1) + 2∑_{i≥1}1/[i(i+1)] ≤ 3:
```
the first term is at most `a/(exp(a)−1)≤1` when `a>0` and is zero when `a=0`. The endpoint loss `1−x₁≤1`. Section 2 now gives `1−c_N≥f(B_m−8)`.

For `N>c^(−1/2)` take `N′=floor(c^(−1/2))` and pad by zeros after the last offer. If `m′=N′−1`, then `m′≥exp(L/2)/2` since `exp(L/2)≥4`. Consequently
```
B_m−B_{m′} ≤ L−B_{m′} ≤ L²/(2m′) ≤ L² exp(−L/2) ≤ 16/e² < 3,
```
by `1−e^(−x)≥x−x²/2` and single-variable maximization. This proves the additive lower bound uniformly.

## 4. Why the relative assertion includes bounded horizons

For `m≥√L`, monotonicity of `B_m` in `m` gives `B_m≥√L(1−exp(−√L))→∞`; the preceding absolute constants therefore give the relative assertion uniformly in that regime. For `m≤√L`, use instead geometric knots with `r_i=r=exp(−L/m)≤exp(−√L)`, so `c/k_j=r^{j−1}`. All factors `x_i` are at least `1−∑_{j≥2}r^{j−1}=1−r/(1−r)`. Section 2 then gives
```
(1−c_N)/f ≥ m(1−r)[1−r/(1−r)]−r/(1−r).
```
Divide by `B_m=m(1−r)`, which is at least `1−r`, to get a lower ratio tending to 1 uniformly. The upper ratio is at most `m/B_m=1/(1−r)` by the greedy policy. This proves the claimed uniform relative limit.
