# The size and internal profile of an exactly extremizing indifferent instance

Fix the independent known-order linear-buyback prophet problem of ENNV and let θ=α(f) be its **unrestricted** sharp ratio. Put c=f/(1+f), K=1/c, L=ln K, ℓ=(1+f)/θ=1+η. We use the known sharp small-fee estimate θ=1−fL+O(f), equivalently ηK=L+O(1). An ENNV knot family is specified by strictly increasing `1=t₁<t₂<…<t_N=K`: put `k_i=t_i/K`, `k₀=0`, `p_i=(k_i−k_{i−1})/k_i`, `x_N=1`, `x_{i−1}=x_i(1−1/t_i)`, and independently offer `x_i Ber(p_i)`. An *extremizing family* here means that its exact ratio equals θ, not just that its loss has the correct leading asymptotic.

**Theorem.** Such extremizing knot families exist for each fee by [Ekbatani–Niazadeh–Nuti–Vondrák (ENNV), Theorem 2.9, §3.3 and Theorem 3.1](https://arxiv.org/html/2404.00527v3#S3.SS3). As f↓0 every such family has
```
N ~ (π/√2) √(K/L) ~ π/√(2 f ln(1/f)).
```
The empirical distribution with mass 1/N at each k_i tends weakly to the arcsine distribution on [0,1], with density `1/[π√(x(1−x))]`. These statements do **not** assert that no shorter general instance with different supports can be exactly worst-case. In ENNV's construction stop their inverse iteration at the *first* knot at least y(1), then append 1. If the prior point is below y(1), its inverse is strictly below 1; thus no dummy terminal knot is required. For small f the initial knot is below y(1) since c→0 and θ→1. In any case a repeated terminal knot would just pad the instance and is excluded by definition.

## 1. A prefix optimization

At a chain `1=t₁<…<t_i` define `U₁=ℓ+1` and
```
U_i = ℓ+t_i−t_{i−1}+(1−1/t_i)U_{i−1},     C_i=U_i−t_i.
```
For any full chain put M=expected maximum, O=optimal online expected payoff. ENNV's indifference lemma gives `O=1−f∑_{j<N}x_j` and `M=K^{-1}∑(t_j−t_{j−1})x_j`, where t₀=0. Expanding the recurrence gives `U_N=ℓ∑x_j+KM`, hence
```
U_N−ℓK = K(M−O/θ).
```
Indeed `Kf/θ=ℓ` and `K/θ+ℓ=ℓK`. Therefore all chains have `U_N≤ℓK` and equality is attained by each extremizer. Every prefix of any extremizer maximizes U_i among **all finite chains with the same endpoint**, not just among chains of length i: replacing a prefix changes U_N by that prefix increment times the positive product of subsequent factors `1−1/t_j`.

Uniformly at all such prefix points (and all sufficiently large K) we have
```
C_i = ln t_i + O(1).                                  (1)
```
For the upper estimate the recurrence reads `C_i=η+(t_i−s)/t_i+(1−1/t_i)C_{i−1}`, s=t_{i−1}. Take a constant D large enough that `ln t+D−ln 2≥ηt` throughout [1,K]: concavity of `ln t−ηt` reduces this to 1 and K, where it follows from ηK=L+O(1). Suppose C_{i−1}≤ln s+D. If s≥t/2, `(ln s+D)/t≥η` and `ln(t/s)≥(t−s)/t`. If s<t/2, `ln(t/s)−(t−s)/t≥ln 2−1/2>η` for large K. These prove C_i≤ln t_i+D by induction, enlarging D to cover t₁=1.

For the lower estimate ℓ≥1, so it suffices to construct a prefix at the smaller coefficient 1. For t≥16 let n=floor √t, m=n−1, `a=(ln t−2ln n)/m≥0`, and t_j=j²exp(a(j−1)). Put `z_n=1, z_{j−1}=z_j(1−1/t_j), r_j=t_j/t_{j+1}`. By telescoping the prefix recurrence at ℓ=1 its excess over t equals
```
1+∑_{j<n}(z_j−r_j z_{j+1})=z₁+∑_{j<n}(1−r_j)z_{j+1}.
```
For completeness this is at least ln t−10. Indeed the log steps δ_j=a+2ln(1+1/j) have mean h=(ln t)/m. Taylor's theorem for g(u)=1−exp(−u) gives `m g(h)−∑(1−r_j)≤(1/2)∑(δ_j−a)²≤2∑j^{-2}≤4`. Also `1−z_{j+1}≤exp(−a(j+1))/(j+1)` by the reciprocal-square sum after j+1; multiplying by `1−r_j≤a+2/j` and summing costs at most 3 (use a/(e^a−1)≤1, interpreted by continuity). Finally `ln t−m g(h)≤(ln t)²/(2m)≤(ln t)²/√t<3` since m≥√t/2. For t<16 the lower bound with an absolute error is immediate from nonnegative C (e.g. the recurrence). This proves (1).

## 2. Local variation of a maximizing chain

Write d_i=t_i−t_{i−1} for 2≤i≤N. For each interior point `u=t_i` with neighbors `s=t_{i−1}, v=t_{i+1}`, differentiate its contribution to U_{i+1}, holding the earlier prefix and later knots fixed. Strict increase makes this a two-sided variation. The derivative is `(1−1/v)(1+U_{i−1}/u²)−1=0`. Thus
```
v=1+u²/(s+C_{i−1}),                        (2)
d_{i+1}−d_i=1−C_{i−1}+(d_i−C_{i−1})²/(s+C_{i−1}).
```
Removing that knot cannot improve the full-chain objective. More generally the effect, in units of U at v, of inserting u between consecutive s,v is
```
[(v−1)(ℓ−U(s)/u)−(u−s)]/v.                 (3)
```
Here U(s) means the value of the prefix ending at s. Formula (3) follows by substituting the recurrence twice. Where u is already present this quantity is nonnegative; if no knot is present it is nonpositive for every intermediate trial u. For an existing interior knot (2) gives the useful removal consequences
```
s+ℓ(v−1) ≥ 2√((v−1)(s+C_{i−1})),
ℓ d_{i+1} ≥ d_i+ℓ−ηu.                      (4)
```
For consecutive points s,v with v−1>s, test the missing knot `u=√(s(v−1))` in (3). Write R=√((v−1)/s)>1. This gives
```
s(R−1)²+η(v−1) ≤ C(s)R.                     (5)
```
Hereafter constants in O-bounds are absolute unless indexed by a fixed ε>0. In particular (1),(5) imply for every step starting at s that
```
v−s ≤ O(1+√(s(1+ln s))).                    (6)
```
Indeed `R+R^{-1}−2≤C(s)/s` bounds R by an absolute constant and then bounds R−1 by `O(√((1+ln s)/s))`. Steps v−1≤s are trivial. In particular t₂ is bounded absolutely.

One further endpoint variation is needed. Append a second terminal K: its activation is zero; the recurrence gives `ℓ+(1−1/K)U_N=ℓK`. Holding the added terminal fixed, move the old last point from K to the left. Since no strictly ordered chain can do better, the left derivative at K is nonnegative:
```
(1−1/K)(1+U_{N−1}/K²)−1≥0,  hence U_{N−1}≥K²/(K−1).
```
In particular `d_N=O(L)` by (1). For large K there must be intermediate points by (6); all following estimates concern this regime.

## 3. Bulk gap profile by a discrete energy identity

First record `N=O(K^{3/4})`. Below √K inequality (4) forces `d_{i+1}≥1/3` for large K, because η√K=o(1). Above √K at most K^{3/4} steps can have gap >K^{1/4}. Once a step ending above √K has d_i≤K^{1/4}, its starting point is at least √K−K^{1/4}. By (1) the C at that point is between (1/3)L and O(L). In (2) the square divided by s+C is then bounded absolutely, so subsequent gaps drop by at least 1 as long as the chain continues. There are at most 1+K^{1/4} such subsequent gaps. This proves the crude bound.

Let `v_i=(d_{i+1}−1)/t_i` for 1≤i<N. Unlike d_i this velocity need not be positive. In adjacent interior steps (2) gives the exact identity
```
v_{i−1}−v_i = [C_{i−1}(1+v_i)−1]/t_{i−1}  (2≤i≤N−1).  (7)
```
For the terminal value, `v_{N−1}=O(L/K)` by the endpoint estimate. Fix ε>0; write s=t_{i−1}, u=t_i. For all s≥εK, (6) gives `|v_i|+|v_{i−1}|=O_ε(√(L/K))`, and (1) gives `C_{i−1}=L+O_ε(1)`. Thus the numerator of (7) is `L(1+o_ε(1))` uniformly. Put `w_i=√(K/L)v_i`. Squaring (7) in difference form gives
```
w_{i−1}²−w_i² = [2+o_ε(1)] (K/s²)(u−s) + O_ε(L/K).     (8)
```
Indeed, write `v_{i−1}²−v_i²=2v_{i−1}(v_{i−1}−v_i)−(v_{i−1}−v_i)²`, use `v_{i−1}=(u−s−1)/s`, and bound the subtracted square using (7); the missing 1 in u−s costs O_ε(1/K) after normalization. The summed additive error tends to zero since N=O(K^{3/4}). By (6) the mesh in coordinates `t_i/K` has vanishing maximal diameter; `t_{N−1}/K→1`. Hence summing (8) to the endpoint, using `w_{N−1}²=O(L/K)`, gives by Riemann sums, uniformly for t_i≥εK,
```
w_i² = 2(K/t_i−1)+o_ε(1).                              (9)
```
Since v_i≥−1/t_i, its negative part after normalization tends to zero there. On each fixed compact subinterval of (0,1), if x_i=t_i/K,
```
d_{i+1}/√(KL) = √(2x_i(1−x_i))+o(1)                   (10)
```
uniformly. Counting gaps by the Riemann sum of the reciprocal of the right-hand profile shows that, for fixed `0<a<b<1`,
```
(#{i : a≤t_i/K≤b}) / √(K/L) → ∫_a^b [2x(1−x)]^(−1/2) dx.  (11)
```
Intervals crossing the boundary of [a,b] cost at most two points.

## 4. No escaping mass at either end

We provide estimates with absolute implied constants for all sufficiently small **fixed** ε>0, taking K→∞ before ε↓0.

*Lower end.* At two steps from s=t_{i−1} to v=t_{i+1}, if `s≤εK`, then for all large K, (4) ensures `d_i+d_{i+1}>1` when s and K are large enough **or** the following argument applies directly to the absolute difference. In fact no monotonicity assertion about v−1 versus s is needed: when v−1<s one has `0<s−(v−1)<1`. If v−1≥2s the two-step span is already ≥s. In the remaining case, v−1∈(s−1,2s), and (4) gives
```
(√(v−1)−√s)² ≥ 2√(v−1) C(s)/(√(s+C(s))+√s) − η(v−1).
```
For s≥s₀ large enough, (1) makes the first term ≥(1/2)ln s. Uniformly on s∈[s₀,εK], for fixed ε<1/32 and large K we have `2ηs≤(1/4)ln s`: use that s/ln s increases for s>e and ηK=L+O(1). Thus the left side is at least (1/4)ln s, ruling out v−1<s and implying
```
v−s ≥ c₀√(s ln s)
```
with an absolute c₀>0. Count alternate indices in dyadic bins [T,2T), T≥s₀. Each bin contains O(1+√(T/ln T)) points: except for at most two exits, the two-step spans fit in its length. Below fixed s₀ there are only O(s₀) points by (4) for large K. Summing the geometric bins through √K gives O(K^{1/4} log K), negligible compared with √(K/L). Up to εK above √K use ln T≥L/2−O(1); summing the resulting geometric series gives O(log K+√(εK/L)). The limsup of the normalized lower-end count is O(√ε).

*Upper end.* For consecutive knots s,v with s≥(1−2ε)K, (5) and (6) give `R=1+O(√(L/K))` when v−1>s and hence
```
s(R−1)² ≤ (L+O(1))R−η(v−1) ≤ (2ε+o(1))L.
```
Thus `(v−s)²/s≤(8ε+o(1))L`; the same estimate holds trivially for v−s≤1. For such a step of size d_i starting at s, C(s)=L+O(1) and `C(s)/√(sL)→0`. Consequently (2) gives `d_{i+1}−d_i≤−L/2` for all sufficiently small fixed ε and all large K. The initial gap in that region is O(√(εKL)); (6) ensures that the region is reached before (1−ε)K. The positivity of all remaining d's bounds their number by O(1+√(εK/L)). Thus the upper-end normalized limsup is again O(√ε).

Let ε↓0 in (11) and these estimates. The integral over (0,1) equals π/√2. Dividing the compact-interval counts by the total gives the asserted arcsine law.
