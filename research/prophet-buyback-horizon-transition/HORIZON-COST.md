# Two scales of near-attainment

In the notation of the uniform horizon theorem, let `α(f)=inf_{N≥2}c_N(f)`. Because `B_m↑L` for each fixed fee, the additive inequalities give
```
1−α(f)=fL+O(f),       c_N(f)−α(f)=f(L−B_m)+O(f),
```
with absolute implied constants independent of the fee and horizon as `f↓0`. The first display's unrestricted estimate is prior; the second is its finite-horizon consequence here.

If `L≪m≪L²`, expand `exp(−L/m)` at zero to get `L−B_m=L²/(2m)(1+O(L/m))`. Since `L²/m→∞`, it follows that `c_N(f)−α(f)∼ f L²/(2m)`. More generally, for an arbitrary horizon sequence
```
c_N(f)−α(f)=O(f)   if and only if   m=Ω(L²).
```
Indeed the additive comparison implies that the left-hand side is equivalent to bounded `L−B_m`. If `m≥bL²` this quantity is at most `L²/(2m)≤1/(2b)`. Conversely, bounded `L−B_m` first forces `L/m→0`, since `1−(1−exp(−u))/u` is strictly positive, increasing on `u>0`; then the expansion yields bounded `L²/m`. Contrast this quadratic scale with the merely superlogarithmic horizon necessary and sufficient for ratio 1 of the *leading losses*. Neither comparison proves that any given horizon attains the exact unrestricted optimum at a particular positive fee.
