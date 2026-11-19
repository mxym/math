# The sharp prophet inequality with linear buyback at horizon three

**Yongxian Zhang.** Research manuscript. AI-assisted; mathematical review and priority status are distinct from external peer review.

## 1. Statement and prior work

Three independent nonnegative random variables of finite means arrive in a fixed order known to the policy, with known laws. Upon each observation the policy may keep its current choice, or replace it and pay a charge equal to a fixed fraction `f` times the discarded choice (no fee for an initial acceptance). It receives the final choice minus all such charges. Let `O` be the largest expected net reward and `M` the expected maximum of the three observations. Write `c₃(f)=inf O/M` over these instances with `M>0`. This is a ratio of expectations, not an expected samplewise ratio.

**Theorem.** For `0<f<1`, let `a=1+f` and `s=√(f(2−f))`. Then
```
c₃(f) = a(1+s)/(1+3f+a s).
```
At `f=0` the value is 1, and for `f≥1` it is the already known `a/(1+2f)`.

The upper bound and the attaining instance for every `0<f<1` are due to [Ekbatani, Niazadeh, Nuti and Vondrák (ENNV), STOC 2024, §§1,4](https://arxiv.org/html/2404.00527v1#S4.SS1). They explicitly conjectured equality for horizon three. Their [2026 extended paper, §§2,3.1, Eq. (10)](https://arxiv.org/html/2404.00527v3#S3.SS1) characterizes the unrestricted-horizon factor for every fee, and proves that their three-variable extremizer is optimal even without a horizon bound for `1/3≤f≤1`. Thus the additional regime here is **fixed horizon three and `0<f<1/3`**. Their general scaled-Bernoulli reduction (§2.1, Lemma 2.3) may increase the number of arrivals. Below the reduction is instead kept within three. We claim neither a new unrestricted-horizon result nor an order-agnostic policy attaining the stated fixed-horizon value.

## 2. Reduction without increasing the horizon

The exact dynamic program is ENNV's. Two arrivals already guarantee `c₂=a/(1+2f)` (ENNV 2024, App. C); a short bound useful here is as follows. With two observations `y,z`, choose the first with probability `c₂`, independently, then use the better final option. The conditional expected reward over the coin is
```
c₂ max(y,z−fy)+(1−c₂)z ≥ c₂ max(y,z).
```
For `y>0` scale it to 1: the difference is piecewise affine with knots `0,1,a`, nonnegative at the knots, and nondecreasing after the last. The assertion for `y=0` is immediate. For `0<f<1`, `c₂` is at least the displayed three-arrival factor, since `s≤1` and the scaled excess `a(1/c₂−1)=f≤2f/(1+s)`.

Condition first on the first observation. Independence leaves the two succeeding laws unchanged, and the policy knows the observed value before deciding. Either this value is zero (two arrivals suffice), or homogeneity scales it to 1. Write `Y,Z` for the remaining observations. Conditional on this initial 1, define
```
g(y) = E max(y,Z−fy),                   w = g(0),  v = g(1),
A(y) = max(w,g(y)),                      B(y) = max(v,g(y)−f),
m(y) = E max(1,y,Z).
```
Thus `O=max(E A(Y), E B(Y))` (initial reject or accept), and `M=E m(Y)`. All expectations are finite. These functions of `y` are Lipschitz, since `g` is an expectation of a maximum of two affine functions of slopes 1 and `−f`. Finite approximations to `Y` in mean therefore approximate `O,M`; it suffices to treat finite `Y`.

Fix the law of `Z` and any finite set of allowed `y`. As the law of `Y` varies, the normalized pairs `(EA/M,EB/M)` fill exactly the planar convex hull of the points
```
(A(y)/m(y), B(y)/m(y)).
```
Indeed the new weights are proportional to the original probabilities times `m(y)≥1`, an invertible reweighting. The minimum of the larger coordinate in a finite polygon is reached on its boundary (otherwise reduce both coordinates a little). This also works for a point or segment, so a minimizing distribution takes at most two values.

If both values are at least 1, ignoring the first arrival leaves the prophet benchmark unchanged and the two-arrival bound applies. For a value `y≤1`, replacing it by zero keeps `m(y)` unchanged and cannot increase either policy payoff: `A(0)=w≤A(y)` and `B(0)=v≤B(y)` since `g(1)≥w−f`. If after replacement the law is constant zero, two arrivals again suffice. It thus remains to bound the ratio when `Y=x=1+h>1` with probability `q`, and zero otherwise.

For this law one may assume `Z` supported on `{0,a,ax}`. First cap at `ax`: each of `g(0),g(1),g(x)` and the prophet benchmark decreases by the very same amount `E(Z−ax)₊`, hence so does `O`. Proving `O≥c M` after capping proves it before capping for `c≤1`. Then round a capped `z` to the two ends of its interval `[0,a]` or `[a,ax]` at probabilities preserving the conditional mean, independently of `Y`. The functions `z↦max(y,z−fy)` for `y=0,1,x` are affine on each interval, so `O` is unchanged; `z↦max(1,Y,z)` is convex, so `M` can only increase. This reduction does not assert that an arbitrary last arrival can be split into new arrival times.

## 3. The equality of two initial actions

Let `u,t` be the probabilities that `Z=a,ax` respectively, with the remaining mass at zero. Now
```
w=a(u+xt),   v=1+a h t,   g(x)=x,
m(0)−w=1−u−t,   m(x)−x=(f−h)₊u+fx t.
```
As a function of `q`, the online value is the maximum of two affine functions:
```
O_rej = (1−q)w+q max(w,x),
O_acc = (1−q)v+q max(v,x−f).
```
The prophet is positive and affine. On any interval with a single active branch the ratio is fractional-linear and its minimum occurs at an end. Thus we need only the endpoints `q=0,1` (both covered by the two-arrival bound) and a genuine interior switch. If `v≤w`, rejection is weakly better at both ends, so a genuine switch requires `v>w`. If `x≤v`, acceptance is then weakly better at both ends, so in addition `x>v>w`.

Set
```
D=v−w=1−a(u+t),     T=1−at,     e=x−max(v,x−f)=min(hT,f).
```
At a genuine switch `0<D≤T≤1`, `e>0` and the two actions agree at `q=D/(D+e)`. Rewrite `w=1−D+h(1−T)` and use the preceding differences to express the scaled excess
```
L = a(M/O−1) = N/B,
N = e(f+D)+D[(f−h)₊(T−D)+f(1+h)(1−T)],
B = e[1−D+h(1−T)]+D(1+h).
```
The denominator is positive. The desired estimate is `L≤2f/(1+s)`.

## 4. Optimizing the excess

If `h≤f`, we have `e=hT`, and direct subtraction gives
```
N−fB = −(f−h)D²−f h² T(1−T) ≤ 0.
```
So `L≤f`. Suppose now `h≥f`. For fixed `h,T>0`, both numerator and denominator are affine in `D`. It suffices to maximize over `0≤D≤T` at either end; the denominators there are positive. At zero `L=f/[1+h(1−T)]≤f`. At `D=T` the remaining expression is
```
L = [e(f+T)/(1+h)+T f(1−T)]/[e(1−T)+T].
```
If `hT≥f`, we have `e=f` and the right-hand side is nonincreasing in `h`; take `h=f/T`. If `hT≤f`, substitute `e=hT` and cancel to get
```
L = [h(f+T)+f(1+h)(1−T)] / [(1+h)(1+h(1−T))].
```
For fixed `h≥f` this is fractional-linear in `T∈[0,f/h]` (using the continuous limiting value at zero). Its maximum is at `T=f/h`, or at zero where `L=f(1+2h)/(1+h)²≤f`.

On the shared boundary `hT=f` the formula simplifies to
```
L = f T(2−T)/[f+(1−f)T],       0<T≤1.
```
Let `T*=2f/(f+s)=(s−f)/(1−f)`. This lies in `(0,1)`. The sharp scalar inequality follows without differentiation:
```
2[f+(1−f)T]−(1+s)T(2−T) = (1+s)(T−T₀)²,
T₀=(f+s)/(1+s)=T*.
```
Here `(f+s)²=2f(1+s)`. Hence `L≤2f/(1+s)` as required.

## 5. Attainment

The maximizing parameters from the preceding calculation are `D=T=T*`, `h=f/T`, `x=1+h`, `q=T/(T+f)=1/x`, and `u=0, t=(1−T)/a`. All are legitimate probabilities. For this instance the two initial actions agree, `hT=f`, and the formulas give equality. Substitution shows `x=(2+f+s)/2`; this is exactly ENNV's three-variable extremizer, not a new lower-bound construction. With `f=0`, free replacement attains the prophet. For `f≥1` the known unrestricted guarantee together with the known two-variable upper example, padded by a zero, gives the stated endpoint regime.
