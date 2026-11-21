# Adaptive sieve ratios in the two-smallest switch

This sharpens the unconditional scope of
[VariableLevelTwoSmallestRows.md](VariableLevelTwoSmallestRows.md).
In particular the deleted unmarked powers need not shrink when the
original small cutoff y=x^ε tends to very small powers. No bound on
the entire surviving low residual is proved.

Keep H=1/2−ε, A_p=H−log_x p for p∈{1}∪J, and all other notation
from the switch. For any fixed integer k≥4, choose s sufficiently
large in terms of k and define

    K_p = k + ½ log(1/A_p),
    β_p = A_p/[2(K_p+1)],             γ_p=2β_p,
    T_p(r)=x^((A_p−log_x r)/K_p).

Use precisely the same whole-row and two-smallest-wedge deletions,
with K_p in place of constant K for the p-th term. Then

    |D(N)| ≪ [(k−1)!^(−1) + exp(−s/2) + o_{s,k}(1)] M_N,       (19)

uniformly for even N with absolute implied constant. The arbitrary
moving interval and sign-weight versions for the wedge persist.
Here k, then s, then N can be chosen in that order. The limiting
unmarked exponents as s→∞ at fixed k are

    β_1 → [4(k+1+½ log 2)]^(−1),       γ_1=2β_1.

The same prescribed fixed marker exponents u∈(1/3,1/2) give
positive limiting β_p with A=1/2−u. This decouples the large
presieve s needed for the original B(n) loss from the actual
geometric scope of the controlled low rows.

## Proof

All local moduli, multiplicity, and coprimality statements of the
switch remain in force with these moving parameters. In particular
the full larger-than-r cutoff always has exponent at most H/k<1/3,
so it is strictly below any actual marker. For choosing s, note
that A_p≥(s+1)ε and K_p≤k+s/4. Hence
2(K_p+1)≤s+1 for s≥4k+2, which ensures β_p≥ε.
The smallest local ratio during the second switch is K_p≥4 and
the largest is at most H/ε, finite at fixed s; the linear-sieve
errors are uniform. For a precise source with coefficient errors
uniform under the fixed dimension hypothesis, see
[Theorem 2.1 in *Superscars for arithmetic point scatterers II*](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136),
or Friedlander–Iwaniec, *Opera de Cribro*, Theorem 11.13.

Use the exact linear-sieve gap instead of its exponential bound.
With Euler's constant γ_E, the defining delay equations and
initial values of the linear-sieve functions yield, for v≥1,

    F(v)−f(v) = (2e^{γ_E}/v) ρ(v−1),

where ρ is the Dickman function. Indeed set
h(t)=(t+1)(F(t+1)−f(t+1))/(2e^{γ_E}). The initial value is one
on [0,1]; the difference of the two defining delay equations
gives th'(t)=−h(t−1), for t>1. This determines h=ρ recursively.
Equivalently tρ(t)=∫_{t−1}^tρ(u)du for t≥1, as is seen by
differentiation and the initial value. This shows positivity and
monotonicity inductively (a first zero would contradict the
positive integral). It also gives
ρ(t)≤ρ(t−1)/t for t≥1, so ρ(t)≤1/⌊t⌋! by iteration.

At an endpoint U=x^u for a fixed conditioned product rp, t=log_x r,
equation (14) of the switch therefore gives normalized discrepancy
at most

    [2ρ((A_p−t)/u −1)/(A_p−t) + o_{s,k}(1)] g_N(rp),

with the little-o after normalization uniform, including the
local prime-power density at r. For β_p≤t≤γ_p, u≤(A_p−t)/K_p,
this is at most

    [2(K_p+1)ρ(K_p−1)/(K_p A_p) + o_{s,k}(1)] g_N(rp).

Summing over r costs at most log 2+o_{s,k}(1), independently
of the varying p, and both endpoints are paid. For the whole-row
second endpoint x^{β_p}, the same expression with t=0 and
ratio 2(K_p+1) is again bounded by O(ρ(K_p−1)/A_p) times
g_N(p). The first endpoint y gives the previous
O(exp(−s/2)) bound by A_p/ε≥s+1 and the factorial bound.

Write v=½ log(1/A_p), so A_p≤1/2 and v≥0.
By the factorial estimate and (m+n)!≥m!n!,

    ρ(K_p−1) ≤ 1/[(k−1)!⌊v⌋!] ≪ A_p^(1/2)/(k−1)!.

For the last step, e^v/⌊v⌋! is bounded on [0,∞), e.g. by
e Σ_{j≥0} e^j/j!. Thus the remaining marker sum divided by
A_p is bounded by a constant times

    1/(k−1)! · Σ_{p∈{1}∪J} g_N(p)/√A_p
      ≪ 1/(k−1)! · [1 + ∫_{1/3}^{H} du/(u√(H−u)) + o_{s,k}(1)]
      ≪ 1/(k−1)! .

For each fixed s the reciprocal-prime sum is taken only up to the
actual last marker below H by (s+1)ε. Its Riemann sum therefore
has a bounded smooth weight at fixed s; only after taking that
limit is it majorized by the displayed integrable endpoint.
The integral is bounded by an absolute constant for all H<1/2.
Together with ordinary (12) for all progression errors, this
proves (19). The arithmetic parity witness of the switch still
applies and keeps a large positive surviving low residual in
that model; changing cutoff schedules is not an escape by itself.
