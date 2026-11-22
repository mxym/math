# Fixed-rank behavior and an angular budget obstruction for one true log mark

Let `N=2x` be even, `L=log x`, `J=xJ_0` with fixed nonempty interval
`J_0 subset [1,4/3]`, `P=N-y`, and `M_N=|J| S(N)`, with the usual
Goldbach singular factor `S(N)`. Every reflected prime below is this true
prime `P`, weighted by `log P`. This is a follow-up to the
[true one-mark transfer](https://github.com/mxym/math/commit/45b7095c),
with its reference `2M_N`, not a second application of the six-factor
cusp cap.

For squarefree `y in J`, write `u_i=log p_i/L` for its distinct prime
labels and `T=sum u_i`. For a subset `A` write `u_A=sum_{i in A} u_i`.
The cusp and the tested mark are
```
 F(y) = sum_A (-1)^|A| |u_A-T/2|,
 Z_{a,g}(y) = -sum_A (-1)^|A| g(u_A) sum_{i in A} 2u_i a(u_i).
```
The adjusted score is `F-Z`; thus **positive** adjusted values are a
debit. The established mark has `a=w chi_delta`, with
`0<=w,chi_delta<=1`, `w=1` for `u>=2beta`,
`chi_delta=1` for `u<=1/2-delta`, and a common nonincreasing cutoff
`g` equal to one through `1/2-2eps` and zero from `1/2-eps`. That
proof evaluates the true signed total of the marker as zero. We do not
repeat its calibration or assert one for more general kernels.

## 1. Sharp limit on each fixed actual rank

Let `Z_*(y)` be the same mark with amplitude `2u_i` and the exact
cutoff `u_A<T/2`. For every fixed `k>=3`, and the parameters of
the established transfer, one has uniformly in even `N`
```
 (1/M_N) sum_{y in J, P prime, y squarefree, omega(y)=k}
              log(P) L |Z_{a,g}(y)-Z_*(y)|
 <= C_k sum_{t in {beta,delta,eps}} t (1+|log t|)^(k-2) + o(1).
                                                               (1)
```
The error is taken as `N->infty` with the parameters fixed. One can
restrict the sum further to the actual `x^(1/log L)`-rough class.
For `k=2` the bound holds with error `O(beta+delta+eps)+o(1)`.
Furthermore the reference scores on the actual squarefree row are exactly
```
 F(y)-Z_*(y) = 0                             if k is even;
 F(y)-Z_*(y) = T sum_{u_A<T/2} (-1)^|A|       if k>=3 is odd.    (2)
```
In particular the *entire adjusted rank six*, including its positive
part, costs arbitrarily little by fixing sufficiently small parameters.
This neither reduces the unadjusted cusp's .872 cost as an additional
credit nor proves that all adjusted even ranks cost little at once.
The tail constant for the fixed smooth transfer depends on its parameters.
There is no interchange of a shrinking cutoff and a growing rank in (1).

### True weighted wall estimate

Order the labels, write `m=min_i u_i`, and keep the actual largest prime
`q` free, fixing the other `k-1` primes and their product `H`. The
physical interval for `q` has length at most a constant times `x/H`,
and `q>=x^(1/k)`, so `H<=1.5 x^(1-1/k)`. The elementary two-form
upper sieve in `q,N-Hq` gives
```
 sum_{q,P prime, y=Hq in J, q largest} log(P) L
              <<_{k,J_0} x S(N)/H.                            (3)
```
This is the same true two-form upper used in the
[absolute-tail proof](https://github.com/mxym/math/commit/18df7d45).
For completeness, use a fixed small power of `x^{1/k}` for the
sieve, so its polynomial floor loss is absorbed by `x/H` with fixed
reserve. Fixing a prime of `H` not dividing `N` changes a two-root
factor to one root, multiplying its local reference by
`(p-1)/(p-2)<=2`. If `p|N` but `p !| H`, the two root classes
coincide already in `S(N)`; at 2 there is one root since the actual
`y` is odd and `N` even. Cases with a prime divisor common to
`y,N` force the actual prime `P|N` and are negligible by the
divisor bound in the fixed central interval. Thus no dependence on
unbounded target local factors has been suppressed.

In applying (3), substitute `u_A=T-u_{A^c}` when `q in A`, so
that any wall about a value `1/2+O(delta+eps+m)` is a wall in a sum of
**fixed** prime logs only. Here `T=1+O_J(1/L)`. If `m<1/(10k)`
and the wall is within a fixed small neighborhood of the half, after
this substitution and, if necessary, removing the fixed least label,
the sum in the wall is bounded below by an absolute positive constant.
At least one of its actual fixed labels other than `m` therefore has
log exponent `>=c/k`. Split into the finitely many possible labels
and integrate that one first, with the others fixed. For a moving
logarithmic exponent interval of length `h`, its prime harmonic sum
is `O_k(h+L^{-B})` for any fixed `B`, by partial summation of the
ordinary PNT uniformly above `x^(c/k)`. The interval may depend
arbitrarily on the other fixed labels; we only use that it is
contained in an interval of the stated length. If `m>=1/(10k)`,
all denominators are bounded and the same argument with any involved
fixed label applies to a thin single wall. An empty or full subset
is not a near-half wall. For a symmetric difference of walls first
used below, in the compact case we may keep the two thin intervals
instead of pairing.

Consequently a wall of exponent width `O(min(m,t)+1/L)`, with at
most a bounded number of such intervals, costs in (3) at most
```
 C_k M_N [ t(1+|log t|)^(k-2) + o(1) ].                       (4)
```
Indeed, outside the two integrated coordinates `m` and the
polynomial label there are at most `k-3` fixed prime labels. Each
has harmonic sum `O(1+log(2/m))`. The least-label harmonic integral is
```
 integral_0^2 min(m,t) (1+log(2/m))^(k-3) dm/m
      <<_k t (1+|log t|)^(k-2).
```
The same sum bound, including labels arbitrarily small, follows by
binning `log(2/m)` at unit spacing and using the prime harmonic upper
on each bin. The `1/L` loss is
`O_k((1+log L)^(k-1)/L)`. A compact wall can be bounded directly by
its width, as all prime logs are above a fixed power.

### Applying it to the actual cutoffs

* Replace the common `g` by the exact half cutoff while retaining
  the bounded marked coefficient. A monotone `g` is a probability
  mixture of sharp endpoints `v in [1/2-2eps,1/2-eps]`. For a fixed
  mark different from the least prime, pair the other subsets across
  the least label before taking absolute values. The difference
  between the two sharp cutoffs is an indicator of a band. Its
  least-label difference is supported on the symmetric difference
  of that band and its translate by `m`, of total width at most
  `2 min(m,2eps+O(1/L))`. This can be applied after replacing
  the own half by `1/2`: the two extra true half seam intervals
  cost `O(1/L)` by (3). In each paired term the membership of
  the largest label does not change. Thus the polynomial-coordinate
  count preceding (4) applies to the same two intervals after
  taking complements, even if the fixed sum then no longer contains
  the original marked prime. If the mark *is* the least prime,
  use its amplitude at most `2m`, without pairing. This is a strip
  of width `O(eps+1/L)` with another polynomial coordinate, since
  a least label alone cannot lie near the half for `k>=3`.
  Its integral is `O_k(eps)+o(1)`. These estimates give (4) for eps.

* Restore marks of size at most `2beta` in the sharp sum.
  If the mark is least, use its amplitude `O(m)` and
  `m<=2beta`; the remaining `k-2` fixed prime harmonic sums
  cost at most `C_k(1+log(2/m))^(k-2)`. Otherwise the amplitude
  is `O(beta)` and pairing across the least label now restricts
  to a half-wall of width `O(m+1/L)`. This costs `O_k(beta)+o(1)`
  by the same integration. Both bounds are within (1).

* Restore marks above `1/2-delta` in the sharp sum. For small
  fixed delta and `k>=3`, the mark is not the least. Pair across
  the least label, which leaves a band of width `O(m+1/L)`.
  If the mark is not the global largest, a contributing subset
  cannot contain the largest as well (the two macroscopic labels
  would exceed the half). Sum the actual marked label itself:
  it is also confined to `[1/2-delta,T/2)`. If the mark is the
  largest, replace the contributing subset by the complementary
  fixed sum near the half. The mark condition imposes the
  *additional* interval restriction on the **total** fixed log
  `sum_{p_i!=q} u_i = T-u_q`, an interval of width
  `O(delta+1/L)` near the half. The same polynomial coordinate
  in the complementary wall enters that total with coefficient
  one. Fixing all other labels hence gives the intersection cost
  `O(min(m,delta)+1/L)` in either case, proving (4) for delta.

All statements count only actual prime labels and actual unit rows.
For `k=2`, the only possible active mark is the smaller prime;
the amplitude `2u` pays its tiny harmonic, and the near-half
interval has bounded harmonic density. This proves (1).
The same argument with the ordered simplex measure instead of (3)
also bounds the corresponding ordinary angular absolute integrals.

For (2), squarefreeness ensures no equality `u_A=T/2`.
On even ranks, reflection is even, so the short half of
`sum_A (-1)^|A|` vanishes and
`F=-2 sum_short (-1)^|A| u_A=Z_*`.
On odd ranks the reflection of the absolute value cancels it.
For odd `k>=3` the full weighted sum
`sum_A(-1)^|A| u_A` is zero, and complementary substitution
in its long half gives
`2 sum_short (-1)^|A| u_A=T sum_short (-1)^|A|`.
This proves (2).

At rank five, the short-step value in (2) vanishes on a giant
(the only short sets are all subsets of the remaining four
labels). Otherwise all singles are short. The long pairs are
pairwise intersecting (two disjoint pairs cannot both exceed
the half), and there are `j<=4` of them: an intersecting graph
is a star or a triangle. By complements the number of short
triples is `j`, and no quadruple is short. The value is
therefore `6-2j`. Thus the **positive** adjusted rank-five
debit includes the full balanced chamber, rather than being
a half-root or tiny-coordinate seam. Its ordinary signed value
is `pi^4/120` by the sine law below; it is not an estimate at
a prescribed target.

## 2. Exact obstruction to the common angular upper recipe

For a symmetric profile score `B` in rank `k`, put
```
 I_k(B) = (1/k!) integral_{u_i>0, sum u_i=1} B(u) du_1...du_{k-1}/prod u_i.
```
This is the same angular normalization as the
[genuine central prime upper](../AngularPrimeDomination.md).
For that upper, two-form tail bounds of the preceding type allow
removal of a fixed positive minimum log cutoff for each fixed
rank, when the angular positive parts are integrable and the
kernel has the corresponding small-label estimates. We use
that theorem **only to describe the recipe being tested**:
discard all favorable rows, and price each remaining rank by
`(200/53) I_k((F-Z)_+)` in units of the same `M_N`.
The number shown to be too large is this **upper bound recipe**,
not the physical prime-supported contribution itself.

In this section the tag amplitude may be arbitrary
`2u a(u)`, `0<=a<=1`; the **common** monotone cutoff `g`
may be anywhere below the half, not just the preceding thin
seam. The shape must of course also satisfy any needed
hypotheses of a true zero calibration for the proof scheme
to be used. We show that even allowing all such amplitudes
and all common monotone `0<=g<=1`, supported at or below the
half, one always has
```
  I_2((F-Z)_+) + I_5((F-Z)_+) + I_8((F-Z)_+) > .538 .       (5)
```
Because `(200/53)*.538 > 2.03`, this particular envelope
cannot meet the literal reference `2M_N`, **even with all
other ranks left out**. This does not rule out using more
precise arithmetic estimates on some ranks, keeping signed
credits, tag-dependent cutoffs or interactions of more than
one genuine marked factor.

### Pin the mark before taking the angular mean

We use the [signed rank law](../rank_sine/Proof.md) for the
flat short threshold on `r` labels:
```
 J_r(v) = I_r(sum_A (-1)^|A| 1_{u_A<v})
        = Im[(log((1-v)/v)+i pi)^r]/(pi r!), 0<v<1.
                                                               (6)
```
Here the ordinary integral is absolutely integrable at every
fixed rank and threshold. The cited proof is by angular
Gamma regularization of the exact additive cutoff and the
sine integral. Equation (6) has the sign shown; in particular
`J_1=1`, and at half `J_5=pi^4/120`.

First take a sharp common cutoff `g=1_{u_A<v}`, with
`0<v<=1/2`. Pinning one actual mark for the ordinary angular
integral gives
```
 I_k(Z) = 2 integral_0^v a(u)/(1-u) J_{k-1}((v-u)/(1-u)) du.
                                                               (7)
```
The mark bit changes the sign of the Möbius factor, canceling
the outside minus. The `k` choices turn `1/k!` into
`1/(k-1)!`. After dividing the other `k-1` labels by
`1-u`, the reciprocal density is
`du/[u(1-u)]` times their normalized simplex measure; `2u`
cancels the factor `u`. This proves (7), not a conditional
distribution of the actual partner prime. For fixed
`v>0`, Fubini follows by pairing across a least *other*
label: as in the wall proof, the loss from a step of width
`m` is integrable when both groups have positive mass.
For `u` near `v` the remaining threshold is small; a usable
absolute bound for the signed step integral before the
`u` integral is
`O_k((1+|log((v-u)/(1-u))|)^(k-2))`.
One way to check this bound is to use the paired-wall proof
for `m` below a small constant times the threshold
and select one label in each side. On the small side
rescale its selected interval of length `O(m)` by the
threshold (its harmonic cost is then `O_k(m/threshold)`);
on the large side the largest label stays bounded below.
The other labels cost finite powers of `1+|log m|`.
For `m` above that multiple of the threshold, the full
ordered harmonic bound is `O_k((1+|log threshold|)^(k-2))`
after keeping the largest coordinate free. This proves
integrability as the mark approaches the sharp edge.
Alternatively, joint integrability follows directly by
the fixed-`v` wall argument with the marked term's `2u`
amplitude and the least label, without uniformity in `v`.
If an endpoint mixture approaches zero, the same analysis
works with a bound `O_k(v(1+|log v|)^{k-2})` for the
absolute marked mean, by integrating `u<v` in this argument.
Thus averaging sharp layers is legitimate. For the actual
transfer all its endpoints are in a fixed near-half interval.

With `t=log((1-v)/(v-u))` one has
```
 u=v-(1-v)e^(-t), t>=log((1-v)/v)>=0, du/(1-u)=dt/(1+e^t).
```
Use the linear combination of signed means with coefficients
`1, A5=29/40, A8=7/10` for ranks `2,5,8` respectively.
Since every coefficient is in `[0,1]`, the sum of positive
means in (5) is at least this signed combination. In its
marker part, (6)--(7) give the polynomial
```
 D(t)= 2 + (A5/3) (t^3-pi^2 t)
         + (A8/2520)(7t^6-35pi^2 t^4+21pi^4 t^2-pi^6).
```
The signed marker contribution is at most the integral of
`D(t)_+/(1+e^t)` over all `t>=0`, regardless of the choice
of tag amplitude or of the sharp common endpoint. A common
monotone `g` is a positive mixture of such endpoints
(with total mass at most one), so the same upper holds.
A cutoff endpoint depending on the tag would not permit
this argument, which averages a **common** sharp endpoint
before the one-dimensional change of variable.

### Exact cusp normalization and rational bound

For the same linear absolute cusp,
`I_2(F)=2 log 2`, from `F=2 min(u,1-u)`;
`I_5(F)=0`. The exact signed even means are
```
 I_k(F) = (-1)^(k/2+1) 2^k/(pi k!) integral_0^(pi/2) z^k/sin(z)^2 dz.
                                                               (8)
```
For verification, replace the prime reciprocal simplex measure
by `prod u_i^(b-1)`, `b>0`, and pass to independent gamma
coordinates with density `e^(-sum y_i) prod y_i^(b-1)`.
The radial factor is `Gamma(k b+1)` by degree-one homogeneity.
In the Fourier formula
`|r|=(2/pi) integral_0^infty (1-cos(tr)) dt/t^2`, the
constant cancels in the subset sum, and the remaining
gamma factors form the `k`th power of
```
 Gamma(b)[(1+i t/2)^(-b)-(1-i t/2)^(-b)].
```
Its modulus is uniformly `O(min(t,1))` as `b->0`,
since `b Gamma(b)` is bounded and
`|sin(b arctan(t/2))|<=b arctan(t/2)`.
Pass to the limit in the Fourier integral by dominated
convergence, using also the angular bound by a constant
times the smallest label (pairing its bit in the
one-Lipschitz cusp). The gamma expression tends to
`-2i arctan(t/2)`. Substituting `z=arctan(t/2)` gives
exactly (8). In particular the elementary chord
`sin z>=2z/pi` yields
```
           |I_8(F)| <= pi^8/(14*8!) < .01681.
                                                               (9)
```
So the left side of (5) is bounded below by
```
 2 log 2 - A8*pi^8/(14*8!) - integral_0^infty D(t)_+/(1+e^t) dt.
                                                               (10)
```

The included [exact checker](check.py) gives a lower bound
strictly above `.538` for (10), using no floating-point
arithmetic in its inequalities. Here are the details of the
certificate. Enclose pi in rational decimals with 15 digits
after the point, verified from Machin's arctangent identity
by alternating series. Enclose `2 log 2` below by 16 terms
of its positive inverse-hyperbolic tangent series at `1/3`.
Divide `[0,32]` into `32*2048` intervals of width `1/2048`.
An upper for `D` is obtained by the appropriate rational
pi endpoint in every coefficient, then the right endpoint
for positive monomials and the left for negative ones.
Take the positive part and use the left endpoint for the
decreasing logistic. A lower endpoint value of the
exponential is propagated by repeatedly multiplying by
`1+1/2048+1/(2*2048^2)` and rounding down with denominator
`10^22`; each resulting rectangle bound is rounded up
with that denominator. Beyond 32 use `exp(-t)` and drop
the negative polynomial monomials, bounding the tail with
the exact incomplete moments of an integer power against
`exp(-t)`. The full integral upper is less than
`.836390866608`, and (10) is certified above .538.
The script also checks the parity, exact sharp subtraction,
and the rank-five chamber formula on 18,000 exact integer
log-profile fixtures and three explicit examples.

The estimate does not claim that the positive mass of the true prime
rows is at least any of these angular constants, and does not rule
out genuinely signed fixed-target comparisons.
