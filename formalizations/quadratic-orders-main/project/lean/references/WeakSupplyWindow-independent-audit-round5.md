# Independent audit of the weaker common-window supply

Audit date: 2026-10-07. Scope: the proposed replacement of uniform natural
dyadic density by positive upper logarithmic density of genuinely good dyadic
bins, while retaining the existing integer base parameter, bands, floors,
schedule, and smoothing. Existing Lean source was read but not modified.

**Verdict:** the proposed forty-phase / 196-block covering and discrete
averaging argument is mathematically valid. Its density normalization is
`beta / log 2`; the advertised `q * beta / 2` lower bound is consequently a
valid conservative bound. Empty individual windows do not obstruct the
literal schedule or local batch charge. The current final engine still needs
an aggregate weighted-supply bridge and a weaker arithmetic interface. This
audit does not prove the arithmetic supply for all quadratic orders, or the
unconditional ALL theorem.

## Precise input

Let `ell = log 2`, `L = log 100`, and `h = log (21/20)`. Require one fixed
`delta > 0` and a set `G` of positive integers such that every `j in G`
satisfies the actual finite-batch condition

```
delta * 2^j / log(2^(j+1)) <= card (dyadicPrimeBatch data.primes j).
```

Require, for the same `G`,

```
limsup_{J -> infinity} (sum_{1 <= j <= J, j in G} 1/j) / log J = beta > 0.
```

The good-bin density alone, with no fixed positive `delta` attached to those
bins, would not discharge the local entropy/capacity conditions. The measure
must exclude `j = 0`: the ordinary real expression `log(j*ell)` is not a valid
logarithm there. A finite initial deletion never changes the stated upper
logarithmic density.

## Forty phases really cover the integer-shift circle

The rational bounds `4.605 <= L <= 4.606` imply, for `d = 5*L - 23`,

```
1/40 <= d <= 3/100 < 1/21 <= h < 1.
```

The `h` lower bound follows from `1 - 1/x <= log x` at `x = 21/20`; the
upper bound follows from `log x <= x-1`. Successive closed intervals
`[k*d, k*d+h]`, `0 <= k < 40`, overlap because `d <= h`. Their last upper
endpoint is at least

```
39/40 + 1/21 = 859/840 > 1.
```

Thus their union contains `[0,1]`, including both endpoints. This proof does
not require equidistribution, irrationality of `L`, or an asymptotic orbit
density assertion. Floating-point evaluation is only a diagnostic: the
actual values are approximately `d = 0.02585092994` and
`39*d+h = 1.05697643185`.

For an atom at real coordinate `x` and a block `b`, put

```
s = x - 196*b*L,  a = floor(s) in Z,  t = s-a in [0,1).
```

Choose `k < 40` with `k*d <= t <= k*d+h`, set
`w = 196*b + 5*k` and `m = a - 23*k`. Then

```
w*L = 196*b*L + 23*k + k*d,
0 <= x - (m+w*L) = t-k*d <= h.
```

So the atom lies in `[m+w*L, m+w*L+h]`. The forty selected offsets are
distinct and lie between `196*b` and `196*b+195`. For `b < q`, all lie in
`0 <= w < 196*q`; offsets from different blocks lie in disjoint integer
blocks. An atom therefore contributes to at least `q` distinct pairs `(m,w)`.
It need not be caught in every window, or at the same integer `m` in every
block. That is precisely why one sums over integer `m` before averaging.

## Correct normalization of the atomic measure

Define the locally finite positive atomic measure

```
nu = sum_{j in G, j >= 1} (1/(j*ell)) * Dirac(log(j*ell)).
```

For any fixed real lower endpoint `A`,

```
nu([A,T]) = (1/ell) * sum_{j in G, j <= floor(exp(T)/ell)} 1/j
            - a bounded initial-endpoint correction.
```

The possible equality atom at `A` changes only that fixed finite correction.
For `J(T) = floor(exp(T)/ell)`, `log J(T)/T -> 1`. Hence

```
limsup_{T -> infinity} nu([A,T])/T = beta/ell.
```

This identity also holds with upper endpoint restricted to integers `N`.
For the nontrivial direction, round any real endpoint up to `ceil(T)` and
use positivity of `nu` and `ceil(T)/T -> 1`; the reverse inequality follows
because integers are a subsequence. The monotone numerator likewise makes
the natural-index and real-index logarithmic-density formulations agree.

Calling this measure density `beta` would miss a factor `1/log 2`. Since
`0 < log 2 < 1`, a target `q*beta/2` is weaker than
`q*beta/(2*log 2)` and is safe.

## Finite summation, atom boundaries, and arbitrarily large natural bases

Fix `q >= 1` first and set `W = 196*q`. For a natural threshold `M`, define

```
F_W(m) = sum_{0 <= w < W} nu([m+w*L, m+w*L+h]),
A = M + W*L + h.
```

The slightly smaller margin `M+(W-1)*L+h` also works; `A` above is simpler.
If `A <= x <= N`, the catch in each block satisfies

```
m = x-w*L-theta,  0 <= theta <= h,
M <= m <= N.
```

In particular these integer catches are natural numbers when `M >= 0`.
The endpoint-inclusive inequalities remain valid when `x = A`, `x = N`,
or an atom is exactly a window endpoint. Closed intervals only increase
multiplicity. Because `h < 1`, an atom has at most one catch for each fixed
`w`, though uniqueness is not needed for the lower bound.

For an integer `N >= M`, finite double counting gives

```
sum_{m=M}^N F_W(m) >= q * nu([A,N]).
```

There is no infinite-series exchange hidden here. Every window in this finite
sum lies inside `[M, N+(W-1)*L+h]`, whose atoms have bounded positive integer
indices. One may exchange the two finite sums of nonnegative weighted
indicators. The right-hand side retains a subset of these atoms and uses
their at-least-`q` multiplicity.

The fixed lower endpoint `A` deletes only finite mass. Therefore

```
limsup_{N -> infinity} q*nu([A,N])/(N-M+1) = q*beta/ell.
```

For sufficiently large members of this limsup subsequence, the average of
the finitely many `F_W(m)`, `M <= m <= N`, exceeds `q*beta/(2*ell)`.
At least one integer `m` in that range consequently has

```
F_W(m) >= q*beta/(2*ell) >= q*beta/2.
```

Since `M` was arbitrary, this gives arbitrarily large natural `m` for each
fixed `q` / `W`. It does **not** give an eventual statement for all `m`.
For example, let `t_(n+1) = t_n^2`, and let `G` consist of the integer
indices in `[exp(t_n), exp(2*t_n)]`. Elementary harmonic-sum estimates give
upper logarithmic density `1/2`. For every fixed `W`, the intervening gaps
contain arbitrarily large integer `m` for which all `W` windows miss `G`,
so `F_W(m) = 0`. Thus replacing the required arbitrarily-large existence
by an eventual supply assertion would be false under the stated hypothesis.

## Maximum-weight residue thinning and the rate bound

For the selected `m`, let `B_w` be the finite set of `j in G` with
`log(j*ell)` in `[m+w*L, m+w*L+h]`. Exponentiating is exactly equivalent to
the unchanged implemented window condition

```
100^w * exp(m) <= j*ell <= (21/20)*(100^w * exp(m)).
```

The sets `B_w` are disjoint because `h < L`. Consequently, with
`B = union_{w<W} B_w`,

```
F_W(m) = sum_{j in B} 1/(j*ell).
```

For the already chosen `K > 0`, choose a residue class `a mod K` maximizing
this weight, and set `J_w = {j in B_w : j % K = a}`. The finite pigeonhole
principle gives

```
sum_{j in union J_w} 1/(j*ell) >= F_W(m)/K.
```

This must be a maximum-**weight** class, not merely a maximum-cardinality
class. The same class can be chosen globally; distinct indices in it differ
by at least `K`, so it gives global and within-window separation. Individual
`J_w` may be empty. Every retained bin still has its original fixed-`delta`
batch-cardinality condition.

For the literal `windowBatchRate c j = c/(10000000*log(2^j))`,

```
sum_{j in allBins W J} windowBatchRate c j
  = (c/10000000) * sum_{j in allBins W J} 1/(j*ell)
 >= c*q*beta/(20000000*K).
```

All selected indices are positive, so these rates are positive. Select
`q >= 1` large enough that this last expression exceeds
`log(card(wordStepBall b e D))+1`, then set `W=196*q`. The stronger normalized
bound saves a factor `ell`, but is unnecessary. Positive aggregate weight
also proves `allBins W J` is nonempty, supplying the engine's required
`card = n+1` enumeration even when some windows are empty.

## Quantifier order and existing Lean interfaces

The required order is:

1. Fix the order, embedding, step bound, good-bin parameters `delta,beta`,
   then choose the original `a,K,c` using `exists_window_gap_parameters`.
2. Choose `q` and `W=196*q` from the rate excess.
3. Collect the existing eventual numerical/charge thresholds for this fixed
   `W`, and choose the arbitrary lower bound `M` beyond their maximum.
4. Use the arbitrarily-large weak-supply conclusion to choose natural
   `m >= M`, then finite `B`, the weight-maximizing residue class, `J`, and
   the actual finite prime pool `S`.
5. Only after these choices quantify over all injective avoiding walks.

This permits intersection with every existing eventual guard. It never
intersects two merely arbitrarily-large sets, and never chooses `W` after
`m` or after a walk.

Read-only inspection found these relevant points:

| Existing source | Finding |
|---|---|
| `GenericBandParameters.lean:297` and `:307` | `windowBlocks` and its split identity accept arbitrary finite `J_w`. Empty top blocks are valid; the accurate block for that window is still included. |
| `GenericWindowSchedule.lean:65`, `:74`, `:90` | `commonBlocks`, length bounds, suffix operations, and metric-ball bounds use upper bin-size guards, not a positive lower cardinality per window. |
| `GenericCommonWindowCharge.lean:79` and `:137` | The common-law charge is conditional on selected `j in J_w`. Its prime-batch nonemptiness is derived from the selected bin's fixed-`delta` cardinality lower bound. It never needs every `J_w` to be nonempty. |
| `GenericWindowLogBudget.lean:156` onward | Predecessor and pool cost/error bounds use separation, prime membership, and upper scales; empty windows cause no problem. |
| `GenericFiniteSieveEngine.lean:35` | The actual finite telescope uses aggregate `allBins.card=n+1`, upper scales, errors, and local selected charges. It does not require per-window density. |
| `GenericFiniteSieveEngine.lean:141-174`, `:197` | The current final engine still obtains the strong eventual per-window cardinality supply, proves nonemptiness from window 0, and calls `allBins_rate`. These are the exact final assembly steps needing a new aggregate-supply version. |
| `GenericWindowLogBudget.lean:300` | `common_window_parameters` still asserts eventual linear cardinality in every window and reads `A.uniform_dyadic_density`. The weaker input cannot be silently substituted into this theorem. |
| `Sieve.lean:34`, `:53` | `ArithmeticInterface` itself contains the stronger dyadic `Tendsto` density field. Local geometric proofs can be replayed over the geometric fields, but their existing theorem statements still require this stronger interface. |
| `PrimeSupply.lean:11`, `FiniteSieveConsequences.lean:15`, `Assembly.lean:17` | The current ALL assembly is explicitly conditional on the stronger principal split-prime supply. It is not made unconditional by the covering argument. |

The literal `m : Nat`, `accurateGrid m = exp(-m^2)`,
`accurateIterations m = 4*m^2`, `bandSize` natural floor, and
`windowSmoothing W m = ceil(exp(20*100^W*exp(m)))` can all remain unchanged.

## Machine-checked deliverable and remaining gaps

Added the distinct module
`Entry002/WeakSupplyWindowIndependentGrid.lean`. It proves:

- arbitrary finite overlapping grid coverage;
- the actual logarithmic width bounds `1/21 <= log(21/20) < 1`;
- the step bounds and forty-cover, conditional on the displayed rational
  bounds for `L`;
- the exact integer catch for each 196-block;
- a catch in a prescribed integer range for an atom beyond the conservative
  fixed lower margin;
- actual `L = log 100` versions of the forty-cover, integer catch, and
  integer-range catch, using the separately proved
  `Entry002.weakSupplyWindow_log100_bounds` from
  `Entry002/WeakSupplyWindowLogCertificate.lean`;
- maximum-weight residue-class thinning with exact global `K`-separation.

Compilation used only the authorized direct wrapper:

```
python3 scripts/compile_round5.py --final \
  Entry002/WeakSupplyWindowIndependentGrid.lean \
  logs/WeakSupplyWindowIndependentGrid-axioms.lean
```

The build/axiom evidence is in
`logs/WeakSupplyWindowIndependentGrid-final-audit.log`. No existing Lean
source, old round cache, Lake configuration, or unrelated repository was
modified. The new module does not import an existing analytic certificate,
or postulate a density or arithmetic conclusion.

The actual logarithm certificate was inspected: it rewrites `log 100` as
`6*log 2 + 2*log(5/4)` and applies proved finite logarithm-series lower and
upper remainder bounds at `1/3` and `1/9`. It contains no `sorry`, custom
axiom, or assumed numerical bound. The actual catch corollaries therefore
remove the earlier rational-logarithm premises.

Remaining formal work, rather than proved conclusions of this audit:

- Formalize the atomic/finite-sum density conversion, endpoint truncation,
  discrete double count, integer limsup subsequence, and arbitrarily-large
  natural-base selection.
- Expose a weaker arithmetic interface carrying the four geometric fields
  plus fixed-`delta` positive upper logarithmic density of good bins; replay
  the needed geometric lemmas without retaining a natural-density premise.
- Compose the aggregate-rate engine and restoration with this weak supply,
  retaining the finite pool before all walk quantifiers.
- Prove that actual principal split-prime witnesses for **every** quadratic
  order supply the same fixed-`delta` good-bin density. No existence,
  Dirichlet density, natural density, or Chebotarev theorem was supplied or
  certified by this finite covering audit.

No counterexample was found to the precise proposed conditional covering /
weighted-supply argument. The genuine limitations are the weaker existential
quantifier in `m`, the indispensable actual good-bin condition, and the
unproved arithmetic and formal integration steps above.
