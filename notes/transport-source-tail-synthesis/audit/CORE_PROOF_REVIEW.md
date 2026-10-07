# Core density-root theorem: independent proof review

Date: 7 October 2026  
Scope: Section 1 of synthesis B, including the profile lemma, root characterization, strong first-order limit, endpoint warning, and density-level corollary.  
Reviewed pre-correction TeX SHA-256: `b2ad6b9c6ef055852768ae95871cc13e98bdb38769d0bcea8477eebe5bd59547`.
The corrected synthesis applies the 11 recorded exposition and status edits, with Section 1 and all 10 theorem, lemma, corollary and proof environments unchanged. This historical source digest is not a digest of the corrected full TeX.

## Exact verdict

**PASS for the stated mathematical claims in this scope, with the stated restriction `1 < s < infinity`.** I independently reconstructed the argument and found no counterexample or proof-breaking gap. The quantitative constants are valid upper/lower bounds; they are not asserted to be optimal. The forward-loss coefficient is 8 and the backward-loss coefficient is 6, exactly as the displayed limit requires.

In particular:

- Global membership of `r^(1/s)` in `W^(1,s)(R^d)` is equivalent to the directional `O(h)` overlap bound.
- A finite directional liminf suffices. Each coordinate may use a different sequence; no common sequence is needed.
- The claimed strong `L^s(dx)` limit is valid, including at zero sets and for arbitrary finite nonnegative representatives of the density.
- Zero extension is essential to the global theorem: support-boundary jumps are retained, not ignored.
- At `s = 1`, the overlap condition characterizes `BV`, rather than `W^(1,1)`. The strong-limit conclusion remains true if `W^(1,1)` is separately assumed, but it cannot be inferred from the overlap bound alone.
- The density-level `L^1` formula follows and recovers an existing result on a subclass. This does not establish new novelty or extend the transport framework beyond its separate hypotheses.

This is an **independent model-based mathematical audit**, not independent external human review, peer review, Lean or other proof-assistant verification. No external mathematician participated. No literature-novelty, priority, optimality, publication, authorship or licensing conclusion is certified. The proof below is the basis for the verdict; examples are only checks, not substitutes for that proof.

## 1. Setup and representative issues

Let `1 < s < infinity`. Let `r : R^d -> [0,infinity)` be measurable and finite everywhere, with integral 1, and let

`rho = r dx`, `sigma = r^(1/s)`.

Thus `sigma` is in `L^s(dx)` and its `L^s` norm is 1. For a fixed coordinate `j` and `h > 0`, write

- `sigma_+(x) = sigma(x + h e_j)` and `sigma_-(x) = sigma(x - h e_j)`;
- `d_+(x) = (1 - r(x+h e_j)/r(x))_+` and `d_-(x) = (1 - r(x-h e_j)/r(x))_+` when `r(x) > 0`;
- `d_+(x) = d_-(x) = 0` when `r(x) = 0`;
- `W_h = 6 |d_+ - d_-| + 2 d_+`;
- `B(h) = ||sigma_+ - sigma||_s`;
- `Xi(h) = max(||d_+||_(L^s(rho)), ||d_-||_(L^s(rho)))`.

The quantities are measurable and `0 <= d_+, d_- <= 1`, so `0 <= W_h <= 8`. The latter bound follows by considering `d_+ >= d_-` and `d_- > d_+` separately.

If two finite density representatives differ on a null set `N`, their deficits and weights for a fixed `h` differ only within `N union (N+h e_j) union (N-h e_j)`. Consequently all the displayed norms, and all statements about strong convergence, are independent of the representative. An uncountable common exceptional set over all `h` is not required for any argument below.

All functions live on `R^d`. If a density was originally specified on a support or domain, its zero extension is used throughout. This is not a theorem about an interior Sobolev space on that support.

For completeness, if `m(x) = min(r(x),r(x+h e_j))`, then everywhere on `{r>0}`,

`m(x) = r(x)(1-d_+(x))`,

`m(x-h e_j) = r(x)(1-d_-(x))`.

Hence `|m(x-h e_j)-m(x)|/r(x) = |d_+-d_-|`. On `{r=0}`, both minima vanish. The minimum-density interpretation and its zero convention are therefore consistent.

## 2. Quantitative comparison, including all constants

For `0 <= t <= 1`,

`1-t <= 1-t^s <= s(1-t)`.

The lower bound uses `t^s <= t`; the upper bound is the mean-value theorem, since the derivative of `t^s` is at most `s` on `[0,1]`. If `sigma_+ >= sigma`, both the forward deficit and the positive root loss vanish. Otherwise apply this inequality to `t = sigma_+/sigma`. It follows everywhere, including where `sigma=0`, that

`(sigma-sigma_+)_+ <= sigma d_+ <= s (sigma-sigma_+)_+`.     (2.1)

The corresponding backward inequality also holds.

For any nonnegative `a,b`,

`2 max(a,b) <= 6|a-b|+2a <= 8a+6b`.                       (2.2)

The left inequality is immediate for `a>=b`; when `b>a`, it is `6b-4a >= 2b`. Taking norms and then using Minkowski gives

`2 Xi(h) <= ||W_h||_(L^s(rho)) <= 14 Xi(h)`.              (2.3)

To recover the full root translation, split it into downward and upward increments:

`B(h)^s = integral (sigma-sigma_+)_+^s dx`

`         + integral (sigma_+-sigma)_+^s dx`.

The first term is at most `||d_+||_(L^s(rho))^s` by (2.1). In the second term set `y=x+h e_j` and use the backward version of (2.1). This gives

`B(h)^s <= ||d_+||_(L^s(rho))^s + ||d_-||_(L^s(rho))^s`

`        <= 2^(1-s) ||W_h||_(L^s(rho))^s`.

Thus

`B(h) <= 2^(1/s-1) ||W_h||_(L^s(rho))`.                  (2.4)

There is no missing contribution from `{r=0}`: an upward increment originating there is accounted for after translating to its nonzero endpoint.

Conversely, (2.1) yields

`||d_+||_(L^s(rho)) <= s B(h)`.

The backward full translation has exactly the same Lebesgue `L^s` norm as the forward translation, by a change of variables, so the same bound holds for `d_-`. Using (2.2),

`||W_h||_(L^s(rho)) <= 14 s B(h)`.                       (2.5)

Equations (2.3)--(2.5) prove every inequality in the profile lemma, including its chained bound

`B(h) <= 2^(1/s-1) ||W_h||_(L^s(rho))`

`     <= 14 s 2^(1/s-1) B(h)`.

These are genuine analytic inequalities for every `h>0`; they are not asymptotic or numerical observations. Probability normalization is not otherwise essential: the same comparisons hold for every nonnegative integrable density of finite mass.

## 3. A finite liminf gives a global Sobolev derivative

Assume, for this coordinate, that

`liminf_(h downarrow 0) ||W_h||_(L^s(rho))/h < infinity`.

There is a sequence `h_n downarrow 0` for which those quotients are bounded. By (2.4),

`q_n(x) = (sigma(x+h_n e_j)-sigma(x))/h_n`

is bounded in `L^s(R^d)`. Since `1<s<infinity`, this space is reflexive, including on the infinite-measure domain `R^d`. A subsequence converges weakly to some `b_j in L^s`.

For every `phi in C_c^infinity(R^d)`, a change of variables gives

`integral q_n phi dx`

`= integral sigma(x) [phi(x-h_n e_j)-phi(x)]/h_n dx`.

The bracket converges uniformly to `-partial_j phi`. For all sufficiently large `n` it is supported in a single fixed compact set and is bounded by `sup |partial_j phi|`. Also `sigma` is locally integrable by Holder's inequality. Therefore this integral converges to

`- integral sigma partial_j phi dx`.

On the other hand, weak convergence is testable against `phi`, because `phi in L^(s')`, where `s'=s/(s-1)`. Hence

`integral b_j phi dx = - integral sigma partial_j phi dx`.

This identifies `b_j` with the distributional derivative of `sigma`. Repeating the argument for each of the finitely many coordinates proves `sigma in W^(1,s)(R^d)`.

**Subsequence audit.** Each coordinate may have a different initial sequence and a different weakly convergent subsequence. Distributional identification is coordinatewise and yields the same uniquely determined derivative for any such choice. There is no need to synchronize the sequences.

An equivalent proof avoids extracting a weak limit: the test identity and the uniform quotient bound show that the distribution `partial_j sigma` defines a bounded linear functional on `L^(s')`; `L^p` duality represents it by a function in `L^s`. Both proofs depend on a finite exponent strictly above 1 in this formulation.

## 4. Sobolev regularity gives uniform overlap bounds

Suppose now `sigma in W^(1,s)(R^d)` and put `b_j=partial_j sigma`.

The Sobolev translation identity, in `L^s`, is

`sigma(x+h e_j)-sigma(x) = integral_0^h b_j(x+t e_j) dt`.   (4.1)

One way to justify (4.1) without choosing a pointwise representative is to convolve `sigma` with smooth approximate identities, apply the ordinary fundamental theorem of calculus, and pass to the `L^s` limit for the functions and their derivatives. Minkowski's inequality and translation invariance give

`B(h) <= h ||b_j||_s`.

Combined with (2.5),

`||W_h||_(L^s(rho)) <= 14 s h ||b_j||_s`.

This proves the finite limsup condition. A finite limsup trivially implies a finite liminf, completing all three equivalences.

The same identity, together with strong continuity of translations in `L^s` for finite `s`, gives

`q_h^+ = (sigma(x+h e_j)-sigma(x))/h -> b_j`,

`q_h^- = (sigma(x)-sigma(x-h e_j))/h -> b_j`

strongly in `L^s` as `h downarrow 0`. For example,

`||q_h^+-b_j||_s <= (1/h) integral_0^h ||b_j(.-t e_j)-b_j||_s dt -> 0`,

where either sign of translation gives the same continuity conclusion.

## 5. The zero set and the exact strong limit

### 5.1 Why the derivative vanishes on the zero set

Let `Z={sigma=0}`. Since the chosen representative is nonnegative everywhere,

`(-q_h^+)_+ = 0` on `Z`,

`(q_h^-)_+ = 0` on `Z`.

The positive-part map is 1-Lipschitz, so the preceding strong quotient limits imply

`(-q_h^+)_+ -> (-b_j)_+`,

`(q_h^-)_+ -> (b_j)_+`

strongly in `L^s`. Restricting to `Z` shows that both `(-b_j)_+` and `(b_j)_+` vanish there. Thus `b_j=0` almost everywhere on `Z`.

This argument independently establishes the level-set fact used in the synthesis proof. Alternatively, the Sobolev ACL representative is nonnegative on almost every coordinate line, and at a differentiability point where it is zero it has a local minimum and derivative zero. Either justification is valid. Merely saying that the density is zero there, without one of these Sobolev arguments, would not suffice.

### 5.2 Bounded multipliers

Define a continuous bounded coefficient for `t>=0` by

`c_s(t)=(1-t^s)/(1-t)` for `0<=t<1`,

`c_s(t)=s` for `t>=1`.

Then `1<=c_s<=s`; continuity at 1 follows from differentiating `t^s` at 1.

On `{sigma>0}`, define

`c_h^+(x)=c_s(sigma_+(x)/sigma(x))`,

`c_h^-(x)=c_s(sigma_-(x)/sigma(x))`.

On `Z`, set both coefficients equal to `s`. Then the following identities hold almost everywhere, including on `Z`:

`sigma d_+/h = c_h^+ (-q_h^+)_+`,

`sigma d_-/h = c_h^- (q_h^-)_+`.                         (5.1)

On `Z` this follows from the exact vanishing of the positive quotients just noted. Extending `c_s` by the constant `s` for ratios above 1 is harmless because the corresponding positive part is zero.

### 5.3 What convergence is actually available

One must not assert that arbitrary measurable representatives satisfy `sigma(x+h e_j)->sigma(x)` pointwise for every `h downarrow 0`. That assertion is unnecessary.

Take any sequence `h_n downarrow 0`. Translation continuity gives `sigma(. +/- h_n e_j)->sigma` in `L^s`. Extract a common subsequence along which both convergences hold almost everywhere. For example, select the subsequence so that the sum over it of the two `s`th-power errors is finite; Tonelli then gives the almost-everywhere conclusion.

At every point with `sigma(x)>0` where these convergences hold, both ratios tend to 1 and hence `c_h^+(x),c_h^-(x)->s`. On `Z` the coefficients were defined to be `s`. Therefore both coefficient sequences converge to `s` almost everywhere along this subsequence.

### 5.4 Dominated convergence is applied to a fixed limit, not moving quotients

Let `z_h` denote either positive quotient in (5.1), and `z` its strong `L^s` limit. Let `c_h` denote its coefficient. Since `|c_h|<=s`,

`||c_h z_h-s z||_s`

`<= s ||z_h-z||_s + ||(c_h-s)z||_s`.                     (5.2)

The first term tends to zero by the strong quotient convergence. The second tends to zero along the extracted subsequence by dominated convergence: its `s`th-power integrand is bounded, for instance, by `(2s)^s |z|^s`, an integrable fixed function.

Thus, along that subsequence,

`sigma d_+/h -> s(-b_j)_+`,

`sigma d_-/h -> s(b_j)_+`

strongly in `L^s`. Since every original sequence has a subsequence with this same strong limit, the limits hold for the full parameter `h downarrow 0`. Explicitly, failure of a full limit would give a sequence whose errors stay above a positive number, contradicting the extracted-subsequence conclusion.

This resolves both potential pitfalls: there is no unsupported full pointwise translation limit, and there is no use of dominated convergence with an unproved dominating function for the moving difference quotients.

### 5.5 The coefficient and sign

For `a_h=sigma d_+/h` and `b_h=sigma d_-/h`,

`sigma W_h/h = 6|a_h-b_h|+2a_h`.

The map on the right is Lipschitz, with error bounded by `8|Delta a|+6|Delta b|`. Its strong limit is

`s [6|(-b_j)_+-(b_j)_+|+2(-b_j)_+]`

`= s [6|b_j|+2(-b_j)_+]`

`= s [8(-b_j)_++6(b_j)_+]`.

This proves exactly the strong-limit formula in the synthesis. An increasing root (`b_j>0`) produces a backward loss and coefficient 6; a decreasing root (`b_j<0`) produces a forward loss and coefficient 8. Reversing these signs would be an error, but the synthesis does not reverse them.

Finally,

`||sigma W_h/h||_(L^s(dx)) = ||W_h||_(L^s(rho))/h`.

Continuity of the norm under strong convergence proves the claimed norm limit.

## 6. Density-level Sobolev regularity and the `L^1` corollary

Under the theorem, `sigma^(s-1)` belongs to `L^(s/(s-1))`, with norm 1 in the probability normalization. Holder gives

`s sigma^(s-1) b_j in L^1`.

To justify the weak chain rule despite the unbounded derivative of the power map, let

`r_N=(min(sigma,N))^s`.

The truncated power admits a globally Lipschitz extension as a function of its real argument. The Sobolev chain rule gives, almost everywhere,

`partial_j r_N = s sigma^(s-1) b_j 1_{sigma<N}`.

The choice of strict inequality at the level `sigma=N` causes no issue, because the weak derivative of a Sobolev function vanishes almost everywhere on every level set. Each `r_N` is integrable, and its displayed derivative is in `L^1` by Holder. Thus `r_N in W^(1,1)`.

Dominated convergence gives `r_N->r` in `L^1` and convergence of its derivatives in `L^1` to `s sigma^(s-1)b_j`. Passing to distributions proves

`r in W^(1,1)(R^d)`,

`partial_j r=s sigma^(s-1)b_j`.

Multiply the strong limit from Section 5 by the fixed function `sigma^(s-1)` and apply Holder. Because that factor is nonnegative,

`r W_h/h -> 6|partial_j r|+2(-partial_j r)_+`

strongly in `L^1(dx)`, precisely as claimed.

This is a recovery of the existing density-level formula on the root-Sobolev subclass, not a new broader formula. The subclass can be proper. For example, for a fixed `s>1`, take the normalized one-dimensional density

`r(x)=C x^beta (1-x)^beta 1_(0,1)(x)`, where `0<beta<=s-1`.

It belongs globally to `W^(1,1)`, because it vanishes at both endpoints and its derivative is integrable. But near an endpoint,

`|(r^(1/s))'|^s` is comparable to `x^(beta-s)`,

which is not integrable when `beta<=s-1`. Therefore a theorem for every `W^(1,1)` density is genuinely broader than this corollary.

## 7. Endpoints and exact analytic checks

### 7.1 The endpoint `s=1`

The algebraic profile comparisons remain valid at `s=1`. The failed step is the implication from bounded `L^1` difference quotients to an `L^1` weak derivative. `L^1` is not reflexive, and such bounded quotients can concentrate into singular derivative measures.

More precisely, the finite directional liminf condition at `s=1`, in all coordinates, characterizes `BV(R^d)`:

- Bounded difference quotients have weak-* subsequential limits as finite signed measures, and the distributional test identity identifies those limits with the derivative measures.
- Conversely, the standard BV translation estimate is `||r(.+h e_j)-r||_1 <= h |D_j r|(R^d)`; combining it with the profile comparison gives the overlap bound. This estimate also follows by smoothing a BV function, applying the fundamental theorem of calculus, and passing to the limit.

The endpoint failure is explicit. Let `d=1` and `r=1_(0,1)`. For `0<h<1/2`,

- on `(0,h)`: `d_+=0`, `d_-=1`, hence `W_h=6`;
- on `(1-h,1)`: `d_+=1`, `d_-=0`, hence `W_h=8`;
- on the rest of `(0,1)`: `W_h=0`.

Consequently,

`||W_h||_(L^s(rho)) = ((6^s+8^s)h)^(1/s)`.

At `s=1` the mean is exactly `14h`, although `r` is not in `W^(1,1)`: its distributional derivative is `delta_0-delta_1`. Also

`r W_h/h = (6/h)1_(0,h)+(8/h)1_(1-h,1)`

has norm 14 and concentrates to the measure `6 delta_0+8 delta_1`. It has no strong `L^1` limit. For every `s>1`, its overlap norm divided by `h` diverges, exactly as the theorem predicts for this non-Sobolev root.

If `r in W^(1,1)` is separately assumed at `s=1`, the strong `L^1` formula itself remains true: then the root is `r`, the multipliers are identically 1, and ordinary `W^(1,1)` difference-quotient convergence suffices. The invalid extension is the stated equivalence and its inference of that regularity from overlap control.

In the finite-moment parameterization `s=q/(q-2)`, the bounded-target endpoint `q=infinity` corresponds to `s=1`. It therefore cannot inherit a `W^(1,1)` characterization merely by taking an exponent limit.

### 7.2 No `s=infinity` statement is established

The density-root definition and weighted isometry are formulated for finite `s`; setting `s=infinity` is not a literal instance of them. In addition, translations of arbitrary `L^infinity` derivatives are not strongly continuous in the essential-supremum norm. Thus neither the current density-root formula nor the strong-limit argument can be extended to this endpoint by continuity. This does not deny that separate weak-* or Lipschitz difference-quotient characterizations exist; they would be different statements requiring their own formulation and proof.

### 7.3 Independent Gaussian sign check

For the standard one-dimensional Gaussian density, `sigma'=-(x/s)sigma`. The theorem predicts

`sigma W_h/h -> sigma(6|x|+2x_+)`.

The exact forward density ratio is `exp(-xh-h^2/2)`. At a fixed `x>0`, only the forward loss survives at first order, giving coefficient `8x`; at `x<0`, only the backward loss survives at first order, giving coefficient `6|x|`. At `x=0`, both deficits are second order and the first-order limit is zero. This independently checks the signs and coefficients. It is an analytic consistency check, not evidence replacing Sections 2--5.

## 8. Scope limits and suggested editorial clarification

No mathematical correction is required to Section 1. Two optional wording clarifications could make the argument harder to misread:

1. Explicitly define the multiplier to equal `s` on `{sigma=0}`; the products there are exactly zero. This avoids any appearance of dividing by zero in the strong-limit proof.
2. In the endpoint remark, say that the **equivalence** fails at `s=1`, while the strong `L^1` formula is still valid under a separately imposed `W^(1,1)` assumption. The current discussion is mathematically consistent, but this distinguishes the endpoint failure precisely.

Neither clarification changes the result. They are explanatory remarks in this review, not additional changes to the preserved Section 1.

This audit establishes no transport necessity theorem, no centered-potential estimate from root regularity, no realization or sharpness of the rearrangement envelope, and no literature novelty. The existing sufficient direction and existing `L^1` formula should continue to retain their prior attribution. The independent proof here supports the internal mathematical validity of the overlap/root equivalence and strong limit under their exact hypotheses; no external human review was performed, and no literature-priority certification is claimed.
