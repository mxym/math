# Independent ordinary mathematical review of M0–M2

Decision: **PASS for the frozen M0–M2 mathematical scope specified below.**
This is an internal AI-agent mathematical read, independent of the author
agent's new M proof and controls. It is not blind, external human peer
review, a formal proof, an exhaustive priority search or an effective
dimension certificate. The same reviewer separately read I/J/K/L. Their
previous PASS decisions are dependencies, not an automatic PASS for M.

## Frozen source and actual reading

The full 222-line GLOBAL_ORDER.md and full 28-line GLOBAL_TARGET.md were
read. The manuscript is bound to SHA-256
`0b928b6c3f0b9636d6e8cb8eb0c7201f9f83c69b2b8e4d2f51b1967286875bec`;
the target to
`936780ba827e3023e1bfba31eb79c0f3f023775753bebab2f4dbc5776e047eb8`.
The reviewer captured these bytes before writing this report. The exact
line counts and complete copied-input hashes are in INPUT_MANIFEST.json.
The author M checker and its actual run result were read in full, without
execution. No author source was revised during this M review.

The separately reviewed L manuscript was read again in full here: 205
lines, SHA `c76f83bf7bb4a42eee81cafbab6fd8cdb430312fc7026503acbc86a9dfbda58b`.
In particular I rechecked its exact normalized crossing identity and
removable kernels, its physical adjacent-rank construction, the closed
FINAL-onset sublevel argument and the EVERY bounded-gap localization.
The L kernel identities (5a) were supplied by this reviewer during the
earlier L review and are openly credited there. This prior contribution
does not make the present review blind.

The exact I/J/K mathematical inputs had been read in full by this same
agent under their separate frozen-source reviews. Their published copies
at commit 5522928ae7e8b1960dedb790d7f3506f3b1f5f0b were previously compared
byte-for-byte after reversing only their disclosed final-status diffs.
That existing comparison, the published input copies and their separate
reports/bindings are retained here. I did not reclassify all actual
optimizers or rerun their controls. For M I specifically used I's actual
positive/negative boundary states and crossing identity, J's strict
critical-ratio order derivatives and unique crossing, K3's uniform FINAL
onset and L's fixed-compact-interval optimization theorem. The new escape
exclusions were examined separately rather than inferred from a fixed-order
limit. No Lean or old kernel audit was run or enlarged.

## Domain and quantified conclusion

The feasible set remains the original complex density matrices that are
PPT after EVERY global unitary. E_alpha is their attained maximal entropy
deficit; G_alpha is the exact integer projection bulk. N_alpha(m) remains
the least integer N>=m at which equality holds for EVERY later integer n,
and is +infinity if no such integer exists. For each m, alpha is held
fixed while that all-later-n condition is tested.

For sufficiently large common m, M proves a finite attained minimum over
the ENTIRE positive finite half-axis, with a nonempty closed minimizing
set, value `d0*m^2+ac*m+O(1)`, and location
`alpha0+uc/m+O(m^-2)` for EVERY minimizing order. Every order whose actual
N is within any fixed additive H of the minimum satisfies the same location
with an H-dependent constant. Infinite N values and all integer ties remain.
Orders may initially approach zero or grow with m without restriction.
The proof excludes those escapes before applying L on [1/2,2].

## M0: the arbitrarily small positive orders

The integral formula (M4) follows by Taylor's theorem from
`psi_alpha''(y)=alpha*y^(alpha-2)` and the zero value and first derivative
of psi_alpha itself at y=1. With the fixed negative limiting head h in (-1,0), all bases are
positive. Dividing by alpha gives a jointly analytic function through
alpha=0. Differentiating the integral in alpha is strictly negative at a
negative head. Thus the fixed-z ratio is decreasing and its minimum on
[0,1/2] is D_-(1/2), strictly above d0 by J. This is an exact gap; the
decimal examples play no role.

M's (M6) is the exact substitution w=alpha*w0 into L's (5a). In particular
`v=(alpha-1)*w0`, not a quantity singular at zero. The quotient
`log(1+alpha*w0)/alpha` is analytic there. The normalized g_s/alpha is
analytic as well; its limiting value is positive and uniformly bounded
away from zero for the chosen head. One must extend g/alpha and the body
difference/alpha, rather than bound their unscaled remainders.

Writing epsilon=1/m makes kappa=2*epsilon/[1+(z-1)*epsilon] and
t=2*epsilon/(1-epsilon) analytic. The body difference divided by alpha has
leading term `-z*epsilon^3`; g/alpha has leading term
`psi_alpha(1+h)/alpha`. In the exact crossing denominator
`1-exp(alpha*[body_difference/alpha])`, the alpha*epsilon^3 factor is
removable with a nonzero remaining factor. Therefore the crossing expansion
`nu=R_-(alpha,z)*m^2+O(m)` has ONE uniform remainder on [0,1/2]. It is not
obtained by choosing a maximum of pointwise cutoffs.

The exact n derivative of the real score minus B_alpha(t), after dividing
by alpha, is

    -(g/alpha)/[m*n^2*(1-g/(mn))].

It is uniformly bounded above and below in absolute value by constant
m^-5 for n in the relevant fixed comparable-m^2 interval. The crossing
exceeds the common test n_m by a positive multiple of m^2. Integrating
the derivative produces a genuine `c*alpha*m^-3` advantage.

The real-rank maximizer and rounding can also be regularized at alpha=0.
Put Q=alpha*Q0 and H=alpha*H0. Its exact rank formula becomes

    k*=[Q0*(D+h)-kappa*(D+alpha*H0)]
                                      /[(alpha-1)*kappa*Q0].

Here Q0=log(1+kappa)*expm1(alpha*log(1+kappa)) /
`[alpha*log(1+kappa)]`, continued at zero. Expanding the canceled kappa
factors gives k*/D=1/2+O(1/m) uniformly. Since D is a positive constant
times m^3, its adjacent integers satisfy the actual physical rank bounds
R=m(m-1)/2 and D-K with K=m(m+1)/2 for all sufficiently large common m.

For raw trace S=D+kappa*k+h and power sum A=D+Q*k+H, the exact second rank
derivative divided by alpha is

    [kappa^2/S^2-alpha*Q0^2/A^2]/(alpha-1).

This is uniformly O(kappa^2/D^2) even at alpha=0. Adjacent-rank loss is
therefore O(alpha*m^-8). It is dominated by the above advantage uniformly
for EVERY positive alpha<=1/2, however tiny. The rounded state beats the
continuous body maximum and hence also the exact integer bulk. The
positive extension at alpha=0 is only an analytic device; M makes no
entropy-improvement assertion at the zero order itself.

## M1: the growing and unbounded positive orders

For 2<=alpha<=alpha_star, alpha*kappa=O(log(m)/m) tends to zero uniformly.
The exact continuous bulk rank expands as 1/2+O(alpha/m) as a fraction of
D. Its objective has a single derivative sign change, so EVERY integer
bulk winner is one of the adjacent ranks, including all ties. It is
physical, uniformly in this range. The positive z=2 boundary family at
this actual winning rank is original all-unitary APPT independently of
alpha. The comparison uses this same integer rank at t and at kappa;
there is no continuous-rank loss hidden in the bulk side.

The estimates (M10) are uniform because both exponent arguments
`alpha*log(1+kappa)` and `alpha*log(1+3*kappa/4)` tend to zero. The power
increment H is `2^alpha-1+O(alpha*2^alpha/m)`. Also
`H/D=O(m^-1/2)`, since 2^alpha_star=m^(5/2) and D~d0*m^3.

The exact subtracted head logarithms are essential. Writing theta=k/D,
their first D-scaled term is

    D*log(1+H/[D*(1+theta*Q)]),

equal to `2^alpha-1+O(2^alpha*(alpha/m+m^-1/2))`. The trace term is
`alpha+O(alpha/m)`. After subtraction, the leading numerator is
`2^alpha-1-alpha`. For all alpha>=2 it is at least 2^(alpha-2): equality
holds at two and the derivative of `(3/4)*2^alpha-1-alpha` is already
positive at two and increases. Thus every error is absorbed relative to
this numerator before division by alpha-1. This proves the uniform
relative lower bound (M11), including its left endpoint.

I independently factored the exact fixed-rank body derivative as

    alpha*theta*(1-theta)*expm1((alpha-1)*log(1+r))
      /[(alpha-1)*(1+theta*expm1(alpha*log(1+r)))*(1+theta*r)].

Consequently its ratio to alpha*theta*(1-theta)*r is 1+O(alpha*r)
throughout kappa<=r<=t. The two denominators are positive and close to
one; the remaining quotient is regular and has that uniform expansion
whenever alpha*r is small. This argument controls the apparent
cancellation in the original derivative and proves (M12).

Integration, theta*(1-theta)<=1/4 and the exact identity
`t^2-kappa^2=16*m/(m^2-1)^2` give (M13) with a common error of order
O(log(m)/m), including the O(m) change in n_m. The head gain divided by
alpha is at least `(psi_alpha(2)/alpha)*(1-o(1))` and the body loss divided
by alpha is at most `2*d0+o(1)`. The integral formula at h=1 makes the
former kernel increasing in alpha and >=1/2. J gives the strict exact
inequality d0<1/4, so the difference is uniformly positive on the ENTIRE
growing window, not merely at finitely many orders.

At its endpoint, the same actual state's own deficit is at least
`c*psi_alpha_star(2)/D`, because its normalized body deficit is nonnegative.
Since psi_alpha_star(2) is comparable to m^(5/2)/log(m), this is
`c*m^-1/2/log(m)` as in (M14). This is a bound for the unscaled entropy
deficit, not just for a D-scaled increment.

Now fix that one state, with the rank and all matrix entries chosen at
alpha_star. Convexity of log(sum lambda_i^alpha), with value zero at one,
makes its secant slopes from one increasing over all positive orders;
those slopes equal the state's entropy deficit up to the constant log D.
This proves deficit monotonicity without reselecting the state. Every
projection-bulk state has `D*lambda_max<=1+t`, hence at EVERY positive
order its deficit is <=log(1+t)=O(1/m). The bound
`m^-1/2/log(m)>>m^-1` eventually beats it. The same fixed state therefore
works for EVERY alpha>=alpha_star, with no bound or relation to m. The
two intervals overlap at alpha_star and cover all alpha>=2.

## M2: full-axis attainment and EVERY fixed-gap order

All exclusions occur at the SINGLE integer
`n_m=floor(d0*m^2+(abs(ac)+2)*m)`. Failure there forces N_alpha>n_m under
the original all-later-n definition, even if equality happened earlier.
This implication applies to the entire exterior of (1/2,2), including
endpoints, and also accommodates N_alpha=+infinity.

L's inside candidate has N<=d0*m^2+ac*m+C<n_m. The set of finite integer
N values is nonempty, and no exterior order can realize the least one.
Thus the global minimum equals L's compact minimum. Its minimizing set
is L's nonempty closed subset of [1/2,2], lies in the interior and is
compact in the full positive half-axis. L gives its value and EVERY
minimizer's stated second-order location.

For each fixed H, the gap n_m-M_[1/2,2] grows at least linearly, since
abs(ac)+2-ac>=2. Hence eventually EVERY order with N_alpha<=M+H also
lies in (1/2,2). L's bounded-gap theorem applies without a selected
subsequence or a uniqueness assumption and gives the same location with
an H-dependent constant. No all-positive-order exact optimizer
classification has been inserted into this reasoning.

## Actual controls and limitations

The author run 20261015T083026.400414Z was copied and hash-checked, not
reexecuted. It reports 18 tiny-order cases to 1e-1000, 15 growing-order
comparisons, 45 derivative cases and 15 later-order samples to 1e12.
Its AST selection of nine pure scalar author-L functions is explicitly
disclosed. The prior L constant-result bytes that it reads were also
captured and their SHA checked.

The reviewer wrote a new scalar implementation with no imported or
AST-selected author functions. Its final run 20261015T084023.622885Z passes four
symbolic checks, 15 tiny-order/analytic-zero-limit cases (12 positive
cases, smallest 1e-500), 15 growing-order actual-state comparisons, 45
derivative cases and 15 fixed-state later-order samples to 1e30. Three
incorrect proof variants raise and retain real AssertionError records.
Alpha_0 and d0 were resolved anew for illustration; a_c was taken from
the same reviewer's earlier L diagnostic, with its exact result bytes and
SHA retained. No numerical interval certification is claimed.

One earlier reviewer checker run genuinely FAILED because I imposed an
unsupported rank-loss constant ten. The actual scaled loss was about
12.589, compatible with the source's unspecified finite O constant and
the derived leading worst-rounding coefficient 1/(2*d0^2), about 15.89.
Only that diagnostic bound was repaired to 2/d0^2 for the first successful
run 20261015T083604.420048Z, and the original executed source and failure
remain. The final successful run changes only the prior-result input to
its byte-identical local snapshot and clarifies the phi helper docstring;
all controls and numerical assertions remain the same. CONTROL_HISTORY.md
records all three runs. This was not a mathematical-source correction or
a hidden PASS.

The finite evidence cannot verify all actual quantum states, the
continuum of orders, arbitrary unbounded orders or all later dimensions.
The proof read above supplies those quantifiers through actual witnesses,
uniform estimates, monotonicity and the separately reviewed K/L theorem.
There is no stronger arbitrary-moving-order entropy theorem, exact finite
onset/minimizer, effective cutoff, new Lean result, old audit extension,
external human review or additional major-conjecture solution in this
PASS. Existing bounded primary-source screens are credited context; I
have performed no new exhaustive literature or priority investigation.
Final publication metadata and any later manuscript changes require
their own source/status binding.
