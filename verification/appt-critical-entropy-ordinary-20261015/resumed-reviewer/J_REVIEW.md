# Separate independent ordinary review of frozen J0-J3

15 October 2026, Asia/Shanghai. Reviewer: the resumed independent review
agent, separate from the author/root. This is an internal AI-agent
ordinary mathematical read, not external human peer review, Lean checking,
an expansion of old audits, or a historical-priority certificate.

**Conclusion: PASS for the complete J0-J3 mathematical target on the source
bound below, with the separately reviewed C/E/H/I inputs. No mathematical
correction, extra hypothesis, or narrowing is requested.**

This is a new full review. Neither the H nor the I PASS automatically
covered J. The reviewer found a numerical-helper defect in their own J
controls; its two actual failed executions and the eventual repair/PASS
are documented below and retained on disk. The manuscript was unchanged.

## Frozen source and actual read scope

The complete PAPER (230 lines), THEOREM_MAP (31 lines), and author's
checks.py (115 lines) were read and copied without alteration to snapshot/J/.
SHA-256:

- PAPER.md: `c2d5c37b950a029cf3919e4de0bf8950d6462b773fffc9b38499f5373fa0df8e`
- THEOREM_MAP.md: `73d73651e6b4e7be8ae42e11c28323c42653e0c8d9a6b86be34990885b10bcb6`
- checks.py: `62f80d031abcee308bb71fd8d8764341706d54eb6bbfd0877b128c5eef054c3f`

C461/E377/W292, H681/Map41/Followup28, and I313/Map38/History18 had all
been read in full during this resumed review. The separate H_REVIEW and
I_REVIEW reports bind their exact sources, conclusions, and limitations.
The main theorem dependency is H's full actual finite-window optimizer
classification together with I's complete scalar expansion and eventual
integer-onset enclosure. The present J proof supplies the extra curvature
condition for EVERY fixed positive order; its calculus alone is not
substituted for any of those physical quantum theorems.

## J0: unique nondegenerate maxima at every positive order

For the positive ratio, differentiation yields (4) exactly. The endpoint
values G_+(0)=2*alpha>0 and G_+(2)=-2*f'(2)<0 are correct. For
alpha<=7/2, G'_+<0 throughout the open interval, including the endpoint
case alpha=7/2. For alpha>7/2, its single sign change lies inside (0,2):
G_+ initially increases from a strictly positive value and then strictly
decreases to a negative value. It therefore has exactly one zero g and
the stated signs on either side. In particular, the proof does not make
the false all-order assertion that G_+ is decreasing everywhere.

Since F'_+=p*G_+, F_+ increases strictly from F_+(0)=0 to a positive
maximum and then decreases strictly to F_+(2)=-2*f(2)<0. Its unique
interior zero lies AFTER g. The ratio derivative changes sign precisely
there. At that zero R''_+=G_+/(2*alpha*p)<0, proving both uniqueness
of the global maximum and strict nondegeneracy. No upper or positive
lower restriction on the fixed alpha was used.

For the negative ratio, f''' has the correct sign from differentiating
psi(1-b), and (6) is exact. G'_-= -alpha*(alpha+1)*(1-b)^(alpha-2)
is strictly negative. G_-(0)=alpha>0. Its negative endpoint limit is
finite and equal to -2*alpha/(alpha-1) for alpha>1, minus infinity
for alpha=1, and minus infinity for 0<alpha<1. The explicit expression
in the latter case has the correct divergent coefficient. The separate
alpha=1 value is 1+2*log(1-b). Thus G_- has exactly one zero and F_-
again first strictly increases and then strictly decreases. At b->1,
f->1 and (1-b)*f'->0 for EVERY fixed positive order, so F_->-1.
Its unique zero lies on the strict decrease, and R''_-=G_-/(alpha*b)<0.
No derivative at b=1 or uniformly bounded singular endpoint derivative
was assumed. This proves the entire negative half and the full J0.

## J1: analytic critical branches and one transverse sign crossing

The integral representation (8) is the Taylor integral for psi with
psi''=alpha*y^(alpha-2). It proves joint real analyticity locally at
every alpha>0,y>0, including alpha=1, with no zero-denominator obstacle.
At each interior critical point the parameter second derivative is
nonzero by J0. The analytic implicit-function theorem applies to the
ratio derivative. The local branches coincide by uniqueness, so their
global continuation on (0,infinity) is analytic. The local arguments
never approach the singular negative endpoint; no uniform-in-alpha
compactness is needed for the stated analytic property.

At fixed anomaly parameter, differentiating (9) under its nonsingular
compact integral inserts log(1+u*p)>0 for the positive sign and
log(1-u*b)<0 for the negative sign, on every 0<u<1. The positive
weights yield STRICTLY signed partial derivatives. At an optimum the
anomaly derivative vanishes, so the chain rule gives these partials
as D'_+>0 and D'_-<0. The conclusion is stronger than a weak monotonic
comparison of suprema, and the written proof justifies that strength.

The exact comparisons (10) are valid: H4 gives the negative win at
alpha=1/2. The positive alpha=1 test p=1 gives log(2)-1/2;
the strictly truncated atanh series gives log(2)>56/81 and hence
log(2)-1/2>31/162>3/16. Strict decrease of D_- and
sqrt(5)<179/80 give D_-(1)<D_-(1/2)<3/16. These facts avoid
any numerical root certificate. The continuous difference D_+-D_-
has strictly positive derivative and opposite signs at the endpoints
1/2 and 1. It has exactly one zero alpha_x in that interval and the
crossing is transverse.

## J2: full leading phase and actual critical-window signs

Below alpha_x, d_alpha equals the strictly decreasing negative branch;
above it, d_alpha equals the strictly increasing positive branch.
This proves the unique global minimum and the different one-sided
derivatives at alpha_x without assuming endpoint limits as alpha->0
or alpha->infinity. Both critical maxima remain interior for every
fixed positive alpha by J0.

The finite physical sign conclusion correctly uses H's full-list
localization and exact finite-optimizer classification. A nonbulk
optimizer with the inactive sign along a sequence would violate that
localization. This is a statement on every optimizing actual matrix
in the entire fixed critical linear window, not an inference from
feasibility of a single scalar family. At the crossing both leading
critical profiles exist, one per sign, and both families are retained
in the finite formula. The manuscript expressly does not assert that
both necessarily win or tie at each finite dimension. Bulk, parameter
and integer-rank ties are not lost.

## J3: unconditional O(1) remainder with the original N quantifier

The parameter changes from p or b to z have finite nonzero derivatives
at every critical point. Since the first derivative vanishes there,
the z second derivative of each d_s has the sign of its anomaly second
derivative and is strictly negative. For a fixed alpha there is exactly
one globally critical point, or two at alpha_x. They lie inside the
compact I_alpha. The leading losses are quadratic in neighborhoods of
these points, the next scalar coefficients are Lipschitz, and the full
compact set outside these neighborhoods has a fixed positive leading
gap. Inactive sign branches are included in that gap argument.

I's UNIFORM expansion therefore bounds the maximization gain above
d_alpha*m^2+a_alpha*m by
max_v[-c*m^2*v^2+C*m*v]+O(1)=O(1). Evaluating a critical point
attaining the largest next coefficient gives the matching lower. At
alpha_x, a_alpha is the MAXIMUM over its two critical sign coefficients;
no uniqueness or false average is inserted, and a genuine tie is kept.

Finally I's two-ceiling enclosure transfers this O(1) statement from
the complete continuous crossing envelope to the actual minimal final
integer onset. The ceiling changes are bounded by 1+C*m^-3. I's full
physical classification and E0 glue already ensure equality for EVERY
integer n above the final onset, so the proof preserves the original
all-global-unitary APPT object and all-larger-n meaning of N. No
monotonicity of individual finite-rank winners, no lattice separation,
and no unconditional exact single ceiling are assumed. The improvement
from I's o(m) remainder to O(1) is thus unconditional for each fixed
finite positive alpha, as claimed.

## Independent controls, actual failures, and final PASS

I read the author's source-bound PASS at
`critical-order-transition/control-runs/20261015T064631.359276Z` as
author evidence and did NOT rerun it or call it independent checking.
I separately wrote j_independent_checks.py and ran my own controls.

The first actual run, `j-runs/20261015T065002.850890Z`, failed a numeric
alpha-derivative/integral comparison. A diagnostic-only message edit
and second run, `j-runs/20261015T065021.994809Z`, located the same failure
at alpha=1, positive sign. mp.diff through the piecewise raw quotient
at its removable alpha=1 singularity gave 0.04369590438686... rather
than 0.04369593283021.... Both source snapshots and FAIL results remain.
This was a numerical-helper defect, not a failure of the manuscript's
analytic integral. J_CONTROL_HISTORY.md records the observation.

The control now uses, only at alpha=1, the independently derived exact
identity

    partial_alpha(psi_alpha(y)/alpha)|1
                               = y*(log y)^2/2-psi_1(y).

Every other tested alpha continues to use direct numerical differentiation.
The complete corrected run `j-runs/20261015T065106.403365Z/RESULT.json`
is PASS. A later explicit check that the raw alpha=1 quotient raises
ZeroDivisionError strengthens the third shortcut control; the full
rerun `j-runs/20261015T065449.410035Z/RESULT.json` is also PASS.
The runs bind the exact H/I/J hashes, check 15 exact derivative
identities and 2 rational inequalities, and compares 30 two-sign critical
cases with direct ratio differentiation, second derivatives and the
integral alpha-slopes at 160-digit precision. Fixed tested orders span
1e-8 through 500 and include alpha=1 plus/minus 1e-25, 7/2 and its two
sides. A separate simultaneous three-variable stationarity/equal-value
solve finds the illustrative alpha_x around 0.5525205507 and a positive
transverse slope. This is a numerical diagnostic, not a rigorous rational
enclosure, an algebraic expression for alpha_x, or a proof of uniqueness.
The all-order uniqueness proof is the analytic F/G argument above.
Adversarial controls reject all-order decreasing G_+, a finite negative
endpoint G for alpha<=1, and raw alpha-1 division at the von Neumann point.

The earlier H/I reviewer control results stay separately bound and dated.
No author failure, predecessor evidence or current reviewer failure was
erased or mislabeled as another agent's execution.

## Scope and binding

The conclusion covers all J0-J3 for EVERY fixed finite positive alpha,
with no nondegeneracy exception. Constants and starting dimensions may
depend on that fixed alpha and are non-effective. This gives no varying-
alpha theorem, all-finite-dimensional formula, single exact ceiling,
ASEP statement, new Lean theorem or new major-conjecture count. The
bounded literature screen is not independently promoted to a priority
claim. No root tree, frozen input or old audit was modified in this review.

The conclusion binds the literal hashes above. Mathematical source changes
require a further read. Metadata-only publication changes require a precise
diff and explicit final binding rather than silent certification of new bytes.
