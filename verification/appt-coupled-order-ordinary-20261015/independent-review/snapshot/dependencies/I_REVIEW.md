# Separate independent ordinary review of frozen I0-I3

15 October 2026, Asia/Shanghai. Reviewer: the resumed independent review
agent, separate from the author/root. This is an internal AI-agent
ordinary mathematical review. It is neither external human peer review,
Lean verification, an expansion of older audits, nor a priority certificate.

**Conclusion: PASS for the complete I0-I3 target on the source bound below,
using the credited C/E inputs and the separately reviewed H0-H4 theorem.
No mathematical correction or narrowing is requested.**

The H report was completed first. This review separately reads and tests
the new general-order algebra, exact onset enclosure, and all-critical-tie
linear coefficient; it is not inherited automatically from H's PASS.
Further work beyond these frozen I sources is not covered by this report.

## Frozen source and actual coverage

The complete I manuscript (313 lines), THEOREM_MAP (38 lines) and
CONTROL_HISTORY (18 lines) were read and copied to snapshot/I/. SHA-256:

- PAPER.md: `593735fc7bfcd1988df370134a6b5b5b7e3a4204e56013ac1c574031d2b0a1f2`
- THEOREM_MAP.md: `0d6134fd820843c1a88292a58f3a16aa53e8ff39f97dcb2037d541cad0f118db`
- CONTROL_HISTORY.md: `4e00e3be4b5681f36ac52325d7a6f5abd7404b74ccf814a818b8ca424411f956`

Credited C/E/W source copies and the H 681-line manuscript were read in
full in this resumed review. Their literal hashes and full input scope are
recorded in H_REVIEW.md/H_REVIEW.json, completed separately before this
report. In particular the H dependency is PAPER SHA-256
`2faea5eb7112950d80602b07bfbfbf2cc82b851ff162acdfe997b3d05f29d105`.
The original APPT definition, positive finite order fixed before dimensions,
and true eventual/all-larger-n definition of N are retained.

## I0: exact normalized stationary values for both signs

I independently eliminated the real rank from Q*S=alpha*r*A. It gives

    S_* = alpha*(Q-r)*D/((alpha-1)*Q)
                   + alpha*(Q*h-r*H)/((alpha-1)*Q).

This is precisely s_alpha(r)*(D-g_s), with the signed h, actual H and g
in (5). The same equation gives A_*=Q*S_*/(alpha*r). Substituting into
the original entropy deficit yields the stated B_alpha(r)-log(1-g_s/D).
The constant inside B is Q/(alpha*r); its reciprocal would fail the
head-free check. Both signs use their actual trace increment, including
h=-beta in the negative case. No missing trace or head term occurs.

At alpha=1, the stationary equation is
r*(sum x log x)=(L-r)*S. The real trace becomes
(L/r)*D+(L/r)*h-H and therefore g=r*H/L-h. Direct substitution gives
B_1=L/r-1-log(L/r) and the same -log(1-g/D) form. This separately proves
the von Neumann case rather than applying a singular alpha-1 expression.
For each fixed positive alpha, the small-r factors have the needed signs
and nonzero leading coefficients; all limiting raw head values stay in a
compact positive interval on I_alpha. Uniform positivity/boundedness of g
follows from its limiting psi value. The continuous rank here is an
algebraic envelope, with physical ranks restored in the next step.

## I1: complete compact crossing and the two-ceiling eventual onset

The exact scalar crossing condition (7) follows by exponentiating the
stationary comparison. B'_alpha(r)>0 for sufficiently small r and r<t;
hence every denominator in (3) is positive. The scalar functions are
continuous on both copies of compact I_alpha, so their full maximum is
attained. Both signs can be retained even when one critical sign is
inactive; these remain genuinely feasible families.

H's uniform k_star/D=1/2+O(1/m) ensures that the actual adjacent integers
lie in [R,D-K]. The fixed-rank derivative gives curvature O(r^2/D^2)
near the stationary point, so both the head and bulk rounding losses
are O(m^-8) at cubic dimension. The manuscript compares their exact
floor/ceiling values and does not assume nearest-integer selection.

The exact n derivative in (9) is negative and uniformly of order m^-5
on the full fixed window and compact parameter/sign set. The O(m^-8)
rank errors consequently correspond to O(m^-3) uncertainty in n. With
a strict constant margin, the upper comparison controls every sign/z
candidate, and the lower comparison uses an attained full-envelope
maximizer at n_-=ceil(nu_star-C*m^-3)-1. Its physically valid integer-rank
state beats even the continuous bulk bound, so it certainly beats actual
integer bulk.

These comparisons concern the original quantum optimum because H0-H4
classifies EVERY possible optimizing matrix throughout that window.
The uniform expansion puts the crossing center in a fixed linear band.
Choosing the band's width to include the E0 upper band, and applying
E0 to every still larger integer n, gives bulk equality for ALL n above
the upper ceiling. A counterexample at n_- supplies the lower bound for
the MINIMAL final onset, without requiring monotonicity of intermediate
rank winners. Possible integer coincidences are correctly left inside
the two-ceiling enclosure; no Diophantine separation is asserted.

## I2: full linear coefficient and all critical ties

The finite signed mass is h_s(z)*(1+r/2), while the positive base varies
with derivative 1 and the negative base with derivative 0. Direct
differentiation gives the H_s(0), H_s'(0) in Section 4. Expanding the
exact quotient g, I independently obtain

    g_s=P_s+r*((b'_s+h_s/2)*psi'_alpha(1+h_s)
                              -alpha*h_s/2-alpha*P_s/2)+O(r^2).

This is exactly J_s in (10). A direct expansion of the alpha=1 formula
gives the same J with psi'_1=log; no derivative at zero is involved.

The body optimum is invariant under reversing logarithmic contrast and
swapping endpoint fractions, so its analytic expansion is even in
u=log(1+r). Its leading term alpha*u^2/8 proves (12). Analyticity (or
the explicit removable-factor formulas) permits expansion one order
further: the fourth-order coefficient contributes only O(epsilon^5)
to the contrast difference because the two contrasts differ by
O(epsilon^2). The denominator expansion and conversion from m-1 to m
then give precisely d_s=P_s/(alpha*z) and
a_s=2*J_s/(alpha*z)+3*P_s/(2*alpha). The error is uniform on the whole
compact parameter set. Both d_s are the original complete critical ratios
under their corresponding z changes, so every global critical point is
included in Z_alpha and no sign/parameter tie is removed.

Uniformity first yields nu_star=d_alpha*m^2+O(m). Compactness shows every
maximizing sequence approaches the ENTIRE critical set. At such a
maximizer the leading correction m*(d_s-d_alpha) is nonpositive, while
the limiting next coefficient is at most max_Z a_s. Evaluating a point
of Z attaining that maximum gives the matching lower. This proves
the o(m) remainder and the maximum-over-all-ties formula WITHOUT any
uniqueness or nondegeneracy assumption.

The optional O(1) refinement is explicitly conditional on isolated
strictly negative-curvature leading maxima. Under that stated condition,
the compact critical set is finite and quadratic leading losses dominate
linear changes in a_s. The argument is valid as conditional mathematics;
this report does not silently remove its condition for arbitrary alpha.

## I3: consistency and actual control history

At alpha=2, p=1,z=2,psi=p^2,psi'=2p; substitution gives J=1 and a=5/4.
This agrees with the independently earlier purity onset. At alpha=1/2,
substitution of the negative golden-ratio critical point gives
(27-11*sqrt(5))/2; H's unique nondegenerate maximum allows its stronger
O(1) remainder. These recoveries are correctly credited and not counted
as distinct major-conjecture solutions.

CONTROL_HISTORY correctly preserves the author's initial wrong J=2
consistency line, and the separate numerical helper's omission of compact
endpoints. The frozen I source has J=1. The complete argument maximizes
on compact intervals including endpoints; it does not depend on the
earlier interior-only diagnostic. I did not alter, erase, or relabel any
author failure as an independent-review execution.

## Actual independent controls and limitations

I wrote supplemental_checks.py during this resumed review (not the author
or predecessor reviewer). Its actual run
`supplemental-runs/20261015T063610.050259Z/RESULT.json` is PASS and binds
both frozen sources plus the credited input hashes. It checks 7 exact
symbolic elimination/derivative identities, 54 two-sign normalized
stationary/head-free evaluations, and 108 crossing-expansion cases at
250-digit precision. Tested positive orders include 0.17, 0.5, 0.9999,
1, 1.0001, 2, 7 and 1 plus/minus 1e-35. Numerical expansion residuals
are finite consistency checks; the analytic compact proof establishes
the quantifiers. Five adversarial variants are rejected, including
unweighted cube normalization, contrast positivity without variance,
the reciprocal stationary constant, the wrong negative trace sign,
and averaging the linear coefficients of critical ties. No unexpected
failure occurred in this new reviewer script.

I also read and actually reran the predecessor reviewer's unchanged H
script, as accurately attributed in H_REVIEW.md. It is supporting H
dependency evidence; it is not misrepresented as a personally authored
general-I proof. All reviewer snapshots/results are retained.

The bound is eventual for each fixed finite positive order. There is no
effective starting m, unconditional single exact ceiling, assertion for
all finite dimensions, growing-alpha uniformity, ASEP result, new formal
theorem, or priority certificate. No main tree, frozen input or old audit
was modified by this reviewer. The literal conclusion is source-bound;
mathematical changes need a further read, and metadata-only publication
changes need a precise diff and explicit final binding.
