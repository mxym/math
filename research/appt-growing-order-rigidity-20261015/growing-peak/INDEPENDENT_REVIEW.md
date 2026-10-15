# Independent ordinary review of growing-peak rigidity (S6)

Decision: **PASS**, separately for Theorems A, B and C, for the exact frozen
manuscript identified below. This is an internal independent AI-agent
mathematical reading. It is not Lean verification, external human peer review,
a priority certificate, or a count of a newly solved major problem.

The reviewed PAPER is 14,789 bytes, SHA-256
`2374564f1f2cd3c576c3528d8acfda3f9a729ae08f506621f930ed42b33fd227`.
The owner ZIP is
`4cf416671bacc623e24492d95769e22f75fdf3822c3b172a37cd4c35f24e6803`;
AUTHOR_V1_MANIFEST.json is
`c3ac74c2808473892a46302a934a59fa0dc9d9063b4e77ab7b386fa264086b1e`.
The ZIP was copied and safely extracted into this private review directory.
INPUT_VERIFICATION.json verifies all 23 listed files, the manifest itself,
and equality of each of the 12 credited scientific texts to a previously
fully read private copy. No author or root file was modified.

The domain is every fixed finite C>0 and every sequence of original complex
PSD, trace-one density matrices that remain PPT after **every global unitary**,
with integer 2<=m<=n, m tending to infinity, real alpha tending to infinity,
alpha<=Cm eventually, and chi=alpha log[3D/(D+2)]-log D tending to positive
infinity, D=mn. All n>=m are allowed, including unbounded and oscillating
aspect ratios, and alpha/m need not converge. Errors are uniform over the
actual density matrices and aspect ratios under these conditions. This is a
statement about the physical APPT set; the necessary spectral inequalities
are never treated as a sufficient characterization of it.

## Actual read scope and dependency boundary

I read the complete new PAPER, THEOREM_MAP, README, TARGET, SOURCE_INPUTS,
ATTEMPT_LEDGER, PRIMARY_SCREEN, manifest, author_peak_controls.py,
AUTHOR_EXACT_CONTROLS.json, and the two initialization/freezing programs. The
last programs were read as historical provenance, not executed. I reread G
Sections 1--3 through G22, including all definitions and the all-aspect range
of its physical estimates. The complete G and the other 11 credited
scientific manuscripts had already been fully read in the separate S5 review;
each new captured copy was compared byte for byte with that old reading.
This reuses a reading of identical **old input text**, not the conclusion of
the S5 theorem. The present proof does not invoke S5, the phase-four scalar
geometry, or an unreviewed synthesis theorem.

The physical dependencies actually used are G7--G18: actual unitary Schmidt
witnesses, the pivot b>0, star/paired-gap estimates, normalization, the bounded
middle and exceptional estimates, the actual second-peak gap, the exact
first-peak ceiling and its attainable pure-spike state, and trace-centered
real powers. G explains why those inequalities apply for every n>=m; no
D comparable to m cubed or bounded-aspect assumption enters them. Earlier
ordinary written results are credited as such. I have not rerun or enlarged
any previous Lean audit. The remaining credited manuscripts establish the
prior value/spectral scope and are not new dependencies of the proof here.

I did not independently repeat the author's primary-domain searches. I read
their recorded bounded search scope, and make no assertion of exhaustive
literature coverage or historical priority. There is no new external paper
used to close the proof in this report.

## Theorem A: the bound is genuinely uniform over actual states

For sufficiently large m, the actual middle interval is B={R,...,j}, with
R=m(m-1)/2, j=D-m(m+1)/2+1, and exactly D-m^2+2 entries. Its complement E
contains the largest index and has m^2-2 entries. G gives |y-1|<=delta_m on B,
delta_m=O(1/m), Q_E<=C_m=O(1), and Q<=zeta_m(n/m+8). These constants are
independent of n and the actual matrix. In particular a cardinality estimate
of m^2 for E is not being substituted for its bounded square mass.

For real alpha>=2 the integral remainder H_alpha(y)>=0 is valid for every
y>=0, including zero eigenvalues, and is at most
alpha(alpha-1)(y-1)^2 V^(alpha-2)/2 whenever y<=V and V>=1. Trace one gives
the exact sum of these kernels D(M-1). Separating the actual largest kernel
therefore gives the exact equation (4.3), including the subtraction
1+alpha(y_1-1). No cross term or trace-normalization loss is discarded as an
identity.

The middle estimate is uniform even when n/m diverges. Indeed
Q_B/D<=zeta_m(1/m^2+8/D)<=9 zeta_m/m^2; alpha<=Cm then gives a finite K_C.
For an explicit independent common bound, after m>=64 the displayed G
constants imply m delta_m<6 and zeta_m<2. Thus one may take
K_C=9 C^2 exp(6C), whenever alpha>=2 and alpha<=Cm. The argument uses only
the upper bound on alpha/m, so allows every bounded oscillation of this ratio.

All remaining exceptional kernels use the actual second eigenvalue and
Q_E, giving R_E<=a_alpha C_m v_m^(alpha-2). Here v_m tends to 1+sqrt(2),
whereas the exact u_D tends to 3 uniformly in n>=m. Eventually v_m<=5/2 and
u_D>=8/3. Consequently the three errors in (4.4) are bounded by
(1+K_C) exp(-chi), (1+2alpha)/u_D^alpha, and
O(alpha^2 (15/16)^alpha). They tend to zero independently of n and the state.
This proves M/r=exp(-h)+o(1), without a restriction to a candidate family.

For the matching lower bound, (I+2vv*)/(D+2) is an actual APPT density:
every transformed pure projector has partial-transpose least eigenvalue
at least -1/2. Its exact moment is r plus a nonnegative actual tail term.
Thus M*/r tends to one and log M*=chi+o(1). No claim that the spike is an
exact finite maximizer is required. As r and M* diverge and M>=1, relative
raw moment and relative moment excess agree asymptotically; the actual
nonnegative loss h yields both equivalences in (2.3).

## Theorem B: logarithms need an actual peak first

I checked the necessity argument separately from (4.4); taking logarithms
of its additive o(r) error would be invalid. If y_1<=3-epsilon along a
subsequence, the actual ratio u_D/y_1 has logarithm at least some eta>0.
Bounding **all** exceptional kernels by the actual ceiling y_1, while
retaining the separate K_C middle estimate, gives (5.1). The polynomial
factor in alpha is absorbed into exp(eta alpha/2) using alpha tending to
infinity. It is not absorbed using an unjustified log alpha=o(chi).
Since 0<chi<=alpha log 3 eventually, the resulting log sum has ratio to chi
bounded strictly below one. This proves y_1 tends to 3 for every relatively
entropy-optimal actual state path, even when chi/alpha tends to zero.

Once the **actual** y_1 is at least 8/3, the exceptional error relative to
y_1^alpha is O(alpha^2 (15/16)^alpha). Using M>=1 and M>=T_p exactly, where
T_p=y_1^alpha/D=exp(chi-h), gives
max(1,T_p)<=M<=T_p(1+epsilon_m)+1+K_C. Therefore
log M=(chi-h)_++O_C(1). This is an absolute bounded logarithmic error
relative to the state's own peak, not the logarithm of a coarse o(r) error.
The estimate suffices because chi tends to infinity with no lower bound
on chi/alpha.

Necessity now gives (chi-h)_+/chi tending to one, equivalent to h/chi
tending to zero because h>=0. Conversely h/chi tending to zero and
chi<=alpha log 3 force h/alpha tending to zero and actual y_1 tending to 3;
the state-relative estimate then proves entropy optimality. Both directions
retain the original real-order and all-aspect quantifiers.

## Theorem C: total tail moment, actual tail and rank

Either criterion implies h/chi tends to zero and hence T_p tends to infinity.
Dividing the exact centered equation by T_p controls the full middle term
by K_C/T_p, the entire exceptional remainder by the square-energy estimate,
and the baseline and centering polynomial by quantities tending to zero.
This proves M/T_p tends to one and the **sum** of all nonpeak powers divided
by y_1^alpha tends to zero. It avoids an uncontrolled factor D or m^2.

The geometric conclusion uses the actual pivot and star budget. Since
a_1=t y_1-1 tends to 2, 0<=beta_1 and a_1+beta_1=g_1<=2 imply beta_1 tends
to zero and g_1 tends to 2. Then g_2^2<=4-g_1^2 tends to zero. Sorting bounds
all other top pivot deviations by a_2<=g_2; every bottom deviation is at most
beta_1; the remaining upper middle deviations are at most 2/(m-1).
Multiplication by 1/t, with t tending to one, proves the claimed uniform
max over **all** i>=2. The least eigenvalue is thus eventually positive.
Finally y_2/y_1 tends to 1/3 and alpha diverges, proving the power-ratio
assertion. A weak empirical bulk law or a presumed single-spike shape has
not replaced any of these physical losses or estimates. No J saturation
condition is inferred or needed in this diverging-peak regime.

## Actual examples and independent controls

The credited square-dimension reduced-spike example has alpha=m,
coefficient 2-alpha^(-1/2), h asymptotic to sqrt(alpha)/3 and chi asymptotic
to alpha log 3. Its all-unitary APPT property follows from coefficient<=2.
It is relatively entropy optimal and fails sharp moment optimality.

I independently checked the **paper's** exponential-ceiling example, not
just the author's rational-ceiling substitute. For integer k, m=alpha=k^2,
n=ceil(3^m exp(-k)/m), the ceiling changes D by less than m and thus changes
chi by o(1). With coefficient 2-3/k, the normalized peak gives
h=k+1/2+O(1/k) and chi=k+o(1). Thus T_p tends to exp(-1/2), while the
actual tail moment tends to one and M tends to 1+exp(-1/2). This proves
relative entropy/optimum tends to zero despite y_1 tending to 3 and
h/alpha tending to zero. It also supplies a physical counterexample to
inferring total tail negligibility from a decaying second-peak ratio alone.
The integer dimensions and trace normalization are retained throughout.

The independently written independent_checks.py imports no author helper
and executes no author program. Its successful run was
`runs/20261015T142527.968604Z`, with Python 3.10.12, Sympy 1.9, Mpmath 1.2.1
and 800 decimal digits. It checked seven symbolic identities, 576 exact
compressed actual-state/order cases, 54 finite uniform-bound diagnostics,
four actual exponential-ceiling paths and four reduced-spike separation
paths. The finite bound diagnostics use the stated G constants rather than
a fitted constant. Samples support implementation and algebra only; they
do not prove the universal feasible-set statement.

For these controls, three-level states were constructed as
(I+a vv*+sP)/(D+a+sk), with P orthogonal to v, integer rank k and
a+(m-1)s<=2. The pure partial-transpose bound is -1/2. For any projection,
the negative trace of a partially transposed unit pure projector is at most
(m-1)/2, by the Schmidt coefficients and their sum<=sqrt(m). The variational
identity Tr(PA)>=sum of the negative eigenvalues of A therefore gives
(UPU*)^Gamma >=-(m-1)I/2 for every U. This proves the sufficient APPT
condition used in the finite families. The controls do not assume an
arbitrary necessary-inequality spectrum is physically feasible.

Seven deliberately false variants were actually executed in separate
processes and rejected by the intended AssertionError, with stdout/stderr
retained: omitting trace centering; treating the finite peak approximation
as an identity; replacing the entropy loss by h tending to zero; dividing
h by alpha instead of chi; converting a coarse error to a relative peak
error; bounding the whole tail by the second-peak ratio alone; and forgetting
trace normalization. Asymptotic separations for the third, fourth and sixth
are justified analytically above, rather than asserted from a finite sample.

There was one genuine unexpected **reviewer-checker failure**, retained at
`runs/20261015T142447.829759Z`: an expanded Sympy polynomial was compared
structurally with an unexpanded equivalent product. The asserted mathematical
identity is true. The original source was copied before the assertion; the
actual tool traceback and return code 1 are retained. The corrected check
expands the difference and tests it against zero. FIRST_REVIEWER_CONTROL_FAILURE
records this issue and the correction. No author mathematical source was
changed, and the first run is not called a PASS.

The author's 21-case finite-control source and stored result were read and
hash-verified, **not independently executed**. Their original UTC and result
remain intact. In particular their near-window test explicitly uses the
parallel rational rule n=ceil(3^alpha/(m 2^k)), not the manuscript's exp(-k)
path. Neither set of finite diagnostics substitutes for Sections 3--7.

## Scope of this decision

Theorems A--C and the stated distinctions pass for the exact source and
quantifiers above. I found no author-source mathematical or scope error in
this manuscript. The one actual unexpected failure was in my checker.
The author-pending banner is the historical frozen source status, and was
not edited by this review.

This review does not cover alpha/m tending to infinity, fixed m, bounded
alpha, alpha tending to zero, finite chi, exact finite optimizers, a complete
all-diverging-order synthesis, or any later manuscript. It does not certify
future publication metadata, transport or repository layout. No Lean was
run or expanded, no author/root/Gaussian worktree was modified, no new
subagent was created, and no commit, push, submission or external message
was made.
