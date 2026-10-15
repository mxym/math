# Independent ordinary review of corrected and strengthened P0–P2

Decision: **PASS for the final frozen mathematical source below, after a
real P2 corollary-range correction and a separately checked P0/P1
strengthening.** The original unqualified fixed-m P2 range was false and
is not certified by this decision. L/M or any earlier PASS was not used
as automatic coverage for this new theorem.

This is an internal AI-agent mathematical read. It is not blind (the
reviewer supplied the range counterexample), external human peer review,
Lean verification, an exhaustive literature search or a priority
certificate. No author source was edited or author control executed by
this reviewer; the author made the disclosed corrections/strengthening.

## Bound sources and actual reading

The final PAPER.md was read in full: 192 lines, SHA-256
`3d038944ad35c16fb1c3c99db4fcc096f3a12e543016048a002c035712516e06`.
The final 31-line THEOREM_MAP.md is
`d2976594b5780cdf94b3bbbacbc90de48033ab9fb19fcb4683cc791ded864f10`;
the 32-line REVIEW_HISTORY.md is
`825d85c91ef3b52d8c47bb66a7a8b13070d5eb0df9caf5d5b3f5ac8f5ebc1047`.
Both were read fully, as was the final 93-line author checker. Both earlier
manuscripts/maps were also read fully and their exact bytes remain:
original c719b61b.../85a416fd... and corrected v2 50d20926.../8481ff22....

The 259-line SHARP_ASYMPTOTIC.md was read in full, SHA
`49b71670f33283f1018c915d07b11c509266395f3a201dc19bb627cd932bc2f9`.
Its research and supplementary-preprint copies are byte-identical. Its
finite Sections 2–4, rather than its m-growing asymptotic theorem, supply
the graph input. Section 8 supplies the independent bounded-order
countercontrol used below. The 461-line cubic-entropy input is the
previously read frozen source
`a2e940d320950c258d2aed13bb5afa81ea3bc41efa74acc09dca703d0a817449`;
in this task I specifically reread Section 4's exact physical inequalities
and separated them from its later fixed-order/cubic-regime estimates.
No cubic entropy limit or fixed-order Taylor remainder is used for P.
No Lean declaration, kernel audit or formalized scope was widened or run.

## P0 and P1: exact range under review

For EVERY integer 2<=m<=n and EVERY real alpha>=2, write D=mn,
a=alpha-1, q=(m+1)/(m-1), and

    T=max(log q, log3-logD/a),
    L=log(2alpha)/a+4/alpha+4/D,
    U=2m/(D-m)+(2log a+log48+2)/a.

The final proof establishes T-L<=E_alpha<=T+U on the ORIGINAL complex
trace-one PSD matrices which remain PPT after EVERY global unitary.
There is no hidden dimensional or order cutoff in these finite bounds.
Both lower constructions are actual feasible matrices; the upper applies
to the entire actual feasible set, not an assumed complete spectral ansatz.

The conclusion is a uniform absolute formula with error
O(D^-1/2+log(alpha)/alpha) when D and alpha both tend to infinity. The
constant is independent of all m,n,alpha in the specified range. Fixed,
growing and oscillating smaller dimensions and orders above D are covered.
No relative equivalent is asserted when T tends to zero, and the formula
need not have one scalar limit when m oscillates.

## Exact finite graph inputs across every dimension

Set R=m(m-1)/2, K=m(m+1)/2 and b=lambda_(D-K+1). The top R and bottom K
slots are disjoint because R+K=m^2<=D, including D=m^2. The maximally
entangled Schmidt test, with top values in negative directions, gives

    R*kappa+sum p+sum beta <= K-R=m.

Thus 0<=kappa<=2/(m-1) and total anomaly mass <=m, as exact finite
inequalities. The normalized coordinates have kappa=x_R-1>=0 by their
sorted indices. All p and beta entries are nonnegative, and p_R=0.

For ANY assignment of paired gaps delta_i=lambda_i-lambda_(D+1-i) to
the complete graph, the actual all-unitary witness realizes that
assignment. Its diagonal contributions are each <=b. Taking the
nonnegative maximizing Rayleigh vector proves ||A_delta||<=2b; absolute
values of a vector give the lower-eigenvalue bound as well. This requires
neither D~m^3 nor bounded contrast-defect c. A Schmidt vector supported on
two coordinates proves lambda_1-lambda_D<=2b even for m=2. If b=0 this
forces the whole trace-one spectrum to vanish, a contradiction. Therefore
b>0, and lambda_D<=b also gives 0<=x_i<=3.

For m>=3 put w=delta_R and eta_i=delta_i-w. The paired gaps, hence eta,
are decreasing and nonnegative. A star gives at most 4b^2 for the first
m-1 eta squares. A DIFFERENT permitted rearrangement puts eta row by row
and adds w to every edge. The exact degree-square expansion in SHARP
Sections 3–4 bounds ||A_eta e||^2 by 4b^2 after dropping nonnegative
baseline terms. Its row lemma bounds all remaining eta squares by this
quantity. Hence sum eta_i^2<=8b^2. Dividing by b and using

    eta_i/b=p_i+beta_i-beta_R >= p_i

gives sum p_i^2<=8. There is no spectral-level count restriction and no
large-aspect or large-m step here. For m=2 the row lemma is unnecessary:
R=1 and p_1=p_R=0 exactly. The entangled and single-edge inequalities
still apply, so this exceptional dimension is included.

Only bottom-K values can be below one. Their exact total deficit is
sum beta<=m, whence the ACTUAL raw mean s>=1-m/D>0. In particular the
normalization error is D-dependent. Replacing it by a generic O(1/m)
estimate would not justify fixed-m sequences. The proof does not do that.

## Strengthened upper bound and every logarithmic constant

Take epsilon=1/a, which lies in (0,1] for the entire finite range,
including alpha=2. An index with x_i>q+epsilon lies in the top R and has
p_i>epsilon. The square budget bounds their number by 8a^2, whether or
not this bound exceeds R or D. All remaining x_i are <=q+epsilon and
every x_i<=3. Thus the raw alpha-power mean is at most

    (q+1/a)^alpha + (8a^2)*3^alpha/D.

The exact deficit is
`[log(raw power mean)-alpha*log(s)]/a`. The log-sum-exp inequality adds
log2/a. Its head branch is exactly bounded by

    log3-logD/a+(log24+2log a)/a.

The log24 includes the factor 8 and the extra log3 from alpha/a. For the
bulk branch, log(1+epsilon/q)<=epsilon/q and alpha/a<=2 give

    (alpha/a)*log(q+epsilon) <= log q+(log3+2)/a.

Since log a>=0 and log24>=log3, the common branch error
`(2log a+log24+2)/a` bounds both. Adding log2/a yields precisely
`(2log a+log48+2)/a`. Finally -log(s)<=m/(D-m) and alpha/a<=2 bound the
mean contribution by 2m/(D-m), even when the actual s is above one.
This proves the final U with no small-epsilon approximation, no hidden
alpha threshold and no unnormalized replacement of entropy.

This cutoff strengthening was authored AFTER the correction of P2. I
read its complete new source/map/proof separately and reran the independent
finite checks with the new U. An earlier successful weaker-U run does not
automatically certify it.

## Both physical lower constructions and all integer ranks

The partial transpose of a pure-state projector has eigenvalues s_i^2
and +/-s_i*s_j. Since every product is <=1/2, I+2|v><v| remains PPT after
every global unitary. Its exact trace is D+2. Its exact power expression
gives the head branch at least log3-logD/a-4/D: retaining 3^alpha,
discarding only the nonnegative log3/a remainder, and using alpha/a<=2
and log(1+2/D)<=2/D proves that finite constant.

For an ARBITRARY rank-k projection P and an arbitrary Schmidt witness W,
diagonal entries of P in an eigenbasis of W lie in [0,1]. Consequently
Tr(PW) is at least the sum of all negative eigenvalues of W. That sum is

    -[(sum_i s_i)^2-1]/2 >= -(m-1)/2

by Cauchy–Schwarz. As t=2/(m-1), Tr[(I+tP)W]>=0 for every vector witness.
Every global-unitary image of P is still a projection, so this is genuine
all-global-unitary APPT sufficiency. It works for EVERY integer rank,
including k<R or D-k<K. The special full-slot rank restrictions of other
one-head boundary families are not needed for this projection family.

Choose k=max(1,floor(D/alpha)). For D>=4 and alpha>=2 it lies in [1,D-1].
If D/alpha>=2, floor(D/alpha)>=D/(2alpha); otherwise k>=1 and D<2alpha.
Hence theta>=1/(2alpha). The upper bound theta<=1/alpha+1/D also holds
when alpha>D, where k remains one, not a fractional rank.

The exact trace is D+t*k. The power expression is at least theta*q^alpha,
and alpha/a*log(1+t*theta)<=2*t*theta<=4/alpha+4/D. Together with
log(theta)>=-log(2alpha), this proves the bulk branch of (9). Combining
the two actual matrices and using the common L proves the finite lower
bound for all dimensions and real orders in P0. No numerical optimization
or presumed outer-polytope sufficiency appears in either direction.

## Uniform rate and the two distinct zero-ratio regimes

For fixed D, m<=sqrt(D) gives m/(D-m)<=1/(sqrt(D)-1). Also
a>=alpha/2 for alpha>=2. These inequalities convert BOTH explicit errors
to O(D^-1/2+log(alpha)/alpha) with one absolute constant. They establish
the simultaneous uniform formula directly, without a fixed-m/growing-m
subsequence split, a bound on alpha/logD, or an assumption on m/n.

When m->infinity and alpha/logD->c in (0,infinity], alpha automatically
tends to infinity. The leading expression tends to max(0,log3-1/c),
with 1/infinity=0. The transition is c=1/log3; at equality this is only
an absolute zero limit, not a sharp relative next-scale law.

When m is FIXED, the corrected theorem explicitly requires D=mn->infinity
AND alpha->infinity, also when c=infinity. Its bulk term log q persists;
the limit is max(log q,log3-1/c), interpreting the second term as
-infinity when c=0. For m=2 the bulk term is already log3. For m>=3,
solving equality gives c=1/log[3(m-1)/(m+1)], with positive denominator.
The alpha->infinity hypothesis must remain in this fixed-m c=0 branch.

For m->infinity and alpha/logD->0, by contrast, alpha may be ANY positive
sequence, even bounded, tiny or oscillating. Put beta=alpha+sqrt(logD).
Then beta->infinity, beta/logD->0, and the already proved growing-order
formula gives E_beta->0. For each fixed dimension, deficit is increasing
in positive order for every state, hence its maximum over the same APPT
set is increasing too. Therefore 0<=E_alpha<=E_beta->0. This is a valid
extension in this particular c=0 regime, not use of P0 below order two.

## Genuine original finding and retained versions

The original fixed-m c=infinity sentence omitted D->infinity. Literally
it allowed m=n=2 with alpha->infinity. The maximally entangled witness has
one negative and three equal positive eigenvalues; assigning lambda_1 to
the negative slot gives lambda_1<=1/2. The actual D=4 spike has lambda_1=1/2.
Rényi deficit is bounded above by min-entropy deficit log(4*lambda_1),
and the spike tends to that value. Thus the ACTUAL maximal deficit tends
to log2, contradicting the originally stated log3 limit. This is a true
range error, not a mere wording preference.

The author corrected the source and map, disclosed the counterexample and
preserved all original bytes. Its original finite PASS did not detect the
range error and is not treated as certifying that false P2 statement. The
final P2 has the corrected D-growth range. Later author cutoff optimization
is a separate mathematical strengthening of P0/P1, fully disclosed rather
than described as an unchanged target. All three source/map versions,
histories and controls remain in the snapshots and author-version copies.

## Actual finite evidence and review limits

The reviewer wrote new rational/scalar code, without importing, executing
or AST-selecting author helpers. The final run 20261015T091753.210538Z
reports PASS for 65 exact decreasing-row graph tests, 1,488 exact integer-
rank uniform-Schmidt tests, 96 dimension/order cases and 576 actual
family/convex-mixture/singular-state comparisons. These include 25 cases
with alpha>D and 144 m=2 zero-head checks. Six incorrect assertions raised
actual retained AssertionError records, including the original fixed-D
claim, missing normalization, missing fixed-m branch, fractional rank,
bounded-order fixed-m c=0 extension, and unsorted row graph inequality.

The previous run 091232.667475Z passed the same finite controls for the
corrected v2 weaker upper bound. The only independent mathematical-checker
change for the final run is the new U formula. Neither independent run had
an unexpected checker FAIL; the original source-range error remains a
separate mathematical finding. A snapshot-helper setup assertion also
failed initially because two identical SHARP files exist; its actual trace
and source remain. CONTROL_HISTORY.md distinguishes all of these events.

The author runs 090459.816232Z, 090615.061888Z and 091342.637637Z each report
104 finite cases and PASS. The final 93-line script was read in full;
all three results were parsed, their summaries inspected and their exact
source hashes checked. They were copied but NEVER executed by this
reviewer. The first run's missing quantifier countercase is disclosed.

No finite diagnostic verifies every state, order, Schmidt vector or global
unitary, and none is offered as a global numerical maximization certificate.
The analytic physical tests, explicit inequalities and independent actual
constructions carry those quantifiers. This PASS does not certify exact
finite entropy/equality spectra, sharp next terms, relative accuracy at a
vanishing leading value, fixed-order small-deficit asymptotics, absolute
separability, new Lean, external human review or an extra major-conjecture
count. Author bounded primary-abstract screens are contextual claims;
this review did not independently perform a new exhaustive literature or
priority investigation. Publication/status changes require a separate
final source binding.
