# Independent review of the three transport candidates

Review date: 8 October 2026. Scope: a single analytic review of the three complete candidates, with the originals left unchanged. No formal verification, publication, historical-priority certification, or upstream proof audit of (P) is claimed.

## Main conclusion

The main top-N theorem is accepted **conditional on the explicitly imported potential theorem (P)**. The binary mass theorem and the general binary moment envelope are accepted as written mathematical arguments, with the halfspace geometry independently checked in this review. No counterexample to any of their stated quantitative formulas was found.

There is one genuine local inference gap in the third candidate's endpoint section: mere two-sided comparison of Phi with a model growth function does not imply the differentiability and logarithmic-derivative limits required in its Section 6. In particular, the sentence in Section 7.1 asserting that the Section 6 index is zero is false under the hypotheses as stated. Section 7.2 also invokes Section 6 without providing its regularity hypotheses. Both endpoint conclusions remain valid under the stated hypotheses. Sections 5 and 6 of this review give a counterexample to the invalid inference and complete replacement proofs that require no added assumption.

Thus the correct batch status is **accepted main results, one local proof repair required**, rather than an unqualified pass of every line in the original files. The originals have not been edited.

## 1. Reviewed snapshots and dependencies

1. `research_math/source_complexity_envelope_20261008/PROOF.md`
   - 459 lines.
   - SHA-256: `c3cf5061de5ac9298f3fb88e07800c9d88257b01a1cd80f82fdc5e1a083055c1`.
2. `research_math/binary_mass_phase_20261008/PROOF.md`
   - 451 lines.
   - SHA-256: `6858879d5acb26657b7d83ffc1b99386e67cd5c9fbf60ab451b579d132f1b9d8`.
3. `research_math/binary_source_moment_envelope_20261008/PROOF.md`
   - 260 lines.
   - SHA-256: `2eaedf293a1661678f5cde712fd18b094c6e20d5e1c4dea7ea098de44feb8fc6`.

The README files were inspected for scope consistency. Their numerical/exact-check reports were not treated as proofs.

The prior critical-atom result was inspected only as background and for the stated dependency boundary; its pass was not inherited by the new results:

- `research_math/critical_atom_budget_20261008/PROOF.md`, SHA-256 `88d9971c062414b1637806b0b61248585f1132c6082783df227266fe7122996e`.
- `research_math/critical_atom_budget_20261008/PARENT_INDEPENDENT_REVIEW.md`, SHA-256 `f0a135768a3efd6d86772dd689636f7fa264fda8168b1239b99538dd5e959d1c`.

For the legal range of (P), I inspected the actual theorem statement in the local entry-001 v3 source:

- `research_math/dimension_refinements_publication_20261007/stage/preprints/001-strongly-log-concave-brenier/v3/manuscript.tex`, SHA-256 `c5a49355eb805e9cd41f97428827e633cd19577ee34fd5f0f02bb5550b1c15fe`.
- Theorem 1.1 permits densities exp(-kappa |x|^2/2-W)/Z with proper lower-semicontinuous convex extended-valued W, full-dimensional support, and arbitrary finite-second-moment targets. Hard boundaries and nonsmooth extended W are explicitly permitted.
- This review verifies application of that statement, not its proof or identity with an independently downloaded remote revision.

## 2. Result-by-result decisions

- **SC1 — source construction and slow-variation preliminaries: PASS.** The fixed source meets the advertised extended-support strong log-concavity hypotheses.
- **SC2 — quantile majorant and finite-step top-N compression: PASS.** The interval-selection argument controls arbitrary partitions and oscillatory L without a monotonicity substitution.
- **SC3 — uniform dyadic inversion: PASS.** The same distance threshold and adjacent-ratio constants work for every N.
- **SC4 — arbitrary selected-scale lower construction: PASS.** Global convexity, both cumulative mass matches, selected-only moment accounting, and the 2M+1 atom count are valid.
- **SC5 — Theorem A, logarithmic corollary, fixed-N criterion, oscillatory example: CONDITIONAL PASS ON (P).** Lower bounds are unconditional within the stated source class. N=1 and N=2 qualifications are correct.
- **BM1 — all-orientations weighted trace and fixed-mass halfspace motion: PASS.** This is a valid independent geometric input.
- **BM2 — arbitrary binary support locations, weights, centering, and obtuse relabeling: PASS.** There is no hidden common-support or support-separation assumption.
- **BM3 — fixed-mass, minimum-weight, and unrestricted sharp envelopes: PASS.** The lower examples are actual Brenier maps with exactly the required masses.
- **BM4 — alpha=2s phase boundary and slow/logarithmic corrections: PASS.** They follow from the proved binary envelope and the actual quantile inversion.
- **GM1 — general Phi envelope and exact continuity criterion: PASS.** No doubling, regular variation, or differentiability of Phi is needed for these results.
- **GM2 — Section 6 index principle under its explicitly stated extra derivative hypotheses: PASS.** The endpoint kappa=0 and kappa=1/2 cases are included correctly.
- **GM3 — Sections 7.1 and 7.2 under merely comparable Phi: LOCAL PROOF GAP AS WRITTEN; PASS WITH THE REPLACEMENT PROOFS BELOW.** The conclusions and parameter ranges need not change.
- **GM4 — bounded-support-radius variant: PASS.** The upper gap bound and the lower hinge examples apply directly with E(m)=sqrt(m).

Only GM3 depends on the identified repair. It does not invalidate the halfspace lemma, either main binary theorem, the continuity criterion, the bounded-radius result, or the top-N theorem. Conversely, SC5 must retain its (P) dependency even though the binary results do not use it.

## 3. Detailed checks of the top-N candidate

### 3.1 Source and the range of (P)

Write V_1=-log f up to its normalization constant. Near zero,

    V_1'' = 1 + beta/x^2 - (log L)'' >= 1 + beta/(2x^2),

after fixing a sufficiently short initial interval. Continuously extending this second derivative above one and eventually setting it equal to one gives the claimed C^2 interior potential and quadratic-plus-linear tail. Since beta>0 and log L=o(log(1/x)), V_1 tends to infinity at zero. Extending its convex domain by +infinity is lower-semicontinuous.

For the transverse potential V_g(z)=1/(1-z^2),

    V_g''(z)=2(1+3z^2)/(1-z^2)^3 >= 2.

Consequently V-|x|^2/2 extends to a proper lower-semicontinuous convex function on R^d; the support interior (0,infinity) x (-1,1)^(d-1) is nonempty. All targets in the moment classes have finite second moment. The displayed application of (P) with kappa=1 is within the inspected theorem statement. Full-support smoothness is not needed.

The first derivative condition on log L supplies all fixed-ratio comparisons and the inverse-CDF estimates. The second derivative condition is used to ensure the source's convexity, not to smuggle in monotonicity of L.

### 3.2 Quantile rearrangement and the finite-step bound

The overlap deficits include lost density outside the source support. Near X=0 the bound min(1,Ch/X) is valid after treating X<=2h by the trivial bound. The Gaussian tail and compact transverse bump produce tails smaller than the polynomial-scale tail F(1/t). This proves the rearrangement majorant C min(1,h/q(u)); the fixed continuation q(u)=a at larger u merely changes constants.

For an arbitrary at-most-N-valued nonnegative b, its decreasing rearrangement has at most N interval cells. Discrete Holder gives the stated partition functional. Splitting a cell at F(h) increases that functional, so the capped lower-probability region is safely separated, at cost at most F(h) comparable to h^s L(h).

On a remaining cell (v,u), let z=log(u/v). The inverse-CDF estimate with exponent r<1 gives

    integral_v^u 1/q(t) dt <= C u/q(u) min(1,z).

After dividing by the cell length to the power s-1, its contribution is bounded by C h^s M(u) min(1,z). The chosen logarithmic intervals are disjoint and have length at most one. Their number is at most N+1. Each meets a fixed number of dyadic source shells because d log q/d log u is uniformly bounded on the small-probability range. Thus only O(N) source shells are paid for, and grouping sorted weights into blocks of N proves the top-N estimate.

This argument does not assume that a maximizing step function is a realizable transport map. Realizability is supplied separately by the lower construction.

### 3.3 Dyadic inversion and simultaneous constants

Adding one new dyadic value changes A_N by at most a_(K+1)<=2^eta a_K, while A_N(K)>=a_K. Therefore

    1 <= A_N(K+1)/A_N(K) <= 1+2^eta.

This gives the advertised adjacent ratio of W_(N,K), with a strictly subunit upper bound independent of N and K. Also W_(N,1) is independent of N. The choice K=min{K:W_(N,K)<=w} therefore satisfies

    W_(N,K) <= w < W_(N,K-1) <= 2^(3/2) W_(N,K).

There is no hidden N-dependent small-w condition. The optional claim that the map-scale sequence decreases follows from eta<s-1 and

    1+2^eta < 2^(1+eta) < 2^s.

### 3.4 Finite differences and the transport upper bound

The minimum-weight finite-difference inequality was checked directly. Convexity bounds the forward difference quotient between the two directional derivatives. For a<=b,

    (b-a)^2 <= 2(b|b|-a|a|).

After shifting the signed-square integral, the weight is m_h(x-he_j)-m_h(x)=r(x)(d_+-d_-). Both minimum weights are bounded by r(x), so all gradient-square terms are integrable. The difference quotient of u-v-b contributes at most 4h^-2 ||u-v-b||_2^2 before the three-term square bound. The missing weight contributes 2d_+, and the directional-error terms contribute 6|d_+-d_-|. Summing directions gives 12d delta^2/h^2 and the displayed F_h-weighted energy.

For finite atomic targets, |T|^2 has at most N values and its L^(p/2) norm is at most one. Applying the compression estimate and then (P) gives exactly

    ||T_mu-T_nu||_2^2 <= C(w^2/t_K^2+t_K A_N(K)^(1/s)).

The chosen dyadic inverse balances these terms up to uniform constants.

### 3.5 Sparse selected-scale construction

All windows lie in relative neighborhoods of their selected cusp and remain disjoint for one fixed epsilon. The inverse-convolution definitions give exact cumulative matches at both ends. Symmetry removes the first-order intercept error, and the derivative bound controls the remaining O(h^2/t_j) displacement. The positive E|Z| term supplies the uniform symmetric-difference lower bound.

For either broken line, the supporting midpoint-slope line has difference at least R_j times distance to its cusp, with equality between neighboring selected cusps. On the source's transverse support the raised plane is active precisely in its stated window. Global maxima are finite convex functions even where their activity outside the source is different; only source activity is used.

The outer slopes agree between U and V. Every outer label mass is a difference of two cumulative endpoint probabilities, so preserving only central masses would not suffice, but the two exact matches provided in the paper do preserve every label, including across skipped scales. The overlapping windows rule out a direct transition from one outer slope to the other. This proves the exact horizontal discrepancy and the same-label target coupling bound.

For the moment bound, each horizontal slope is controlled by the sum of selected R_j for which X<=2t_j. These R_j grow geometrically with their selected index, even across gaps. Hence for every contributing subset,

    (sum R_j)^p <= C sum R_j^p.

Integration charges only R_j^p F(2t_j), comparable to L(t_j) because beta p/2=s. No unselected shell is charged. Scaling by S_J^-1/p gives the claimed response S_J^(1/(2s)).

There are M+1 outer and M central positive-mass distinct labels. With n=floor((N-1)/2), the choice M<=n respects 2M+1<=N, and sorted-weight averaging gives A_n(K)>=A_N(K)/4 for N>=3. Taking h=epsilon t_K respects every selected cusp, whether or not K is selected. This closes the genuine transport lower bound.

### 3.6 Consequences

The logarithmic sums have the stated orders, including gamma=-1 and gamma<-1. Their logarithms are O(log(e+K)) uniformly in N, giving K comparable to log(e/w). For fixed N, A_N(K) increases to its supremum, so the liminf/limsup assertions and the bounded-L criterion follow without asserting an exact leading coefficient.

The oscillatory example satisfies both derivative assumptions. Its earlier peak and later valley are both captured by dyadic samples with asymptotically negligible relative change; the exponential divergence of the top-N/endpoint ratio is valid. The separate N=2 logarithmic lower construction has equal exact masses and genuine hinge potentials. Its qualification gamma>=0 in this candidate is appropriate; the more complete negative-gamma binary answer comes from the next candidate.

## 4. Detailed checks of the binary and general-moment results

### 4.1 Halfspaces in every direction

For alpha>1 the zero-extended density is continuous and W^(1,1), and |x|r is W^(1,1). The boundary derivative in the first coordinate has size at most C x^(alpha-2)L(x), which is integrable. No omitted boundary measure appears. The fast transverse decay and quadratic far tail handle the other boundaries and infinity.

The weighted score satisfies

    A <= C[1+X^2+X^-1+(1+X) sum D_j],
    D_j=(1-|Z_j|)^-2.

The stretched-exponential tails of the other terms are absorbed by F(1/t). Thus A^*(u)<=C/q(u). Integrating the inverse-CDF comparison with any exponent strictly between 1/alpha and 1 gives integral_0^m A^*<=C m/q(m). The restriction alpha>1 is essential to this particular argument and is correctly retained.

For H={u.x>c}, the vector field u|x|r has outward flux -|x|r across the finite boundary. The divergence identity gives

    integral_boundaryH |x|r = -integral_H u.grad(|x|r)
                           <= integral_H (r+|x||grad r|).

The sign is correct. Sobolev slicing initially gives the identity for almost every threshold; continuous hyperplane integrals under the Gaussian envelope extend it to every threshold. It does not require the origin to be the source barycenter.

For fixed m in (0,1), every projected quantile lies in the interior of the projected support and has strictly positive projected density. Locally expressing the boundary as a graph proves C^1 dependence of halfspace mass on the normal and threshold using only continuity and the Gaussian envelope. The implicit-function theorem therefore gives the mass-preserving threshold. Along a fixed compact normal path the thresholds remain bounded: a source |X|-tail quantile bounds all directional quantiles. There is no loss of continuation at vertical directions or tail directions.

The derivative of the threshold is the boundary average of u'.x. Consequently the integral of the absolute normal velocity is bounded by twice |u'| times the weighted trace. Integration along any shortest spherical arc, including an arbitrarily chosen great semicircle for antipodes, proves (H). The trivial 2m bound supplies saturation. This establishes the full orientation-uniform lemma rather than just the direction used for the lower example.

### 4.2 Coupling, mass changes, and near collisions

Subtracting barycenters splits both squared distances exactly. For centered binary laws the 2x2 coupling cost is affine in tau, whose feasible interval is [max(0,m+n-1),min(m,n)]. The acute optimum at tau=m (after ordering m<=n) gives

    W_c^2=m(1-n)|v-z|^2+(n-m)[m|v|^2+(1-n)|z|^2].

Direct expansion verifies every coefficient. Nesting of same-normal halfspaces isolates the mass difference n-m; the remaining disagreement has common mass m and is controlled by (H). For acute directions,

    angle(v,z)<=C |v-z|/max(|v|,|z|),

so the calculation never divides by a fixed positive support separation. Tiny and nearly colliding gaps are covered.

For obtuse gaps with m+n<=3/4, the optimum tau=0 and 2|v||z|<=|v|^2+|z|^2 imply

    W_c^2 >= (1-m-n)(m|v|^2+n|z|^2).

For m+n>3/4, both rare masses exceed 1/4. Reversing one target's labels gives an acute pair with distinguished mass n'=1-n and 1-n'>1/4. The same formula controls the mass mismatch and the new gap difference. Applying (H) only at the unreversed m<=1/2 is legitimate. The compact-mass O(w) squared-error term is absorbed by the scalar supremum, or by the fixed-mass expression when m>3/8. Dirac degeneracies are handled separately by exact equality of map and target distances.

### 4.3 Exact-mass realization and scalar maximization

For t=q(m), symmetry and uniform local control of f give an exactly mass-matched tilted halfspace with intercept t+O(b^2/t) and disagreement comparable to b m/t for b<=epsilon t. These estimates are uniform up to t=T by positivity and regularity on the compact remainder.

The two targets in the papers are gradients of their displayed global hinge potentials; both atom masses are exact. The rare atom has length m^-1/p, or R(m) in the Phi theorem, so the moment budget is exactly one. The same-label target coupling costs at most b E(m), while mismatch of the source cells contributes at least c b E(m)^2/t to squared map distance. Choosing b=epsilon min(t,w/E(m)) therefore realizes the entire scalar minimum, not an unrelated energy profile.

The additional w term comes from translating two sufficiently short atoms; all norms remain below one and the moment budget is preserved. Translation changes both distances by exactly w.

Since E is positive and nondecreasing, B(t)=tE(F(t)) is strictly increasing even if E has plateaus. Its inverse is well-defined, including a quadratic Phi with constant E. Below h_w the scalar minimum is J(t)^2 and is nondecreasing; above h_w it is wJ(t)/t. This proves the exact maximum identity for every eta, including eta=1/2. The maximizing mass produces actual admissible targets. No doubling of E, no unproved regular variation, and no continuity limit in eta are used.

### 4.4 General Phi assumptions and continuity necessity

The assumptions imply Phi is unbounded, so its inverse exists. For m<=1/2, R(m)>1 and Phi(R(m))>=R(m)^2, hence E(m)<=1. The identity

    E(m)=[Phi(R(m))/R(m)^2]^-1/2

proves continuity and monotonicity of E. Convexity of the radial moment function gives |bar_mu|<=1; the pointwise atom bounds give the gap estimate <=2R(m). It is unnecessary to assert that centering preserves the moment budget.

The nondecreasing ratio Phi(r)/r^2 has a limit in [1,infinity]. An infinite limit is exactly E(m)->0. The split of the scalar supremum at a fixed positive mass proves sufficiency for uniform continuity. If the ratio has a finite limit, E has a positive limiting value. Taking q(m)E(m)<=w in the exact hinge construction gives a positive map discrepancy independent of w. This proves necessity using actual two-atom Brenier maps.

For a fixed positive minimum mass, the compact scalar maximum gives a one-half small-w law. The unit-support-radius variant has gap bound two and the same lower hinges with R=1; it is independent of the Phi hypotheses.

The comparison with a three-atom one-third obstruction can also be checked directly on every source in this batch: select one fixed interior cusp, use the two-endpoint matched strip construction with fixed small jump R, and let its width h tend to zero. All slopes can be kept inside the unit ball; squared map discrepancy is comparable to h and the target coupling cost squared is O(h^3). Thus the binary/three-atom distinction does not require extending the critical source theorem to an unproved family.

## 5. Counterexample to the endpoint proof's implicit regularity claim

This is a counterexample to a proof step, not to the endpoint modulus formula.

Fix gamma>0. Let S be a smooth nondecreasing step with S(v)=0 for v<=0, S(v)=1 for v>=1, and S' positive somewhere in (0,1). Put a=gamma log 2. Choose a fixed D large enough that

    a ||S''||_infinity / D^2 <= 1.

Choose n_0 so that the intervals [2^n,2^n+D], n>=n_0, are disjoint and lie in (0,infinity). Define the locally finite smooth sum

    b(u)=a sum_(n>=n_0) S((u-2^n)/D),
    Phi(r)=r^2 exp(b(log r)) for r>0,  Phi(0)=0.

Near r=0 and up to the first transition, Phi(r)=r^2; in particular Phi(1)=1. Moreover b'>=0 and b''>=-1, because at most one step is in transition. Direct differentiation gives

    Phi'(r)=r exp(b)(2+b')>0,
    Phi''(r)=exp(b)[2+3b'+(b')^2+b'']>0.

Thus Phi is smooth, strictly increasing, convex, and Phi(r)/r^2 is nondecreasing. It satisfies all of (M).

For large u between successive dyadic thresholds, b(u)=gamma log u+O(1), including the fixed-width transition regions. Consequently

    Phi(r) is comparable to r^2 (log r)^gamma.

However r Phi'(r)/Phi(r)=2+b'(log r). This equals 2 throughout arbitrarily long gaps. At a fixed interior point of each transition it equals 2+c for one fixed c>0. It therefore has no limit. Inverse differentiation yields

    m E'(m)/E(m)=1/2-1/[2+b'(log R(m))],

which also has no limit: it is zero along one sequence and positive along another. Thus Section 7.1 cannot claim the Section 6 index kappa=0 from the stated comparison assumptions, even after adding smoothness and strict convexity of Phi.

The only change needed is a proof that works with comparison rather than derivative limits. The next section supplies it for both endpoint applications.

## 6. Complete replacement text for the endpoint arguments

The following text may replace the proof paragraphs of Sections 7.1 and 7.2 in the general-moment candidate. The statements and hypotheses can remain as written.

### Replacement for Section 7.1

Write a=gamma/2>0 and tau(t)=log(e/t). Two-sided comparison of Phi(r) with r^2[log(e+r)]^gamma, followed by inversion, gives

    E(m) comparable to [log(e/m)]^-a.

Since F(t) has a positive boundary index alpha, log(e/F(t))/log(e/t) tends to alpha. Therefore there are fixed positive constants such that

    J(t) comparable to tau(t)^-a

for all sufficiently small t. No differentiability or regular-variation property of Phi or E is needed for this conclusion.

Choose t_0>0 sufficiently small that k(t)=t^-1 tau(t)^-a is decreasing on (0,t_0]. This follows by differentiating the explicit comparison function:

    d log k(t)/d log t = -1+a/tau(t)<0.

For h<=t_0, comparison with k and the finite maximum on [t_0,T] show

    H(h) comparable to h^-1 tau(h)^-a
         comparable to J(h)/h.

The compact-range contribution is absorbed because k(h) tends to infinity as h tends to zero. With the exact defining identity w=h_w J(h_w), the main envelope now gives

    Omega_(Phi,2)(w) comparable to J(h_w).

Also w is comparable to h_w tau(h_w)^-a. Taking logarithms yields

    log(e/w)=log(e/h_w)+a log log(e/h_w)+O(1),

so log(e/h_w)/log(e/w) tends to one. Consequently

    Omega_(Phi,2)(w) comparable to [log(e/w)]^(-gamma/2).

This proves (7.1) under the original comparison hypotheses.

### Replacement for Section 7.2

To avoid confusing the exponent with the source quantile function, denote the stretched-exponential exponent by theta>0 in this proof. Comparison of Phi(r) with exp(r^theta) gives

    R(m) comparable to [log(e/m)]^(1/theta),
    E(m) comparable to sqrt(m)[log(e/m)]^(1/theta).

If the source factor is [log(e/t)]^gamma, set

    A=alpha/2,   b=gamma/2+1/theta,   tau(t)=log(e/t).

The source CDF estimate implies

    J(t) comparable to t^A tau(t)^b.

We apply the main envelope directly to these comparison functions, rather than invoking the extra derivative hypotheses of Section 6.

If A<1, the explicit function t^(A-1)tau(t)^b is eventually decreasing as t increases and tends to infinity at zero. Therefore

    H(h) comparable to h^(A-1)tau(h)^b
         comparable to J(h)/h,

and Omega(w) is comparable to J(h_w). The exact equation w=h_w J(h_w), together with the displayed comparisons, gives

    h_w comparable to w^(1/(A+1)) [log(e/w)]^(-b/(A+1)).

For completeness, taking logarithms first gives tau(h_w) comparable to log(e/w); substituting this into w comparable to h_w^(A+1)tau(h_w)^b gives the claimed two-sided inverse estimate. It follows that

    Omega(w) comparable to w^(A/(A+1))
                             [log(e/w)]^(b/(A+1)).

If A>1, J(t)/t tends to zero and is bounded on (0,T], with a positive value somewhere. Its running maximum is therefore bounded above and below by positive constants for small h, giving Omega(w) comparable to sqrt(w).

If A=1, comparison with tau(t)^b and the positive compact-range contribution gives

    H(h) comparable to tau(h)^(max(b,0)).

The equation w=h_w J(h_w) is comparable to h_w^2 tau(h_w)^b, hence tau(h_w) is comparable to log(e/w). Therefore

    Omega(w) comparable to sqrt(w)[log(e/w)]^(max(b,0)/2).

Substituting A=alpha/2 and b=gamma/2+1/theta, and then writing theta as q to match the statement, yields exactly (7.2). All estimates are for the originally stated comparison class of Phi, without an additional C^1 or logarithmic-derivative assumption.

## 7. Small clarifications that do not affect the verdicts

1. In the general-moment candidate, R is initially defined on (0,1/2], but the gap estimate writes R(1-m). Define R(u)=Phi^-1(1/u) on all 0<u<=1, while keeping E restricted as before, or write the inverse explicitly in that one estimate. This is a notation-domain repair only.
2. The general-moment candidate explicitly fixes the source from the preceding candidate. Preserve that wording. Reading its displayed f(t)~c t^(alpha-1)L(t) as a license to replace the source by an arbitrary merely comparable density would not supply the derivative and convexity assumptions used later.
3. In the top-N construction, the precise central-cell activity assertions for V are assertions on the source's transverse support. The global convex maximum is well-defined outside that support, but its active-cell geometry there is irrelevant and need not equal the displayed window description.
4. Retain the conventions that all comparison constants may depend on the fixed source and moment function, that support counts distinct positive-mass atoms, that d>=2 and alpha>1 are fixed, and that the theorems are small-w statements. None asserts a leading-coefficient limit.

## 8. Stopping point

The review is complete for the specified three-file batch. There is no unresolved mathematical blocker to the principal quantitative results within their stated hypotheses. Before treating the original third manuscript as fully proof-complete, replace its two endpoint proof paragraphs with comparison-based arguments such as Section 6 above and clarify the harmless R-domain notation. The top-N theorem must continue to display its imported (P) dependency. No new claims about historical priority, arbitrary sources, N>=3 minimum-weight classes, or formal verification follow from this review.
