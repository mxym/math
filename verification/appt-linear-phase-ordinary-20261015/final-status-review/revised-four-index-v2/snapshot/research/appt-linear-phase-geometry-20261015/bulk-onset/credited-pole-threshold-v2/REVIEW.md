# Independent ordinary mathematical review of scalar phase geometry, v2

**Decision: PASS for the complete v2 target**, PAPER SHA-256 `83c2240adfbca39009ff446504cc477f47684a0e5de1db52439862053bbcad79`, 437 lines. This includes all-c threshold T2, small-c T4, the original every-real-c≥10 T5, and the stated quantum/spectral transfers. A proposed stronger c≥1 replacement is **pending a separate exact-source read** and is not covered by this decision. This is a private internal independent AI-agent ordinary review, not external human peer review, Lean verification, a priority certificate or a new major-problem count.

## Sources and actual reading

The initial v1 PAPER, 434 lines/18203 bytes, was privately captured as b270516f… and read completely. The omitted alpha>1 restriction in its moment/entropy identity was reported before any PASS. The author retained v1 and the finding and produced v2. The entire exact V1_TO_V2.diff was read and independently regenerated from the original bytes. It changes only that definition domain and the explicit positive derivative substantiating the Hessian argument. The complete manuscript was covered by the original full read and this exact verified delta.

The full new map, PRIMARY_SCOPE, credited-input manifest, author checker and diagnostic script were read. The actual author FAIL and subsequent PASS, their bound scripts, relevant result fields, precision diagnosis and exact checker difference were read; neither author program was executed or imported. INPUT_V1.json and INPUT_V2.json retain the actual snapshots, hashes and read chronology.

The eight author-credited files were verified against immutable main c4e0d9e713ba349d376469231789bb7b36915b7d. This same agent had already read the complete L manuscript343lines, V manuscript267lines and their ordinary review records in earlier source-bound tasks. Their exact mathematical bytes are reused, not claimed as fresh new theorems. The published S manuscript6ae480fc… is the status-only successor of the complete e9ba9730… mathematical source that this agent independently read in full; its literal mathematical report and final de8d72… byte binding were captured. The relevant physical losses, full argmax and attainment scope were rechecked in applying S. Earlier L/V/S dispositions do not automatically establish the new scalar conclusions.

## Finding and correction

F1: v1 stated E_alpha=log(max M_alpha)/(alpha−1) without restricting alpha>1. For 0<alpha<1, concavity makes the maximum normalized moment equal to one at the maximally mixed state. A nonuniform actual APPT pole has positive entropy deficit, so the displayed equality would incorrectly give zero. This is a real definition-domain error even though all fixed-positive-linear-order quantum paths eventually have alpha>1.

For an explicit 3-by-3 pole at alpha=1/2, the normalized moment is (sqrt3+8)/(3sqrt11)<1; squaring reduces the strict comparison to sqrt3<2. The corrected v2 first restricts real alpha>1 before defining the maximum-moment identity. All intended linear-order quantum conclusions retain their original hypotheses. V1 is not retrospectively labeled PASS. The additional explicit derivatives a'(L)>0 and dh/da>0 also make clear why the envelope's second derivative is strictly negative; strict monotonicity alone would not be a general proof of a nonzero derivative.

## Threshold and one-sided derivatives for every c>0

For L>0, A=Lh+G(L)>0 and P<1. Jensen gives B≥1, with h=0 or1 giving B=1. The proof of the boundary extension is substantive: the global Taylor remainder gives e^(−2c)c²B2≤B−1≤e^(2c)c²B2, while x/(1+x)≤1−e^(−x)≤x holds for all x≥0. These imply

    e^(−2c)f <= Q/c <= e^(2c)(f+cB2).

At L=0, f≤L/2 and B2≤L²/8 force Q→0 uniformly for c in any positive compact interval. At L=2 the finite Q equals B−1 and the protected peak vanishes uniformly in h; the same displayed bounds remain valid with f=0. The corner behavior is included. Thus Q is jointly continuous on the compact parameter rectangle, and its positive finite maximum is attained and continuous in c. The width-two pure-bulk competitor ensures positivity.

The exact identity F−(1+r)=(1−P)(Q−r) completely determines the pole threshold. Above the maximum Q, every positive width is strictly inferior; below it some positive width beats the pole; at equality, and only there, the positive-width ties are precisely argmax Q. The h-endpoints have Q=0 and are excluded from any positive-width threshold maximizer. All ties and the zero-width redundant h interval are retained.

For fixed c, parameters of optimizers approaching the threshold from below satisfy Q≥r and ultimately Q≥rcrit/2. Compactness and the fact that Q vanishes on L=0 and h=0,1 keep them away from those faces. Their body variances are bounded below, whereas the pole law has zero variance. This proves the stated body jump without asserting uniqueness of the positive width.

F_* is a compact maximum of affine functions of r. At the threshold its active slopes are P on argmax Q and1 on the zero-width face. The elementary maximum-envelope difference-quotient argument gives the **least** active slope on the left and greatest on the right. The minimum is attained and strictly less than1 because argmax Q is compact and disjoint from L=0. Hence T8 and its strict kink follow; the logarithmic slopes divide by the common positive1+rcrit.

## Global small-c localization, Hessian, IFT and K1

The same global bounds give uniform absolute convergence Q/c→f with O(c) error over the whole closed rectangle, since f≤1 and B2≤1/2. This is not a relative equivalent to f at moving points where f vanishes, and it does not depend on keeping L away from2 before taking the supremum.

For each interior width the unique h maximizing f satisfies a=h²/(1−2h), with a=2L/[3(2−L)]. The optimized value becomes v(h) as printed. Its derivative has the sign of the negative cubic q(h). On [0,1/2], q'>0; its endpoint sign at1/3 and3/8 isolates exactly one critical point. Boundary values of f are zero and its interior maximum is positive, so this is the unique global maximum. At the stationary point f_hh<0. The explicit positive derivatives of a(L) and h(a) show that the optimized envelope has second derivative v''(h0)[h'(L0)]²<0. Its negative Schur complement together with f_hh<0 makes the full Hessian negative definite.

Uniform global convergence localizes **every** Q/c maximizer in any chosen small neighborhood of that unique limit point. Near it the numerator/c² and denominator/c extend analytically through c=0, with limiting denominator A>0. The analytic implicit function theorem yields one critical point in an IFT neighborhood, with negative definite Hessian. Choose the localization neighborhood inside that IFT neighborhood. Every global maximum is then interior and critical there, so this one point is the unique global maximum for all sufficiently small positive c. This justifies the global claim; local IFT alone would not have sufficed.

The cubic moment coefficient is B3=L³h(1−h)(1−2h)/6. Expanding the vanishing denominator as well as the numerator gives

    Q/c=f+c(B3/A+B2/2)+O(c²).

The stationary first derivative of f kills the first-order contribution from the moving maximizing parameters. Therefore K1=B3/A+B2/2 at the limiting maximizer, equal to K0[L0(1−2h0)/3+A0/2]. The B2/2 term is indispensable. At fixed sufficiently small c the Hessian of F at coexistence equals (1−P)Hess Q. It is negative definite; IFT in r and compactness, together with Q≥r keeping approaching maximizers away from zero width, give the unique analytic positive-width global branch just below the threshold.

The pure-bulk excess is c²/2+O(c³), whereas rcrit=K0c+O(c²) with K0>0. Thus the claimed interval above pure-bulk excess and below rcrit is genuinely nonempty for all sufficiently small c. On it the optimum is strictly above both separate branches. No effective epsilon or uniqueness throughout intermediate c is inferred.

## The original entire c≥10 regime

I checked the proof for arbitrary real c≥10 and all widths/mixing parameters, including each boundary. For 0<L≤1 the Taylor and denominator bounds yield Q≤c(1+c)e^c/2. The trial h=1/(2c) gives b(2c)≥e^(2c)/(2ec). The strict comparison follows from e^c>4c²(1+c), obtained at c=10 from e²>7 and propagated by a positive logarithmic derivative; e<3 and2ec e^(−c)<1 complete the displayed algebra. These are continuous-range inequalities, not finite numerical tests.

For1≤L<2, K=cL≥10. The exact derivative of log b is correct. Its subtracted term K e^K/(e^K−1)² strictly decreases for K≥1. The rational estimate e³>20 gives3e³/(e³−1)²<60/361<1/6; consequently (log b)'(K)>1/2 on K≥3. Integration supplies the exponential width gap.

With delta=2−L in(0,1], all steps of T26 have the correct directions. In particular G≥2/(3delta); e^(−x)<1/x is strict;3(c+2)≤2c² holds for c≥3; and delta≤1 permits the denominator comparison before applying x/(1+x)≤1−e^(−x). Thus P is strictly below1−b(cL)/b(2c). At r0=b(2c)−1 this forces every interior width strictly below b(2c). The small-width bound supplies the remaining positive widths. At L=2 the pure-bulk optimum is unique, and at L=0 every h has the pole value.

This proves rcrit=r0 and the complete coexistence set. Affine interpolation between r=0 and r=r0 establishes the entire interval below the threshold, with equality forcing the unique pure-bulk optimizer when r<r0. Above the threshold the general T2 applies. The endpoint h=0,1 cannot conceal another optimizer: at every L>0 they have value at most1+r, strictly below that value when r>0. All exact argmax alternatives are therefore covered. This review decision on that proof is specifically c≥10; it is not automatic coverage of the proposed c≥1 replacement.

## Transfer back to actual matrices and spectral losses

For any fixed C≥10, T1 has exactly the uniform n/order range needed for T28. Substitution of the proved scalar formula gives the relative moment equivalent on10m≤alpha≤Cm for every n≥m. Its relative moment error gives uniform additive logarithmic error; b(20)>1 separates the reference logarithm from zero, justifying the relative entropy statement. C remains fixed; no uncalibrated3^alpha moment substitution is extended to unbounded alpha/m or alpha comparable to D.

For fixed c>0 and finite r, the source-bound S theorem applies to every actual APPT sequence with the exact middle cardinality, actual L=(m−1)kappa, full scalar argmax and both nonnegative J/PeakLoss conditions. The newly identified scalar sets may be inserted into that complete criterion. A bulk empirical law alone is not promoted to a sufficient condition when r>0. For example the actual maximally mixed state has exactly delta0 bulk law and J=0 but nonvanishing PeakLoss on a positive-r pole window; it has zero deficit and is not near-optimal.

S supplies the full Wasserstein laws and their actual integer-rank attainability, including all threshold ties and alternating sequences. Compact threshold parameters have positive variance, so the nonzero laws stay distinct from delta0. At small-c coexistence the interior peak formula gives m(3−y1)→3A(Lc,hc), while the zero-width branch gives zero. The operator-flat nonlargest tail conclusions retain r>0 and interior width. On L=2 the protected head moment vanishes and the interior expansion is singular, so it is expressly not asserted. Statements involving c→0 after these fixed-c results are iterated limits, not a new simultaneous c_m→0 quantum theorem.

## Actual controls, failures and limits

My newly written independent program imports no author code. One actual run, runs/20261015T112602.266319Z, PASSED: seven symbolic identities,160 exact rational cubic-root bisections,294 global/moving-endpoint cases including c=10^(−100), three small-c stationary/K1 diagnostics, and1120 large-c parameter/r samples. It uses a positive exponential-remainder series and analytic Q derivatives, rather than the author's raw bulk-minus-one implementation. Runtime: Python3.10.12, mpmath1.2.1 at400 digits, SymPy1.9. Script f7e6f0c75020e389c5e018ff01b97694aba076c3257dfd4fe2c8f0472e095e7f; result203c47bb248b32c47a4933d524819132766fc395cd05f4dfc204852885071326.

Eight incorrect variants actually raised saved AssertionErrors: the subunit max-moment identity, a global relative small-c limit in place of the proved absolute one, missing K1 denominator correction, greatest instead of least left active slope, independently adding optimized bulk and peak, replacing physical losses by bulk law at r>0, deleting exact pole trace normalization, and extending fixed-C quantum moment transfer to unbounded alpha/m. These finite controls do not certify an arbitrary global maximizer or the unbounded quantifiers. No unexpected independent checker failure occurred.

The author first ran111610.260147Z and obtained an actual FAIL when100-digit arithmetic rounded pole-normalization losses to zero and a strict finite-family decrease assertion failed. The source mathematics was not changed. A separate author diagnosis retains the100/1100-digit observations, and the later111650.131751Z PASS changes only the finite-family diagnostic precision to1100 digits. I read and compared those actual scripts and records without executing them. Neither author run is relabeled independent; the FAIL remains retained and is not called an initial PASS.

The official abstract/version pages of Tran2609.18568v1 and Ahiable–Kothakonda–Winter2608.03390v2 were freshly opened. Three arXiv-restricted queries were independently executed; their pooled output contained those or other primary metadata hits, not an empty result. The other hit papers were not read in full. This is a bounded screen, not priority certification. Mathematical dependencies are the explicitly captured local L/V/S proofs, not search snippets.

No source, public index, Git state or old Lean audit was modified. No author checker, Lean/Lake/kernel replay, publication/submission action, external message or subagent was executed. The unresolved intermediate phase geometry, optimal large-c boundary and unique-transition conjecture remain outside this v2 PASS. Final metadata/README/index binding and any stronger new mathematical source require their separate review.
