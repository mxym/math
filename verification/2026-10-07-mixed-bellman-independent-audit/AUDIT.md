# Independent adversarial audit of the mixed Bellman ceiling

**Audit date:** 7 October 2026.  
**Verdict:** The claimed upper theorem passes for the intended, dimension-preserving point-generated product/join class. No substantive mathematical or certificate gap was found. One class-definition clarification should be made before publication: “affine images” must mean **affine isomorphic images**, not arbitrary rank-dropping affine maps.

The audited result is

\[
\log Q(K)\le \frac{49}{1000}(d+1)
-\frac{87}{2000}\frac{H(K)^2}{d+1}
-\frac{11}{2000}\frac{H(K)^4}{(d+1)^3},
\]

and consequently

\[
2.8534<\Gamma_{\mathcal C}\le \exp(1049/1000)<2.855.
\]

This is a result for the restricted recursively generated class. It does not determine its optimum, improve the inherited lower construction, or establish an upper bound for all convex bodies. This audit is model-assisted mathematical review and exact arithmetic replay, not external human peer review or proof-assistant formalization.

## 1. Inputs and independence

The candidate is the byte-preserved `candidate_source/` snapshot of the received source. Its `MANIFEST.json` was verified both before and after the audit. Its own `combined_audit.md` and saved success reports were not used as evidence of mathematical validity.

The public comparison and inherited geometric/spectral dependencies were read from the **actual Git objects** at commit

`3360e7191cf564a46d09edcbfbd107c9178bd98f`.

The inspected repository’s working HEAD was `65a1baa1307ec91bc53a96087641cc575690f285`; the audit did not substitute that later checkout for the requested baseline. No checkout, pull, original-source edit, or push was performed. The working tree was clean when checked. `pinned_v2/` contains files extracted by read-only `git show`, so the evidence can be replayed without repository access.

The audit used three distinct layers:

1. Mathematical review of normalization, structural induction, continuous state coverage, analytic large dimensions, and spectral passage.
2. Fresh execution of the supplied checkers normally and under `python -O`.
3. A separately written standard-library verifier, `independent_replay.py`, that imports **none** of the candidate checker code. It uses a different logarithm term count and rounding denominator, forms factorials directly for factorial-log bounds, enumerates all four finite support corners, and maximizes both endpoint-gradient quadratics on the whole displacement interval in the tail.

The exact algebraic identities and constants also received symbolic recomputation in `normalization_symbolic_check.py`. Its 29 checks passed in both modes. SymPy is needed only for that supplemental symbolic script; the finite/tail replayer uses the standard library alone.

## 2. Scope wording that should be clarified

The first theorem paragraph in `candidate_source/proof.md` says “affine images of bodies obtained … by finitely many joins and Cartesian products.” The argument invokes affine invariance, which applies to affine isomorphisms on affine hulls. The inherited v2 class is dimension-graded and explicitly a class of affine shapes, which supplies the intended interpretation.

If “affine images” were interpreted as permitting arbitrary rank reduction, every polytope would already occur as an affine image of a sufficiently high-dimensional simplex. The structural induction in this submission does not cover that larger class. This audit therefore certifies the intended recursive class, not that literal broader reading.

A sufficient replacement is:

> Let \(\mathcal C\) consist of bodies affine-isomorphic, on their affine hulls, to finite expressions generated from a point by joins and Cartesian products.

The same clarification should be used wherever the class is defined. This is the only publication-facing issue found; no alteration of the potential, certificates, cutoffs, or claimed numerical endpoint is needed for the intended class.

## 3. Normalization and induction

The public v2 paper uses the conventional projection-body support function equal to the orthogonal projection volume. Thus a nondegenerate interval has \(\Pi K=[-1,1]\), \(R(K)=2\), \(a(K)=1/2\), and \(Q(K)=1\). Its formal point has \(D=H=Q=1\). The candidate matches these conventions.

For a product with positive dimensions \(r,s\), the inherited formula

\[
a'=(ra_A+sa_B)/(r+s)
\]

indeed implies

\[
H'=\frac{r+s}{r/h+s/j},\qquad
\frac{Q'}{Q_AQ_B}=\frac{g(r)g(s)}{g(r+s)}\frac{sh+rj}{r+s}.
\]

The cross weights in the last factor are correct. The arithmetic-mean relaxation of the harmonic state correctly uses the different expression \((rh+sj)/(r+s)\). Confusing these two weightings would invalidate the proof, but the submission and both replay implementations distinguish them correctly.

All positive-dimensional recursively generated states satisfy \(2\le H\le d+1\). The lower bound follows from the first interval, additive join states, and the dimension-weighted arithmetic product rule for \(a\). The upper bound is the inherited universal bound \(a\ge1/(d+1)\). Products with points are removable; joins with one or two points are included. Affine isomorphisms preserve the invariants.

The point has zero potential. Jensen’s inequality applied to the perspective functions \(H^2/D\) and \(H^4/D^3\) proves join superadditivity. For products the potential difference is exactly

\[
-T+\alpha\widehat G_2+\beta\widehat G_4.
\]

Harmonic ≤ arithmetic ≤ fourth-power mean gives \(\widehat G_2\ge G_2\) and \(\widehat G_4\ge G_4\). Thus proving the relaxed violation negative is a sufficient condition with the correct sign. The quadratic determinant is positive and the quartic coefficients are positive; the resulting function is globally strictly concave on the relevant positive states.

## 4. All 19,900 finite rectangles

The candidate lists exactly the ordered pairs \(1\le r\le s\le199\). Both the official verifier and the independent implementation checked complete ordered coverage, integer row types, the denominator, potential constants, and every supporting point’s rectangle membership.

At each rational point, the gradient is rational. Global concavity makes the tangent plane a valid upper bound over the **entire real rectangle**. The linear support maximum is attained at a corner. The independent replayer enumerates all four corners rather than using the submitted gradient-sign endpoint selection. The degenerate interval \([2,2]\) for dimension one is handled correctly.

All 19,900 complete rectangles satisfy the strict uniform upper bound \(-3/2000\). Both implementations locate the worst pair at \((5,5)\), with supporting coordinates

\[
h=j=5995534181/10^9.
\]

The independent exact upper value is

\[
-\frac{72313419913486810919675874374907052013284661763054373675942781684856361}
{46249464634924933400034791229751296000000000000000000000000000000000000000},
\]

approximately \(-0.0015635515023644162\). The displayed approximation is descriptive only. `independent_normal.json` and `independent_optimized.json` contain the exact rational evidence and the digest of every bound. They are byte-identical. The slightly different exact fraction from the candidate’s report is expected: the independent logarithm interval is different.

## 5. All 15,568 tail intervals and infinitely many dimensions

For each integer \(r=1,\ldots,199\), the transformation \(z=1/s\), \(u=J/(s+1)\) puts every required \(s\ge200\) into \(0<z\le1/200\) and every required state into the larger rectangle \([2,r+1]\times[0,1]\).

Symbolic recomputation verifies the two rational cancellations defining the quadratic and quartic coefficients. At \(z=0\), they reduce to

\[
G_2=h^2/(r+1)+3ru^2,\qquad
G_4=h^4/(r+1)^3+4ru^4.
\]

Thus the extra zero endpoint is a regular algebraic extension, not an unproved infinite-dimensional object. The factorial-ratio upper bound is justified either by the decreasing normalized factorial sequence or by the stated Robbins bounds. It yields precisely the submitted normalized logarithm, including the negative one-half log term.

On each cell, interval arithmetic encloses all coefficients, values, and derivatives. Every division’s denominator excludes zero; logarithm arguments stay positive. The checker verifies positive quartic coefficient lower bounds on the **whole real cell**, not just at integer reciprocal dimensions. Young’s inequality gives a positive diagonal lower bound for the quadratic remainder. Dropping the favorable logarithmic and quartic remainders is valid. Taking the worst permitted gradient component separately is an upper bound even though the coefficients and gradients are correlated through \(z\).

The submitted sign-split parabolic maximization is correct. The independent replay instead maximizes each endpoint-gradient parabola over the entire displacement interval; this gives the same valid worst-case envelope by convexity in the gradient parameter.

Both complete replays certify all 15,568 intervals with upper bounds below \(-1/100000000\). They check exact gap-free, overlap-free interval coverage from 0 to \(1/200\) for **each** of the 199 small dimensions. The observed maximum dyadic depth is seven, with counts:

- depth 0: 4
- depth 1: 3
- depth 2: 26
- depth 3: 74
- depth 4: 243
- depth 5: 835
- depth 6: 3,085
- depth 7: 11,298

The independent worst cell is

`[108, 56, 6, 2894165385, 18701552]`,

meaning \(r=108\), \(z\in[56/(200\cdot64),57/(200\cdot64)]\), \(h=2894165385/10^8\), \(u=18701552/10^8\). Its exact bound is stored in the report and is approximately \(-4.482151769730934\cdot10^{-8}\). The whole cell and whole state rectangle are certified, including their endpoints.

## 6. Analytic large dimensions and exhaustive boundaries

The claimed nonnegative-square identity for \(G_2-kx^2\) was checked symbolically, not only at the four sample points in the submitted checker. Its prefactor is positive. The quartic contribution is nonnegative, so maximizing the one-variable relaxation gives the sufficient comparison

\[
C^2/k<2\alpha e^{1-2T}.
\]

The factorial bound \(C^2<(r+s)/(2\pi rs)\) is justified. For \(r,s\ge160\), the submitted simplification bounds its left side by \(1615/7536\). Machin’s identity, alternating arctangent bounds, and the positive exponential partial sum prove the needed strict comparison by exact rationals. The final exponential upper bound uses the correct geometric remainder after the 12th-order Taylor term and proves \(e^{1.049}<571/200\).

There is no dimension coverage gap. By symmetry order \(r\le s\):

- if \(s\le199\), use the finite certificate;
- if \(r\le199\) and \(s\ge200\), use the tail certificate;
- if \(r\ge200\), both dimensions are at least 160 and the analytic lemma applies.

The analytic lemma actually overlaps the other regions. The values 159, 160, 199, 200, \(r=1\), \(s=200\), \(u=0,1\), and \(z=0,1/200\) cause no omission. Every finite expression is therefore covered by structural induction.

## 7. Exact arithmetic and adversarial controls

Both submitted logarithm implementations use valid positive atanh series after power-of-two range reduction and an explicit remainder majorant. Negative integer multiples reverse interval endpoints correctly. All rounding is outward by exact integer floor/ceiling operations. Floating optimization appears only in optional generators; neither proof checker imports those generators or relies on their convergence. Timing floats in the finite checker do not enter mathematical comparisons.

The independent verifier uses 24 terms and outward denominator \(2^{110}\), rather than the candidate’s finite 20-term/\(2^{96}\) and tail 28-term/\(10^{24}\) choices. It computes \(\log(m!)\) by taking an interval logarithm of the independently formed exact integer factorial, rather than summing the candidate’s cached integer logarithms.

All acceptance tests remain active under `python -O`. The official aggregate replay passed both modes. Independent normal/optimized reports are byte-identical. Twenty-four deliberately corrupted-certificate executions were rejected: twelve mutation classes, each tested in both modes. They include missing coverage, overlap, invalid dimension indexing, out-of-box points, wrong constants, invalid denominators/dyadic coordinates, and valid but mathematically failing support points. `negative_controls.json` gives the exact rejection for each.

Additional exact small-grid implementation controls test interval arithmetic, outward rounding, signed powers, reciprocal zero exclusion, and negative power-of-two logarithm scaling. These are regression controls, not substitutes for the mathematical interval proof.

## 8. Spectral passage, lower endpoint, and actual public comparison

The pinned v2 spectral supplement proves a genuine all-dimensional limit. Its upper estimate uses \(a\ge1/(d+1)\); its lower estimate uses self-joins and at most a bounded simplex remainder to fill every sufficiently large dimension. Thus

\[
\Gamma_{\mathcal C}=e\sup_K Q(K)^{1/(d+1)}.
\]

The candidate obtains strict \(\log\lambda(K)<T\) for each positive-dimensional body but correctly concludes only \(\Gamma_{\mathcal C}\le e^{1+T}\) for the supremum. There is no illicit promotion of pointwise strictness to a strict supremum inequality.

The inherited exact v2 checker and certificate were extracted from the pinned public commit and freshly replayed normally and under `-O`, including all four built-in corruption tests. The results are byte-identical to one another and to the candidate’s inherited replay. They verify the known self-similar lower endpoint \(2.8534\), the finite hull evidence, and the direct low-dimensional geometric checks. The lower endpoint remains inherited, rather than a new contribution of the mixed upper envelope.

The actual public `BELLMAN_UPPER_BOUND.md` at the pinned commit proves the quadratic ceiling with

\[
\alpha_*=(11/85)\log(189/128).
\]

Using \(\log t>2(t-1)/(t+1)\) for \(t>1\),

\[
\alpha_*-49/1000>4339/5389000>0.
\]

Thus the mixed theorem strictly improves the actual public constant, not merely its rounded decimal. The public supplement already mentions a numerical mixed quadratic/quartic direction near 2.8542. The submission appropriately claims exact global certification of its displayed potential, not discovery of the method or direction. No priority or unrestricted extremal claim is certified by this audit.

## 9. Delivery and remaining limitations

`candidate_source/verify.py` replays the three main new upper-bound checkers; it does not itself rerun the inherited lower checker or the unrelated classical-literature constant checker. This is not a gap in the upper proof. The present bundle includes and replays the pinned inherited checker independently. The geometric literature comparisons were outside this audit’s requested scope.

The only requested textual clarification is the affine-isomorphism class definition. For that intended class, the finite proof, all infinite tails, analytic large dimensions, normalization, induction, inherited spectral reduction, and strict comparison to the public quadratic ceiling pass. All original candidate hashes remain unchanged. No publication or push was performed.
