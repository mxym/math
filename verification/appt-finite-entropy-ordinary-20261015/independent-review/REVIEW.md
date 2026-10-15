# Independent ordinary review: finite APPT bounds and the simpler entropy profile

**Decision: PASS for the complete revised R0–R2 written targets**, final mathematical manuscript SHA-256 `a1aa49bdeca6c194357734a0d20a169a15e6db8b77beeb096ec0c4433156f579`, theorem map `10770ad8dba389ac52e1a6c502c60511c023c3ab02a0ddcc868c73677a47b8a7`. No unresolved mathematical objection was found in the full actual-domain argument. The two scope corrections and their source histories are retained below. This is an internal independent AI-agent ordinary review, not external human peer review, a Lean proof or a priority certificate. Earlier P/U/linear/V reviews do not automatically certify R.

## Source capture and precise read scope

`capture_inputs.py` made a private 36-file snapshot and an input manifest. Its capture passed. The first mathematical source actually read here was the author's already corrected local-prior-work version, PAPER `296b66adc5939942366d47c2f2193d1eb07a62d982f0d4c25add8d2b0e7d9f29`, 297 lines. The entire PAPER, map, 139-line author checker, literature screen, research log and local-prior-work diff were read. The original 47b4… manuscript and original author-run bytes were preserved in the snapshot rather than relabeled as the corrected source.

All twelve credited-input files matched their declared sizes and SHA-256 values and the immutable main commit `665e9e26d43fa83cb7eb6823cd2cd56b1ac08680` byte for byte. I read in full the following mathematical texts in this review:

- SHARP_ASYMPTOTIC.md, all 259 lines, particularly its finite all-unitary edge rearrangement, star and row-degree-square argument in Sections 2–4.
- The published P manuscript, all 195 lines, including the exact finite physical budgets, lower-state positivity and trace factors.
- Growing-order PAPER.md, all 500 lines, including its explicit physical inputs, adaptive Schmidt SOS, real-power estimates and positive-log argument.
- UNIFORM_PROFILE.md, all 181 lines, including its exact U0 profile and U2 quantifiers.
- LINEAR_ORDER_VARIATIONAL.md, all 343 lines, including L2/L5, the actual quantum upper bridge, all scalar lower competitors and L20–L22.
- ALL_ORDER_VARIATIONAL.md, all 267 lines, plus its complete 16-line map and 107-line existing review record. These demonstrate that the all-positive-order/all-aspect range had already been covered before R.
- The complete 30-line growing-order theorem/formalization map.

I reread the cubic-entropy manuscript's complete Section 4, lines 126–184, for its finite p/beta definitions, budget and shifted graph mass. I did not newly audit that entire 461-line paper in this R task. I inspected the relevant fields of the source-bound P review and final-status binding and verified their exact hashes; their earlier complete P review retains its own scope. The U2 fixed-order and zero-order companion theorems are credited existing inputs, not newly executed or wholly re-audited underlying manuscripts in this task. Nothing in this review broadens any old Lean root set.

After my finite-error comparison finding, the final three changed files were separately captured under `snapshot-v2/`. The entire exact PAPER/map/log differences were read. The author checker, source manifest and literature screen are unchanged. The original new bounds and limit proofs are unchanged; the final text adds the correct comparison explanation and the immediate minimum of two independently proved finite upper errors, R2b. The final source is 304 lines. Saved diffs and `V2_CAPTURE.json` bind this delta rather than pretending the original independent run used the later text bytes.

## R0: full-domain finite upper estimate

The physical domain remains the original complex PSD trace-one density matrices with partial-transpose positivity after **every** global unitary. Compactness and positive-order entropy continuity give the maxima. No list of eigenvalues satisfying necessary inequalities is promoted to a sufficient definition of APPT.

The finite graph inputs apply to every (3\le m\le n\), without cubic dimension scaling or bounded aspect. Top R, bottom K and diagonal slots can be assigned distinctly because (R+K=m^2\le D\). The actual Schmidt witness implies the adjacency upper bound for every edge rearrangement. A star bounds the first m−1 shifted squared gaps by four; the separate row placement and degree-square inequality bound the rest by four after retaining the nonnegative baseline cross terms. Thus the shifted squared gaps sum to at most eight. With the actual definitions, (\eta_i=p_i+\beta_i-\beta_R\ge p_i\), so (\sum p_i^2\le8\). The maximally entangled witness gives the p/beta budget at most m. The single-edge witness and trace one give b>0 and x_i≤3. Consequently (1\le v\le q\le2\), other indices satisfy x_i≤v, and the exact raw mean obeys (s\ge1-m/D>0\), including singular actual states.

For every real (\alpha\ge2\), the integral representation of the divided Taylor remainder has nonnegative integrand and is nondecreasing in p. The value at p=0 is taken continuously. Because (3-v\ge1\),

\[
0\le J_v(p)\le J_v(3-v)\le3^\alpha/(3-v)^2\le3^\alpha.
\]

Adding the genuine linear Taylor contribution on the top indices, bounding the other values by v and using both head budgets proves

\[
D^{-1}\sum_i x_i^\alpha\le v^\alpha+\frac{\alpha m}{D}v^{\alpha-1}+\frac{8\,3^\alpha}{D}
\le(1+\alpha m/D)q^\alpha+8\,3^\alpha/D.
\]

This estimates every actual state, before maximizing. It requires neither integral rank relaxation nor a bounded number of exceptional eigenvalues. The isolated peak coefficient eight has no polynomial dependence on the order.

The exact state deficit is ([\log(D^{-1}\sum x_i^\alpha)-\alpha\log s]/a\), with (a=\alpha-1\). The logarithm of the preceding sum is bounded by the larger exponent plus (\log(9+\alpha m/D)\). Applying (\log(9+z)\le\log9+z\), \(\alpha/a\le2\), \(\log q\le\log3\), and (-\log s\le m/(D-m)\) gives

\[
E_\alpha\le H+\log27/a+2m/D+2m/(D-m)
\le H+\log27/a+4m/(D-m).
\]

All constants and denominators therefore hold at every stated finite dimension and real order, not just eventually. At \(\alpha=2\) the divided remainder is constant in p; no strict monotonicity was needed.

The old P upper bound has the same H on this domain and was separately proved. Taking the minimum of its error and the new error proves the added R2b directly. It does not assert that the new error is smaller everywhere.

## R0: actual integer-rank lower bound

For the two stated finite conditions, (\alpha t\ge2\) and (D/(\alpha t)\ge2\), the rank (k=\lfloor D/(\alpha t)\rfloor\) is a genuine integer with (1\le k<D\). Its fraction lies between (1/(2\alpha t)\) and (1/(\alpha t)\). A rank-k projection exists in the actual D-dimensional space. For any Schmidt witness W, its total negative spectral weight is at most ((m-1)/2=1/t\). Pairing W with any projection is bounded below by minus that weight; this holds for every global-unitary image of the projection. Thus ((I+tP)/(D+tk)\) is an actual all-unitary APPT density for every integer rank, with full density-matrix rank D.

Its exact normalized moment contains the denominator ((1+t\theta)^\alpha\). The numerator is at least (\theta q^\alpha\), and \(\alpha\log(1+t\theta)\le1\). These give precisely R3 after division by a. The lower inequality is valid even if its right side is negative. There is no replacement of k by a fractional rank or unproved extension after either finite rank condition fails.

The separate pure-spike state is normalized by D+2. Its exact spectrum proves R12 for every real order at least two. The loss 4/D is retained, rather than setting its raw peak equal to three after normalization.

## R1: every superlinear sequence and the full supremum

Fix an arbitrary sequence (m\to\infty\), all integer (n\ge m\), and \(\alpha/m\to\infty\). The proof's split at \(\tau=\log3-\log D/a\) has two exhaustive branches; it is not an imposed relation between n and the order.

If \(\tau\ge\log3/2\), H eventually equals tau and is bounded away from zero. The finite upper error vanishes since (m/(D-m)\le1/(m-1)\), and the actual pure-spike lower has vanishing 4/D loss. This gives the relative equivalent on that entire branch, including arbitrarily huge orders relative to D.

If \(\tau<\log3/2\), then (D>\exp[(\log3/2)a]\). Here \(m=o(\alpha)\); polynomial factors in m and the order are negligible against D. Both finite rank conditions eventually hold. The upper error relative to (H\ge\log q\sim2/m\) is (O(m/\alpha)+O(m^2/D)\to0\). The adapted-rank lower loses only (O(\log c/c)\) relatively, with (c=\alpha/m\to\infty\). The pure-spike error 4/D is also o(log q). Taking the better of these two actual states gives (E_\alpha\ge H-o(\log q)\), hence the required relative lower bound even when H tends to zero. The argument is uniform in all aspect ratios because no remaining error depends on a bound on n/m.

Both branches can recur or oscillate. Applying the preceding estimates on their respective subsequences proves R4 for the entire arbitrary sequence. A failure of the claimed supremum for any diverging lower cutoff V_m would select a violating n,alpha sequence with \(\alpha/m\ge V_m\to\infty\), contradicting R4. This verifies R5's exact quantifiers, rather than replacing a continuum supremum with a sampled parameter grid.

## R2: entropy-only scalar simplification and all positive orders

For fixed positive c, the scalar function is continuous on the compact width/mixing rectangle, including L=2 because its protected head tends to zero. The maximum is attained and positive: the pure-bulk L=2,theta=1/2 competitor gives cosh c>1. Its logarithm is therefore well defined even when the peak ratio is zero or tiny.

The credited exact theta optimization and monotonicity of the pure-bulk objective in width give R15. For c≥1 this supplies the lower logarithmic estimate (2c-\log(2c)-2\). The L=0 competitor gives 1+r. Every scalar bulk term is at most exp(2c) and every head term at most r, proving R16 uniformly for every r≥0. Since its comparison maximum is at least 2c, the relative logarithmic error vanishes as c grows independently of r.

For (r=3^\alpha/D\), the logarithmic peak differs from \(\max(0,\tau)\) by at most \((\log3+\log2)/a\). Also \(2c/a\sim\log q\sim2/m\) on the superlinear regime. Dividing all comparison errors by (H\ge\log q\) proves R17 on every such sequence. No unrestricted substitution (u_D^\alpha\sim3^\alpha\) has been used. That substitution is false as a relative moment statement at sufficiently large order; only the entropy logarithm is compared here.

Below sqrt(m), U2 has exactly the same explicit profile and the needed n-uniform quantifier. Above sqrt(m), the orders diverge. A counterexample sequence has a subsequence with c bounded, handled by the credited complete linear L5 for a single fixed C, or a subsequence with c→infinity, handled by R4/R17. The bounded case includes c→0 because L5 already proves the needed moment-excess accuracy there. It is not inferred merely from multiplicative moment convergence. This contradiction proves the supremum over all n≥m and every positive real order, including alpha=1 through the existing continuous branch, arbitrarily tiny orders, alpha>D and oscillations among regimes. Fixed-m all-order relative accuracy and exact endpoints alpha=0,infinity are not newly asserted.

## Existing range and corrected contribution

The older calibrated V manuscript already proves the full all-order/all-aspect entropy range and a stronger large-order moment comparison. Its mathematical statement and prior ordinary review are source-bound here and were read. The initial R screen missed that companion by relying on an earlier manuscript's stale limitations. The author discovered this before this R review began and retained the original six files and first finite PASS. I do not claim that I discovered that earlier local-source error, nor that a finite PASS established novelty.

The corrected target is an explicit finite estimate, the simpler superlinear maximum formula, and an alternative uncalibrated entropy-only scalar expression on an already covered range. It is not the first all-order range closure, another counted major conjecture solution, or a stronger unrestricted moment theorem. The final title, opening, map, literature record and limitations accurately carry this distinction.

## Finding from this review and its resolution

**F1: total finite pointwise domination was not valid.** The first reviewed label called R0 a stronger finite upper bound. At m=n=3 and alpha=10^6, its total error is about 2.0000033 while the older P error is about 1.0000335. The new order-dependent error is smaller, but its displayed dimension term is twice as large. I sent this concrete comparison to the author and recorded it as a rejected erroneous claim in the independent run.

The author preserved the pre-clarification PAPER/map/log, changed the label to describe the O(1/alpha) order term, disclosed the larger dimension term and lack of total pointwise domination, and added R2b as the minimum of both valid errors. I verified the exact final diffs. Neither R2 nor R4/R8 changed. This resolves the finding. It was a comparison-scope correction, not a counterexample to either finite upper inequality or to the relative theorems.

## Actual independent execution and external screen

The author checker and its original run were read but not executed. That stored PASS is bound to original PAPER 47b4… and does not become a new execution of final a1aa… after metadata corrections.

I wrote a separate checker without importing or executing author code. One actual run, `runs/20261015T101117.860481Z/`, passed on the privately frozen 296b… source manifest. Its script is `b8563b464cd93264baeb8385105c342603c28a5f88126a424a1ee6586d2d443d` and result `aa91cef013eff133563d41b462f5e726b5dc14944017f00a3edb5093695d5027`. It checks two symbolic identities; 480 exact rational and 120 noninteger-order remainders; 720 finite physical-spectrum upper comparisons; 51 applicable adapted integer-rank lower comparisons; and 1512 scalar bracket samples. The physical spectra include maximally mixed, pure spike, a noncommuting two-spike convex mixture, singular I−vv*, and projections at four selected actual integer ranks. It does not enumerate every projection rank or optimize every physical matrix.

Seven incorrect statements actually produced and saved their expected AssertionErrors: omitting the linear term, omitting the exponential remainder scale, omitting the trace factor, using the floor outside its rank conditions, replacing integer rank by fractional rank, promoting the entropy profile to unrestricted relative moment accuracy, and the pointwise-total-error claim just corrected. There was no unexpected independent checker failure. No new run was needed for the final explanatory edits or the direct min-of-two-bounds consequence; the original executed bytes and manifest remain intact.

I separately opened the official abstract/version pages for [Tran 2609.18568v1](https://arxiv.org/abs/2609.18568v1) and [Ahiable–Kothakonda–Winter 2608.03390v2](https://arxiv.org/abs/2608.03390v2). Their displayed scopes concern purity, geometry and von Neumann entropy; I did not newly audit their full papers. I independently reran the three arXiv-domain queries recorded in the author literature screen; the pooled result was empty. This is a bounded context screen, not an absence proof or priority certificate. The decisive prior-range correction here is the explicit existing local V theorem, not an inference from those empty searches.

Finite controls and sampled scalar values supplement the ordinary proof; they do not certify all feasible matrices, real orders or unbounded sequences. This review performed no Lean/Lake/kernel execution, Git mutation, public index edit, submission, Release, email or new subagent work. It does not certify future publication metadata or evidence layout.
