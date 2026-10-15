# Independent ordinary mathematical review of S8

Decision: **PASS for the exact frozen manuscript and its stated scope.** No mathematical correction to the author manuscript is requested.

Reviewer: internal OpenAI AI agent `/root/breadth_quantum_resume_20261015`, a different role from the S8 author agent. Review requested by the root for finite wrap-up. This is an internal ordinary mathematical/code read, not human peer review, Lean verification, a priority determination, or a new-major-problem claim. No independent review status for other pending S5/S6/S7 manuscripts is implied.

## Exact object and read scope

Author: Yongxian Zhang, South China University of Technology; author identity, no-funding statement, OpenAI assistance disclosure, original rights reservation and third-party attribution are retained verbatim in the frozen files.

The reviewed `PAPER.md` has SHA-256 `9fdb0649010809711223abd1f30778652ae9bde0cd1d768b66336c3ed22e5cb1` (14,455 bytes). The author manifest has SHA-256 `be554dd0e2ae2ce1d9bf41e55e1a59a729757711c0256ec1ec6ea0b580eabf83`. The owner ZIP has SHA-256 `d3d1a625705c380dea45c5154dcd35b742e9291f178884ecc3837cf343b06996`. All 14 ZIP members were fully read, copied to this private directory, and compared byte for byte with the live frozen source. Every one of the 13 author-manifest file entries was checked for both length and hash. `INPUT_BINDING.json` and `DEPENDENCY_BINDING.json` record exact paths and digests.

Actually read in full: S8 PAPER, README, TARGET, THEOREM_MAP, SOURCE_INPUTS, ATTEMPT_LEDGER, author manifest and freezing source; the four credited scalar manuscripts GLOBAL_MIXED_PHASE, CRITICAL_UNIQUENESS_CERTIFICATE, NO_ISLANDS and LAST_MIXED_BOUNDARY; the additional original PURE_ENVELOPE_GE_ONE proof; and the complete credited L and S mathematical texts. L and S were checked byte for byte against their stated main-tree commit `1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f`.

Actually read source code in full: `critical_exact_intervals.py`, `global_mixed_turn_certificate.py`, both complete certificate replayers, `global_mixed_turn_algebra.py` and `no_islands_author_controls.py`. Both complete certificate JSON files were loaded, and **every stored leaf/bound/cover** was recomputed in the private copies. The author algebra control and both author replay JSONs were read. The entire no-islands author-control JSON, including all 92 finite samples, was parsed and checked; these samples are not proof of its global inequalities. The global certificate also received a separate reviewer partition check described below. Optional older floating discovery files and their freeze/housekeeping programs are hash-bound as manifest inputs, but are not relied upon as mathematical evidence and are not claimed here as a new scientific full read of those discovery programs.

One initial combined tool display truncated the end of GLOBAL_MIXED_PHASE; the entire missing end, from section 9 through the final reproduction/status text, was explicitly reread. No unread truncated passage is counted as read. No other evidence-read failure remained unresolved.

The old scalar geometry and the L/S physical results are credited theorems in their original frozen scopes. Their actual hypotheses and proof interfaces were read. The present review independently checks the new S8 implication; it does not renew, enlarge or replace an older Lean audit or recursively re-audit all historical quantum witnesses. In particular the physical transfer below invokes S, rather than treating scalar samples as proofs for arbitrary APPT matrices.

## Reconstruction of the new mathematical argument

All scalar variables retain their original domains: `c>0`, `r>=0`, `0<=L<=2`, `0<=h<=1`, with `P(c,2,h)=0`. The pole is the entire redundant coordinate class `L=0`, counted once. The full credited scalar geometry supplies exactly two coexistence curves on `0<c<c_star`, all boundary ties, negative definite Hessians for the relevant interior critical points, and the nondegenerate triple point. It supplies the global geometry, not the new monotonicity.

For an interior critical point let `K=2c`, `k=cL=Kx`, `0<x<1`, and

    a=2k^2/[3(2c-k)], T=r q(k)e^(-a), a_k=2x(2-x)/[3(1-x)^2].

Here `a_k` holds `c` fixed. The original `h` derivative of `F` has a strictly decreasing affine numerator. At its interior zero the bracket in `F=e^(-kh)[1+h(e^k-1)+r e^(-a)]` is exactly `1/q(k)`. Substitution therefore gives

    h=[1-q(k)-T]/k, log M=g(k)+T,
    f_k=g'(k)-T[s(k)+a_k].

An interior critical point has `T=g'(k)/(s+a_k)>0`; in particular its `r` is strictly positive. There is no application of strict positivity of `M_c` to a nonexistent interior stationary branch at `r=0`.

Holding `k,r` fixed gives `a_c=-4k^2/[3(2c-k)^2]` and hence `f_c=4T x^2/[3(1-x)^2]`. For the actual stationary value with `r` fixed, both coordinate derivative terms vanish. Thus

    M_c/M=4T x^2/[3(1-x)^2]>0.

Changing to fixed `L` adds exactly `L f_k=2x f_k` to the partial derivative. This vanishes only after stationarity is imposed. Directly, at fixed `L`, `k_c=L=2x` and `a_c=G(L)=4x^2/[3(1-x)]`; substituting the critical equation gives precisely the same value. No step varies `c` while holding the dependent variable `K=2c` fixed.

The key strict upper bound is valid for every relevant interior critical branch:

    M_c/(2M)=g'(k)[a_k/(s+a_k)][x/(2-x)]<g'(k)<g'(K).

Both displayed bracket factors lie strictly between zero and one. The final strict comparison follows from the explicit `g''>0` proved in NO_ISLANDS, or from the differentiable strict convexity argument in S8. The latter is valid: use the interior maximizing `h` at the middle parameter in the log-MGF strict convexity inequality, then use the endpoint maxima. A differentiable strictly convex function has strictly increasing derivative on an interval; a positive pointwise second derivative is not being inferred from arbitrary strict increase.

The actual envelope derivative in `r` is `M_r=P`, with `0<P<1`. Independently, `M_r=M q e^(-a)=e^(-kh-a)`. This is the original `P`, not the derivative of `log M` and not a new peak-weight normalization.

Now, and only now, differentiation along the two coexistence curves yields

    r_B'=[2b'(2c)-M_c]/P>0,
    r_P'=M_c/(1-P)>0.

On the lower curve `M=b(2c)`, so the first numerator is strictly positive by the preceding bound. At the triple point the same mixed point remains strictly interior and nondegenerate; the credited analytic local extension gives finite derivatives with neither denominator vanishing. Thus both endpoint derivatives are also strictly positive. The credited critical theorem supplies `A_star=W_K>0` and

    r_B'=r_0'+2r_star A_star,
    r_P'=r_0'-2p_star r_star A_star/(1-p_star).

Together with the newly proved positivity this gives **`0<r_P'<r_0'<r_B'`** at the triple point. `W_K>0` is an analytic consequence of the admissible-domain no-islands argument; the old exact certificate supplies the stated unique nondegenerate triple-point location. No new interval domain is assumed.

For the small-`c` endpoint, lower coexistence is squeezed by `0<r_B<r_0` and `r_0(0+)=0`. For upper coexistence the quotient `Q=(B-1)/(1-P)` is used only at `L>0`. For `0<c<=1`, the original centered two-point random variable has variance `L^2 h(1-h)` and absolute value at most two. The integral Taylor bound gives `0<=B-1<=C_0 c^2 L^2 h`, `C_0=e^2/2`. For `0<L<2`, `H=Lh+G(L)>0` and `1-e^(-cH)>=cH/(1+cH)`. Hence

    Q<=C_0[c L^2 h/H+c^2 L^2 h]<=C_0(2c+4c^2)<=3e^2 c.

The inequality `L^2 h/H<=L<=2` covers all `h>0`, while `h=0` has numerator zero and positive denominator. At `L=2` the denominator is one and the direct numerator bound also suffices. At `L=0` no quotient is formed. The identity `F-(1+r)=(1-P)(Q-r)` makes the upper threshold `sup Q`; consequently `r_P(0+)=0`. This is a uniform endpoint bound, not substitution of varying `c` into an unproved quantum limit.

Strictly positive derivatives, the endpoint values `0,r_star` and the credited analytic extensions make `r_B` and `r_P` analytic bijections `(0,c_star)->(0,r_star)`. The inverse function theorem applies everywhere needed. `r_B<r_0<r_P` reverses to `c_P<c_0<c_B`. For fixed `0<r<r_star`, the inequalities give pole only below `c_P`, the exact pole/interior tie there, one interior phase until `c_B`, the exact interior/bulk tie there, then bulk. The pure-envelope result extends bulk to the entire remaining positive `c` axis. At `r=r_star` only the triple transition occurs; at `r>r_star`, strict increase and unboundedness of `r_0` give the unique pure crossing above `c_star`; at `r=0` the unique bulk point occurs for every `c>0`. Thus no tie or high-`c` component is omitted. The two boundary mixed coordinates need not equal each other.

Expanding the two analytic inverse functions at `r_star` gives

    c_B-c_P=(1/r_P'(c_star)-1/r_B'(c_star))(r_star-r)+O((r_star-r)^2),

with a strictly positive coefficient. The sign and the direction of approach are correct.

## Original-matrix transfer

The manuscript invokes the original complex PSD trace-one APPT objects with the all-global-unitary quantifier. It keeps the actual middle interval, actual mean, finite `eta_m`, `J`, and nonnegative **actual** peak loss `Pi`. Their definitions agree with the frozen S text. The resulting condition is the relative first-nonzero entropy-deficit nearoptimality of S, equivalent to all three requirements: distance to the **full** scalar maximizing set tending to zero, `J->0`, and `Pi->0`. Phase names or empirical laws alone do not replace this equivalence.

S supplies actual attainment and the W1 body-law statement. The pole law is a point mass, while the mixed and bulk laws have strictly positive two-point weights with distinct gaps `0<L<2` and `2`; the triple point therefore really gives three distinct possible limiting body laws. Alternation is allowed. The peak correction and uniform flattening are invoked only at `r>0,l<2`; the `l=2` case retains only its vanishing peak-moment conclusion.

The physical window remains **`m->infinity`, `n>=m`, real `alpha>1`, `alpha/m->c in (0,infinity)`, `3^alpha/(mn)->r<infinity`**. A family of fixed-`r` scalar slices over all positive `c` is not a new matrix theorem along `c->0`, `c->infinity` or `r->infinity`. There is no finite-dimensional exact-maximizer assertion, basis uniqueness or enlargement of Lean coverage.

## Executed checks and actual failures

`RUN_LOG.json` and the complete stdout/stderr files preserve the final runs, program hashes, UTC times and return codes. All five programs returned zero: the two unchanged author certificate replayers on private copies, the author symbolic controller, the author no-islands controller, and the reviewer's independent controls. Author controllers remain author controls; their execution alone is not this review.

The 73 critical leaves and all their constants, witness and endpoint derivatives were replayed exactly. All 74 global-turn leaves were recomputed; the reviewer additionally checked the full rational rectangle partition using every elementary coordinate-grid cell, independently of the author's active-slab adjacency routine. The six stages contain respectively `78,1,108,9,1,4` such cells. The seven cap-excluded boxes remain restricted to the correct domain. This confirms the supporting old scope and does not extend it.

Independent controls additionally include eight exact symbolic derivative/chain-rule identities; 656 exact-rational containment checks of integer interval arithmetic, including negative endpoints; differentiation of the **original** `F` at 45 stationary points; both original-coordinate coexistence systems and independent central differences at `c=0.2`; the original-coordinate triple system and slope order; and 80 small-`c` edge checks. Numerical values are falsification controls, not proof of all-parameter assertions. For orientation only, the triple system gives approximately `c=0.2596735326882963`, with slopes `r_P'=0.1534399369 < r_0'=0.2665499448 < r_B'=0.3062603034`.

All nine expected negative-control assertion failures are retained, including their actual messages, in `INDEPENDENT_CONTROLS.json`: two zero-containing reciprocal intervals; deletion of a global cover leaf; duplication creating overlap; deletion of the strip touching `K=0`; one-integer forgery of a recorded bound; equating fixed-`k` and fixed-`L` partials away from stationarity; replacing `M_r` by the log-value derivative; and asserting a strictly positive fixed-`k` derivative at `r=0`. There were **no unexpected mathematical or execution failures** in the completed checks. The initial display truncation was repaired by actual rereading as recorded above. Nothing is relabeled as a successful failed research attempt.

## Preservation and disposition

All review writes and executions were confined to this review-private directory. Author manuscripts, owner ZIP, prior evidence, publication indexes and Lean sources were not modified. No push, submission, release or new research occurred. HN0 remained paused throughout; its clock SHA-256 before and after is `d3aab86688c0a69e4cdcaa71f825e1c301017233d9a072adb7c47480af4c6b56`, and its preserved effective time remains **3965.905531 seconds**. This ordinary review time is not added to that research stage. No live review job remains.

The accompanying report manifest binds this report, frozen input bindings, all executed review code, complete results/logs and final pause/source-integrity checks. The decision is limited to the exact S8 paper hash above and the explicitly credited hypotheses. The root may bind the result to publication metadata as part of its already authorized finite integration. The reviewer stops here.
