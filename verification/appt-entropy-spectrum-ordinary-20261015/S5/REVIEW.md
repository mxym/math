# Independent ordinary review of growing-sublinear APPT spectral rigidity

Decision: **PASS** for Theorems A–C and Corollary D, in the exact domain of the frozen manuscript identified below. This is a complete ordinary mathematical read by a different internal AI agent. It is not a Lean proof, an external human review, a priority certificate, or a new major-problem count. This report does not cover another manuscript or a future publication layout.

## Frozen input and actual read

The reviewed `PAPER.md` has 17,954 bytes and SHA-256
`da596b457eb4d2b82a1d231de065d07197def79414be0aaa1c1f069505e8e74b`.
The owner manifest has 13,144 bytes and SHA-256
`2d415d69e3728fb2b26f46ff9f866d067ead83efbc12b22f0fd4f1dec88586b8`.
The immutable owner ZIP has 126,843 bytes and SHA-256
`e12c3a78a1faa7966260a0931639ae45a1171085de7d3876cfefb5bcd50495d9`.
It was copied and safely extracted into this new reviewer-owned directory. Its original mathematical files, author-control result, manifest, and UTC fields were not changed. `INPUT_VERIFICATION.json` checks the 12 manifest-listed files and all 15 credited files, and checks that these, together with the manifest, are exactly the 28 extracted files.

I read the complete current manuscript, theorem map, local coverage map, source map, README, target, attempt ledger, bounded primary-screen record, and author helper/result. I also read the entire scientific text of all 15 captured credited manuscripts. This includes G's original all-state estimates and uniform G1 value, L's complete physical peak/width argument, S's actual-middle definitions, and the older value and spectral papers used for local range comparison. Their captured base is `1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f`; this is a source capture, not a claim about the current main head.

Reading those older texts for the present dependency and collision check does not re-certify every theorem in their original scopes, extend any prior report, or enlarge a Lean audit. The essential inputs here are the ordinary physical/value facts G1 and G7–G19, the finite physical coupling L7, and the actual middle notation. Four phase-4 scalar geometry manuscripts are not dependencies. No phase-4 certificate replay was used to certify this manuscript. The author capture/initialization programs were read, not executed; their Git actions were not performed.

The author primary-screen JSON describes a bounded author search. I did not re-run it or infer worldwide novelty from its empty exact-query results. The local comparison does substantiate the scope distinction: G1 already gives the value for all aspects, G3 gives the spectral criterion only in bounded aspect, S concerns positive finite limiting alpha/m, FAST_ORDER_SPECTRA concerns alpha/m tending to infinity, and the eventual exact fixed-m results are not uniform growing-m results. The older V paper already supplies the all-positive-order value range.

## Original quantum domain and objectives

The quantifiers are every sequence of actual complex positive semidefinite trace-one matrices on C^m tensor C^n, APPT after every global unitary, with integer 2 <= m <= n and

    m -> infinity, alpha -> infinity, alpha/m -> 0.

The orders are real. They are eventually greater than 2, so the real-power kernel used in the proof is in its valid domain. There is no bound on n/m, and it may oscillate. The theorem uses the actual ordered spectrum, with D = mn and y_i = D lambda_i. It concerns `(M_alpha-1)/(M*_alpha-1)` and the first-nonzero relative entropy deficit `log M_alpha/log M*_alpha`. It does not substitute a raw moment ratio or entropy divided by log D. Compactness/continuity and the explicit nonuniform pole state keep the optimizing value and these eventual positive denominators well defined.

The fixed notation is

    U = [3D/(D+2)]^alpha,
    V = alpha(alpha-1)(n/m)/2,
    wp = U/(U+V), wb = V/(U+V),
    chi = log(U/D), h = alpha log([3D/(D+2)]/y_1).

The physical cap makes h nonnegative. The bulk quantities use the actual index interval from R = m(m-1)/2 through j = D-m(m+1)/2+1, inclusive. Thus its exact size is **N = D-m^2+2**, including the square case N = 2. The pivot A is positive. With kappa = y_R/A-1, L = (m-1)kappa lies in [0,2]; theta is the actual middle mean fraction, and is set to zero at zero width. The definitions of z_i, J, and d_b retain this convention. No arbitrary outer-spectrum list is called APPT.

## A: the all-state excess identity and the weighted sum

The physical inputs G11–G14 give a middle deviation O(1/m), a bounded exceptional square mass Q_E <= C independent of n and the actual state, an actual second-eigenvalue bound v_m -> 1+sqrt(2), and Q <= zeta_m(gamma+8), zeta_m -> 1. The uniformity in n is present in G's witnesses, paired-gap estimates, and trace normalization. It does not assume bounded aspect or D comparable to m^3. The exact cap is retained instead of replacing its alpha power by 3^alpha.

The real-power Taylor integral bounds every middle kernel between

    a_alpha Q_B (1-delta_m)^(alpha-2)
    and a_alpha Q_B (1+delta_m)^(alpha-2).

Their relative difference tends to zero because alpha delta_m -> 0. This also handles Q_B = 0, using an absolute remainder bounded by o(1) a_alpha Q_B. For sufficiently large m, the actual first index is outside the middle interval. Isolating its exact centered kernel costs at most 1+2alpha in its polynomial subtraction. The other exceptional kernels have total at most a_alpha C v_m^(alpha-2). Dividing by U, both costs vanish: eventually u_D >= 8/3 and v_m <= 5/2, so a fixed constant times alpha^2(15/16)^alpha suffices. Replacing Q_B by Q costs a_alpha C = o(U).

More explicitly, the total error in (4.5), divided by U+V, is bounded by a middle relative remainder times

    zeta_m (V+8a_alpha)/(U+V),

plus terms bounded by constants times `(1+alpha)/U`, `alpha^2(15/16)^alpha`, and `a_alpha/U`. All vanish on every stated order/dimension path, uniformly in the actual matrix and aspect. Thus (4.5) is an identity at the claimed scale for **each** actual density, not only an upper estimate or a candidate calculation.

Combining it with G1 yields

    excess ratio = wp exp(-h) + wb Q/gamma + o(1).

The manuscript correctly controls the possible Q/gamma overshoot. Its weighted positive part is at most `|zeta_m-1|+8zeta_m a_alpha/(U+V)`, which tends to zero. Clipping Q/gamma at one therefore leaves an o(1) change. The remaining defect is a sum of two nonnegative losses; there is no cancellation with an uncontrolled negative variance loss. The peak loss `1-exp(-h)` is comparable to `min(1,h)`.

On a retained-bulk subsequence wb >= epsilon, gamma >= c_epsilon U/a_alpha -> infinity. The exact trace identity and Cauchy–Schwarz give `m(mu-1)=O(1/gamma)`, which tends to zero. This is stronger than a count-times-maximum estimate. Independently expanding the exact centered variance gives precisely (5.3), including its nonnegative actual-mean-square term. In particular that term is not exactly zero in general.

It follows that `Q/gamma = L^2 theta(1-theta)-J+o(1)` on every retained-bulk subsequence. The independent loss decomposition

    1-[L^2 theta(1-theta)-J]
      = (1-L^2/4) + L^2(theta-1/2)^2 + J

has nonnegative terms. Saturation is equivalent to L -> 2, theta -> 1/2 and J -> 0, exactly d_b -> 0. On vanishing-bulk-weight subsequences the capped weighted defect vanishes automatically. The retained-weight bad-subsequence argument proves the full weighted equivalence for arbitrary oscillations. This proves A, including both-contribution regimes. A minimum between branch defects would fail.

## C: actual W2 body law, with its precise retained-weight hypothesis

On any subsequence with liminf wb > 0, the preceding gamma -> infinity and trace estimate apply. If d_b -> 0, `J = E[z(L-z)] -> 0` concentrates the bounded middle variable at its two endpoints in mean square; its actual mean fixes their limiting weights at one half. Using `A = mu/(1+kappa theta)` gives `m(A-1) -> -1` and `m A kappa -> 2`. The scaled actual middle spectrum therefore converges to beta in W2.

The omitted exceptional mass is O(1/gamma), and its actual second-moment contribution is **Q_E/gamma -> 0**. A coupling to the bounded beta law then costs at most a constant times this second moment plus the omitted mass. This permits adding the exceptional atoms at the W2 level. Bare weak convergence alone would not do so.

Conversely W2 convergence to beta gives convergence of the second moment to one. That second moment is exactly Q/gamma. Equation (5.4) then forces d_b -> 0 by the nonnegative decomposition above. This proves C in both directions. The whole-path replacement of `wb min(1,d_b)` by `wb min(1,W2)` is valid by extracting retained-weight subsequences; the caps control all vanishing-weight subsequences. Unweighted W2 convergence is not asserted for negligible bulk weight.

## B: the two logarithmic regimes

When chi is bounded above, `(U+V)/D = exp(chi)+a_alpha/m^2` is bounded, since alpha/m -> 0. G1 makes the actual optimal moment increment bounded as well. For exact increments `0 <= s <= t <= R`, compactifying `log(1+at)/log(1+t)` with a = s/t and removable value a at t = 0 proves that its ratio tends to one exactly when a tends to one. Hence entropy nearoptimality is equivalent to A in this regime, even at a vanishing moment increment. The bounded positive factor 1+chi_plus does not change the weighted vanishing condition.

When chi -> infinity, wb -> 0, wp -> 1, and `log M*_alpha = chi+o(1)`. Necessity first establishes the physical peak y_1 -> 3. If y_1 <= 3-epsilon on a subsequence, bounding all exceptional kernels by that actual ceiling and treating the middle separately gives

    M <= 1 + exp(chi-eta alpha/2) + o(1)

for a fixed eta > 0 eventually. As chi <= alpha log 3, its logarithmic ratio to chi is bounded by a constant strictly less than one, including the case where the exponent becomes negative. This contradicts relative entropy nearoptimality.

After y_1 -> 3 is established, the nonlargest exceptional kernels and the removed peak polynomial are o(y_1^alpha), using the actual ratio v_m/y_1 <= 15/16 eventually. The whole middle increment, after division by D, is O(alpha^2/m^2) = o(1). Consequently, with q = y_1^alpha/D,

    M = 1+q(1+epsilon_m)+delta_m,
    epsilon_m -> 0, delta_m -> 0.

The error divided by **1+q** tends to zero, regardless of whether q vanishes, stays bounded, or diverges. This establishes the additive logarithmic reduction in (7.3). It is not obtained by logging the coarse o((U+V)/D) error from A. Since `log(1+exp(chi-h)) = (chi-h)_+ + O(1)`, entropy nearoptimality is now equivalent to h/chi -> 0. Conversely h/chi -> 0 implies h/alpha -> 0, hence y_1 -> 3 and the same state-relative argument applies.

Every arbitrary chi sequence admits, from any bad subsequence, a further subsequence bounded above or tending to infinity. These two cases give exactly B's weighted condition on all paths. Both necessity and sufficiency keep the full real-order quantifiers; no finite family replaces them.

## D: actual peak/width compatibility

If both weights stay bounded below, then gamma -> infinity and `exp(chi) = O(alpha^2/m^2) -> 0`. Either nearoptimality criterion forces h -> 0 and d_b -> 0. The exact physical L7 inequality `y_1 <= A(3-eta_m(kappa))` yields

    0 <= alpha[-log(1-eta_m/3)]
      <= h+alpha log A+alpha log(1+2/D) -> 0.

The right side is bounded above by `h+O(alpha/m)+O(alpha/D)`, so the argument does not require log A to have a particular sign. Thus alpha eta_m -> 0. With delta = 2-L, the independently checked exact formula is

    eta_m = 2(m-2)L^2 / [(m-1)(4+(m-3)delta)].

As L -> 2 its numerator after division by m-1 tends to eight. Therefore alpha eta_m -> 0 and alpha -> infinity force `(m/alpha)delta -> infinity`. This is a necessary margin. It does not replace the actual peak defect, guarantee a freely attachable spike, or strengthen the stated asymptotic window.

## Physical counterexamples and independent finite controls

The witness for every operator 0 <= X <= I is valid under every global conjugation: pairing with a unit-vector partial-transpose witness is at least its negative trace, which is at least -(m-1)/2 by the Schmidt Cauchy–Schwarz inequality. Thus the normalized I+[2/(m-1)]X example is actually APPT, at every required physical integer multiplicity. The pure and reduced-strength poles have the separate actual bound on the minimum pure-projector partial-transpose eigenvalue. The protected-spike lower states retain G's exact Schmidt SOS, positive trace normalization, and integer projection ranks. I independently expanded that SOS and the width/eta algebra.

For the balanced pure-pole example of Section 9, U/V -> 1, h = 0, and the actual zero-width theta convention gives d_b = 5/2. Its moment-excess and entropy ratios tend to one half. For the three-level example, the trace-normalized y values are exactly 1-1/m, 1 and 1+1/m in the stated integer proportions. Trimming the true inclusive middle interval gives `mu-1=1/N`, L = 2, theta -> 1/2, J -> 1/2 and Q/gamma = 1/2. This refutes omitting J. The reduced-strength square pole has h asymptotic to sqrt(alpha)/3 but h/chi -> 0, genuinely separating the two objectives in the claimed sublinear range. The ordinary asymptotic arguments establish these sequences; finite checks only supplement them.

The independently written `independent_checks.py` imports no author module and does not extract or execute author AST. Its actual run is

    runs/20261015T133349.443900Z/

The positive jobs passed: 4 symbolic identities, 32 compressed actual integer-spectrum exact cases (normalization, actual middle trimming, exact centering, real-power integer specialization, transport to beta), 9 noninteger-order kernel cases at 180 decimal digits, 3 actual reduced-pole separation cases, and 12 state-relative scalar log cases. The runtime was Python 3.10.12, SymPy 1.9, and mpmath 1.2.1. These are finite diagnostics, not numerical certification of the full feasible set or an all-sequence theorem.

Six separate false variants genuinely raised AssertionError at their intended mathematical assertions, and I read each traceback: branch minimum, deleting J, deleting the exact mean-square term, requiring unweighted W2 despite negligible bulk weight, demanding moment optimality from entropy optimality, and logging a coarse error measured against the optimum peak rather than the actual moment. Their inputs, complete stdout/stderr, script bytes and nonzero return codes are preserved. The final case is explicitly a scalar proof-method countercontrol, not a claimed new quantum state. No unexpected checker failure or manuscript correction occurred in this review.

The author wrote the stored 18-case Fraction helper and reported its PASS before this review. I read its code and result, verified their source/PAPER hashes and original UTC, and did **not** execute it. That author execution is not described as independent execution. The owner ledger also retains its two earlier nonmathematical path/patch failures; neither is silently erased or relabeled as a mathematical finding.

## Scope and disposition

All four statements pass for every actual APPT sequence with growing m, growing real alpha and alpha=o(m), all integer n>=m, and arbitrary aspect/weight/log-scale oscillation. C retains its positive-bulk-weight hypothesis, and D remains a necessary compatibility assertion. All explicit ties between positive contributions are handled by the weighted sum, without a unique-branch assumption.

This does not assert fixed-m synthesis, fixed positive-order unrestricted-aspect rigidity, every remaining zero-order window, positive finite or infinite limiting alpha/m rigidity, exact finite optimizers, eigenbasis rigidity, absolute separability, APPT=ASEP, a new all-order value closure, or any new Lean/audit coverage. No old Gaussian worktree or old review output was modified. No Git mutation, push, submission, release, DOI or third-party communication was performed. Final source/status/README/index publication binding, if requested later, is a separate task.
