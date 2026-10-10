# Research log — 10 October 2026

User priority: mathematical progress, no additional preprints or Release preparation. Started from live main 9526e94c after checking current work and applicable instructions. The universal-extraction work is already complete in its stated regimes. This continuation returned to the original unsolved arbitrary-dimensional APPT purity conjecture rather than extending publication infrastructure or boundary asymptotics of an adjacent task.

The first attempted route was to extend the flat-minimum weighted-star bound. A proposed universal inequality putting the spectral radius of a suitably rearranged weighted complete graph above the Euclidean edge norm fails for a sufficiently large isolated heavy edge plus a light complete background. This was an obstruction to that proof strategy, not a theorem or a counterexample to APPT.

That failure suggested retaining the heavy edge AND the light background. Their two-dimensional equitable quotient gives an exact PSD condition. Interpreted through partial transposes of Schmidt projectors, it proves positivity for a one-spike/plateau density family. Numerical one-variable searches were used only to locate promising parameters. Subsequent fixed rational parameters yield an elementary all-unitary sum-of-squares proof. Increasing the plateau projection rank, rather than restricting it to the number of negative witness eigenvalues, substantially improves the construction and gives the compact 10x38 example recorded here.

The exact proof does not depend on any optimizer, float result, finite chamber list, or previous Lean package. The rank-one projector is nested inside an arbitrary rank-k projector to realize the three-level spectrum. The physical positivity inequality even holds without nesting. Both the conjugated projection and the conjugated vector are bounded against a general Schmidt witness; the inequalities are valid without their commuting with the witness. This avoids replacing APPT with a necessary-only relaxation.

Source version audit: web.run retrieved arXiv v1 and failed on v2. Direct primary abstract retrieval instead revealed v2, revised 18 September 2026. The complete primary v2 HTML was then read at Theorem 6.3, Conjecture 6.7, and the concluding open-problem discussion; it retains the target unchanged. A version mismatch is not suppressed. Targeted searches did not locate an earlier counterexample to this exact conjecture, but no exhaustive historical-priority certification is made.

Completed mathematics: explicit APPT counterexample; all-dimension projection/spike positivity identity; a strict APPT-interior violation; an infinite family m>=11,n=4m; and the exact wider subclass criterion in the range binom(m,2)<=k<=mn-binom(m+1,2). The new open optimization target is the true multilevel maximum, not a proof of the now-refuted formula. No further manuscript or Release is generated.

Further progress in the same research cycle: the two-parameter criterion yields rational counterexamples in every fixed aspect ratio n/m->gamma>=1, with scaled centered-purity coefficient 4+gamma instead of max(4,gamma). A finite moment inequality matches the coefficient throughout the exact-membership intermediate-rank one-spike/plateau subclass. This is a complete subclass asymptotic and an unrestricted lower bound, not a new unsupported global formula. The unrestricted upper-bound problem remains explicit. The successful exact checks are supporting algebra only; no CI or Lean proof is claimed for this checkpoint.


## Unrestricted bounds and the sharp balanced law

The continuation began by checking live main at 4f8d2c72 and the existing working proofs. A separate worktree was used, and a concurrent README-only update was preserved. The first new construction moved the plateau rank from order m^2 to strictly between m and m^2; its coefficient 6 disproves the tentative unrestricted 4+gamma bound in square systems. A complete uniform graph limit then yielded the sharp four-level-sector coefficient max(6+gamma/4,4+gamma).

The major unrestricted step pairs top and bottom eigenvalues in actual Schmidt-projector tests. Every edge rearrangement has bounded spectral radius. A star controls the first order-m squared gaps, and a rectangular rearrangement controls the next order-m^2 gaps. A quartile variance inequality and a normalization bootstrap give the universal balanced upper constant 8, with no spectral-shape assumption. An additional scalar estimate gives the stated rectangular upper bounds.

The lower constant initially failed to match. Simply declaring many plateau contributions independent would be invalid: their witness graphs can interact. The successful argument uses fixed lacunary exponent deficits. Only matched amplitude scales survive in a Rayleigh quotient; a weak probability-measure limit turns their interactions into a graph whose edge labels are sums of nonnegative atom positions. Lacunarity makes this graph a forest. Its bipartite Hilbert--Schmidt bound permits total plateau square mass approaching four, in addition to the isolated spike's four. Every fixed finite hierarchy is given a positive safety margin before the dimension limit. Taking that limit first, then removing the margin and increasing the number of levels, proves the lower constant 8. Thus the balanced leading-order maximum is closed rather than only conjectured.

Checks run in the local analysis environment and on the authorized VPS use exact rational/integer arithmetic. The VPS outputs with and without Python assertions are identical. They test physical partial-transpose pairings, both variance estimates, all small-graph odd-moment bounds, lacunary forests, nested-flag trace identities and the finite coefficient-6 example. Deliberate mathematical failures include a nonlacunary triangle and a too-large spike. No independent CI, Lean verification, or external peer review is claimed for this cycle; none of these finite checks replaces the compactness proof.

Current core target: the exact leading constant for fixed gamma>1, the exact finite-dimensional maximum and its extremizers, or the absolute-separability question for these APPT families. The balanced leading coefficient is 8; neither an arbitrary rectangular equality nor an extremizer classification is assumed. No manuscript or Release work was performed.


## Final triangular improvement and a uniform all-regime equivalent

The rectangular argument initially closed only the balanced coefficient. Retaining the within-part weights sharpened the result through aspect ratio three. The final upper argument no longer needs a balanced cut: assign the residual paired eigenvalue gaps in decreasing order to successive rows of the upper triangle. Every vertex degree includes earlier larger weights, so its square controls the entire next row. This bounds all gaps except a single star, and retaining the complete-graph baseline before squaring yields

    purity-1/D <= b^2 max{8,4+D/(m-1)^2}.

Its normalization error is uniformly O(1/m), even when n/m is unbounded. It exactly matches the maximum of the multiscale-eight construction and the broad-plateau/spike construction. Thus the true fixed-aspect coefficient is max(8,4+gamma), with transition at gamma=4; the earlier leading-constant gaps are now closed.

A separate fixed-m argument uses the uniform Schmidt witness to bound all but m^2-2 eigenvalues in an interval of ratio (m+1)/(m-1). The elementary interval second-moment inequality gives D*Pmax -> m^2/(m^2-1), matched by an actual projection state I+2P/(m-1). A sequential argument combines the fixed-m and growing-m results into the uniform equivalent

    Pmax(m,n)-1/(mn) ~ max{8,4+mn/(m^2-1)}/(mn)^2

as total dimension grows over all pairs 2<=m<=n. This is not an exact finite interpolation formula. The fixed-m first-order bound is recorded as a derived consequence, not claimed as a historically new principle.

The new checker separately tests the triangular degree bound, the exact complete-background cross term, SOS-certified finite APPT states, the fixed-m interval/projection identities, and uniform parameter comparisons. Deliberate failures show that ordering and the cross term cannot be dropped. These programs passed normally and with assertions disabled on the authorized VPS; no independent CI or Lean run is claimed.

A final primary-source search retrieved Tran's arXiv:2609.18568 abstract and the older arXiv:2510.19508 problem description. Their general spectral-purity context is acknowledged; the new proof is self-contained apart from standard spectral/Schmidt decomposition and compactness facts. The search is not an exhaustive historical-priority certification.

Remaining substantive optimization targets: exact finite-dimensional maxima, higher-order terms, rigidity or classification of extremizers, effective quantitative convergence of the hierarchy, and the absolute-separability status of the new states. The leading APPT excess-purity asymptotic is now closed in the stated uniform sense. Work remained on mathematical notes and exact checks; no new preprint or Release was made.


## Exact rectangular theorem: current continuation

Started from live main 757f9b12 after inspecting current proofs, indexes and actual instructions. A separate worktree was used. The new target is exact finite-dimensional optimization, not publication or additional numerical examples.

The full Schmidt-rank-m necessary inequality defines an outer polytope whose entire vertex set is optimized analytically in EXACT_RECTANGULAR.md. The exact outer maximum is the larger of a spurious single-spike value and the full-support two-level plateau value. The plateau wins strictly exactly when n>=m^3-m-2, including integer-rounding parity. In that range its physical APPT attainment closes the unrestricted maximum and all maximizing spectra. The cutoff is exact for this single-test method, not claimed minimal for APPT; the existing qutrit result has a smaller cutoff.

This finite-dimensional argument is independent of the multiscale compactness lower bound. Exact ancillary checks enumerate 101,956 vertices in 70 sample dimension pairs, verify seven symbolic identities and 1,184 cutoff comparisons, and check six rational physical boundary orbits. Normal and assertion-disabled outputs match. These finite checks do not replace the analytic proof, and no Lean or independent CI verification is claimed.

Primary abstract retrieval confirmed Ahiable--Kothakonda--Winter v2 and Tran v1. The known candidate spectrum is credited; no exhaustive priority certification or first prediction of that value is claimed. No preprint or Release was prepared.


## Universal near-maximizer structure and the critical obstruction

Retaining four separate nonnegative defects in the unrestricted upper proof gives paired-gap energy limits for every near-maximizer, not just explicit candidates. A weighted refinement of the decreasing triangular row inequality forces the residual energy below every positive fraction of m^2 and its first moment to be o(m). Clipping actual eigenvalues to the final paired interval converts these identities into W1 laws for m(mn*lambda-1). The empirical second moments are larger than the moments of the limiting measures; the proof explicitly retains the escaping outlier contribution.

At aspect ratio four the scalar defect bound alone falsely permits intermediate bulk amplitudes. Applying Cauchy--Schwarz to the PSD form 2I-(G+wA_complete), with vectors e and Ge, supplies a further matrix inequality. It excludes every normalized background limit strictly between zero and two. Thus the only critical empirical limits are a point at zero and the symmetric two-point law; both are attained by actual near-maximizers. This is structural rigidity, not an inferred visual pattern.

## Exact finite-hierarchy optimization

The amplitude-limit forest argument was sharpened by proving that a component has at most one loop; if that loop has label j, all off-diagonal labels in the component precede j. Its exact extremal norm is a star-with-one-loop value involving the preceding energy sum. Nested flags realizing the matching lower graph are constructed with the earlier rank subtracted from the new clique budget. That detail is necessary for translating a graph obstruction back to one global unitary on nested spectral projectors.

The resulting exact prefix constraints are E_{j-1}+2 sqrt(2 e_j)<=4. Their complete optimization gives e_j=d_{j-1}^2/8 with d_j=d_{j-1}-d_{j-1}^2/8, and sharp coefficient 8-d_J. The first coefficients are 6,13/2,217/32. This proves a depth deficit asymptotic to 8/J and unique energy allocation within the explicitly lacunary intermediate-rank model, not a level-count theorem for every APPT state. A positive safety margin is still fixed before the dimension limit.

Exact supporting tests include rational PSD graph matrices, all four defects and clipping identities, one-loop component restrictions, optimal rational arrowhead kernels, alternative feasible energy allocations, and large-integer nested graph counts. These checks passed normally and with assertions disabled. They do not certify the compactness theorem, and no independent CI, Lean proof, external peer review, preprint, or Release is claimed for this research cycle.


## Two-ended hierarchies and flat reflected near-maximizers

Started from live main 8803903a after reading the current indexes, exact rectangular result, phase rigidity, and fixed-hierarchy graph theorem. No applicable AGENTS.md was found. A separate worktree is used and no preprint or Release is prepared.

The first question was whether the paired-gap energy four in the first m-1 slots forces an order-one eigenvalue spike. It does not. A second hierarchy with ranks m^alpha, 0<alpha<1/2, has its amplitude interactions at the opposite end of the exponent interval from the existing ranks m^(2-delta). The low hierarchy has reverse (suffix) energy constraints. A shared amplitude-measure argument gives an exact combined graph norm, including the non-independent coupling of the broad complete-graph background to the high-rank hierarchy. Nested lower graphs are constructed, so quantum necessity does not rely on incompatible flags.

The resulting families approach the unrestricted maximum excess purity while every normalized eigenvalue D lambda_i tends to one, uniformly in n>=m as m grows. Centering their positive projection sum also gives reflected states about I/D with exactly equal purity, both APPT. This reflection is NOT valid for an arbitrary APPT state: a rank-one-spike APPT state gives an immediate negative eigenvalue after reflection. The new finite positivity lemma explicitly controls the positive diagonal Schmidt-witness terms and requires a small coefficient sum compared with the fixed graph margin.

The full finite-depth objective is derived analytically. Exact checks cover low/high loop components, reversed energy constraints, background coupling, rational reflection states and partial transposes, integer nested graph sizes, moment formulas and an exact rational enclosure for the entropy difference. They are supporting checks, not a finite proof of the graph limit. No Lean, independent CI, or external review is claimed.

The flat and original spike constructions attain the same leading purity but different von Neumann entropy deficits. This comparison motivates the next target: the unrestricted minimum-entropy law rather than treating the Taylor expansion in the flat subclass as a global upper bound.
