# Independent audit of manuscript 008 v1

Date: 2026-10-07. Source snapshot: `9af06fa4cadaa80e176ed633a7176ed7f2e813db`.
Source Git blob: `3b2882cef1a65e890549332c5c9014af9dc5f245`.
Source SHA-256: `24e32066518d97d700cdaed139717726ab6560e0362f4d93b7f0e8243232a013`.

## Verdict and scope

No substantive mathematical error found in the full 11-page source. The overlap interpolation, global density-root criterion, Fisher-information threshold, and explicit boundary-family phase diagram have complete written arguments within the stated imported potential-stability hypothesis. This is an independent mathematical reading and finite replay, not formal verification, external peer review, novelty certification, or a fresh PDF rebuild.

## Independently reconstructed decisive steps

1. At each point, min(r(x-h),r(x))-min(r(x),r(x+h)) equals r(x)(L_+(x)-L_-(x)). Both translated signed-square terms have weights bounded by r after substitution. Thus their integrability follows from the gradient second moment; no uncontrolled translation ratio is used. The factor 14 follows from 3 times the two individual factor-4 errors and the factor-2 missing-weight term.
2. The root inequality uses a(1-b/a)^s <= s^s(a^(1/s)-b^(1/s))^s only for a>=b. Its Lebesgue integral controls the density-weighted losses. The zero extension matters: an interior score integral would not see a boundary jump.
3. Finite Fisher information implies every root order 1<s<=2 by the truncated power chain rule and Holder. For 2<p<4, choosing 1<beta<2/(p-2) gives a globally finite-Fisher source whose rare-cell power is strictly below one third. The stated threshold is therefore sharp for this universal sufficient-condition assertion.
4. Near the longitudinal boundary, the root derivative has s-th power proportional to x^(beta-s). Its integral gives precisely the three power/logarithmic/Sobolev regimes. The transverse bump has no finite-order or jump obstruction. The first root's beta=0 exception is correctly treated as a trace jump.
5. The subcritical two-atom example has exactly unit pth moments. Equal rare masses make target cost exactly m R^2 times the squared directional displacement; the cost decreases as the matched rare mass increases. The map's symmetric difference has a positive asymptotic proportion of m. The explicit parameter choice proves a lower bound at every small upper distance w.
6. The interior example uses symmetry only of the transverse marginal. The unbounded longitudinal marginal has finite first moment, which dominates the clipped-strip limits. Both exterior masses are unchanged. The same-label coupling is only an upper bound, and that is sufficient.
7. In the critical multiscale construction, two separate inverse-CDF equations preserve both exterior cumulative masses, not just the central mass. Symmetry cancels the first-order shift; the inverse corrections are uniformly O(h^2/t_n). For h<=epsilon t_K, all strips remain disjoint, positive and overlapping their respective partners. The symmetric-difference leading term dominates the uniform correction after epsilon is fixed sufficiently small.
8. The broken-line potentials have the same ordered slopes. Each inserted supporting plane dominates exactly on its own strip and cannot interfere with another strip. Thus the construction is a pair of global convex functions, rather than an unverified patched vector field. On mismatches the horizontal gradient difference is R_n; the vertical term is present exactly on the perturbed central cell. This proves the stated exact map-cost identity.
9. Geometric summation bounds all local slopes by C min(x^(-beta/2),t_K^(-beta/2)). The critical identity beta p/2=beta+1 gives a logarithmic moment integral O(K+1), including a uniformly bounded capped tail. Scaling by (C_0(K+1))^(-1/p) normalizes both targets. Consequently map size is at least c K^(1/(2s)) h^(1/2), while target distance is at most C K^(1/(2s)) h^(3/2).
10. K=floor((1/4)log_2(1/w)) and h=(w/(C K^(1/(2s))))^(2/3) satisfy h/t_K -> 0 and yield the exact critical logarithmic power 1/(3s) for every sufficiently small w. No claim of an optimal coupling or a fixed number of atoms is needed.

## Dependency and overlap

Transport upper bounds use the explicitly pinned all-P2 centered-potential theorem in 001 v3; the standalone interpolation and lower bounds do not. This audit does not silently replace that theorem with an assumption of density regularity alone.

The minimum-density/root-density/Fisher mechanism overlaps the parallel 001 v5 assembly. It should be cross-cited and counted once. Manuscript 008 adds a substantially stronger source-specific boundary classification and the multiscale critical logarithm. The 001 v5 Sobolev little-o statements and smooth full-support stretched-exponential obstructions are different assertions; its Gaussian logarithmic-moment result already appeared in 001 v4. No priority assertion is made between parallel drafts.

## Finite verification actually performed

The inspected standard-library checker was replayed with 160 cases and up to 8 scales: 3840 exact root/loss inequalities, 1920 signed-square identities, 640 interpolation inequalities, and 8 full affine-max constructions with 3 through 17 atoms per target and 968 pairwise cells. All passed. A second run under Python -O used 20 cases and up to 4 scales and passed. This is replay of the published verifier, not a newly independent implementation. The rational auxiliary density differs explicitly from the smooth theorem density; its finite checks are not a substitute for the analytic limit proof.

Replay outputs: [normal](../verification/2026-10-07-008-independent-replay/replay.json) and [optimized](../verification/2026-10-07-008-independent-replay/replay_optimized.json). The source and checker are the pinned original files under preprints/008-density-overlap-phase/v1; they are not overwritten.
