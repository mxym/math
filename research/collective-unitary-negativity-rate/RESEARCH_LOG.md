# Research continuation and literature boundary

## Starting point

The current repository was checked at f4b377aa before starting this separate worktree. The qutrit proof Release and the manuscript Release/Zenodo preprint are already published. They were not recreated or modified. The all-dimension APPT two-level reductions and the flat-spectral volume theorem are also present in current main and were read before selecting a new target.

The unrestricted higher-dimensional APPT purity conjecture still has a multilevel-spectrum gap. Its recent search logs report repeated unsuccessful numerical attempts. Compatible spin alignment was also already screened without a structural result. Repeating those searches was not selected. The present approach instead asks for a complete regularized spectral entanglement law and supplies matching bounds rather than another finite numerical instance.

## Chosen problem

Determine the asymptotic maximum logarithmic negativity obtainable from k copies of an arbitrary bipartite state under unrestricted global unitaries on the unchanged A^k:B^k space. This is a many-copy version of the negativity-from-spectrum problem, not a relabeling of the finite-copy APPT purity conjecture.

The main new argument in this directory is a one-shot lower bound from a random subset of a blockwise Bell basis. Its projection rank is allowed to exceed the requested spectral-prefix rank. The exact variance identity makes matrix Bernstein effective in all aspect ratios. A type-distribution argument then matches the full Renyi interval of upper bounds. Both the balanced collision-entropy formula and the unequal-dimension interior regime follow.

## Sources inspected and claims not made

1. J. Abellanet-Vidal, G. Müller-Rigat, A. Rico and A. Sanpera, arXiv:2604.02420. The unversioned abstract was checked and showed v2, revised 9 July 2026; v2 was then inspected. It treats sufficient finite-spectrum negativity/Schmidt-number bounds and reports limitations for general/rank-deficient spectra. The present theorem concerns the regularized orbit maximum. No claim to have closed their entire one-copy characterization is made.
2. T. V. Kondra et al., arXiv:2605.29197v1. Supplemental Lemma 6 already proves finite-copy activation of nonmaximally-mixed full-rank AS states. The qualitative fact is not credited to this work. The rate formula here is a different statement and uses no assumed AS/APPT characterization.
3. J. A. Tropp, arXiv:1004.4389v7, Theorem 1.4; published in Foundations of Computational Mathematics 12 (2012), 389–434. The self-adjoint Bernstein bound is an explicit external theorem. It is not re-proved by the checker.
4. G. Vidal and R. F. Werner, arXiv:quant-ph/0102117; Physical Review A 65, 032314 (2002), for negativity and its entanglement interpretation. The result is about logarithmic negativity, not an achievable LOCC distillation rate.

Searches combined collective/tensor-power/global-unitary/regularized negativity and spectral Renyi entropy terms. They did not identify the exact formula proved here, but this is not an exhaustive priority certification. Random-state negativity asymptotics and entanglement-concentration results under other operation classes are not equated with the present all-spectrum global-unitary theorem.

## Independent checks and review obligations

The quantum argument is dimension uniform and analytic. The checker separately verifies exact small cyclotomic Bell matrices and deliberately rejects malformed controls. Entropy optimization has an exact escort proof; numerical values are not its premise. The two awkward boundaries were handled explicitly: b need not be divisible by a, and zero eigenvalues are retained by working on the positive support.

No Lean verification or external peer review is asserted. The principal places for independent mathematical review are the trace-norm dual projection lower bound, the use of matrix Bernstein with dimension N0, and the type-to-prefix comparison. None is left as an assumed bridge in PROOF.md.

## Reassessment

This direction was retained because it produced a complete matching-exponent argument, not merely favorable simulations. The neighboring finite-copy maximum and efficient implementation questions remain separate. Further work should test or strengthen those questions only with a new structural mechanism, rather than count random restarts as progress.
