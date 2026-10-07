# Classical inputs and public provenance

The complete proof is included in manuscript.tex. No unpublished research note or many-particle H1–H6 package is a mathematical dependency. The dynamical inputs concern isolated systems of at most three spheres.

## Mathematical inputs

1. Almost-everywhere finite-particle elastic flow, phase-volume preservation, collision-free pieces and the standard invariant singular set. [Deng–Hani–Ma, arXiv:2408.07818v3](https://arxiv.org/abs/2408.07818v3), Proposition 1.2, printed page 4, supplies the finite-particle input. [Versioned PDF](https://arxiv.org/pdf/2408.07818v3). No Boltzmann derivation, fluctuation theorem, rate or many-particle history estimate from that work is imported. The collision-tube Jacobian and transfer from bulk nullity to incoming-flux nullity are explained in the supplement.
2. Finite total collision count on a nonsingular isolated trajectory. [Burdzy, arXiv:2107.10362v2](https://arxiv.org/abs/2107.10362v2), Theorem 1.1 and Section 3 assumptions, provides a stronger uniform bound for equal masses and radii. [Versioned PDF](https://arxiv.org/pdf/2107.10362v2). Its radius convention is scaled to diameter one. Only eventual exactly free incoming asymptotes are used; no uniform bound on the last collision time or offsets is presumed.

The finite coefficient extraction, quadratic TV expansion, signed connected cancellation, two-encounter tail and cubic mean deduction are proved in the supplement. The build and finite checker do not fetch these sources or access the network.

## Context only

- [van Beijeren–Ernst, Kinetic Theory of Hard Spheres](https://www.phys.uu.nl/~vanbeije/pub/KinThHS.pdf), Journal of Statistical Physics 21 (1979), 125–167
- [Pulvirenti–Simonella, arXiv:1405.4676v2](https://arxiv.org/abs/1405.4676v2)

These are background and scope comparisons, not additional hypotheses. No comprehensive priority assessment or novelty certification is claimed.

## Exact independent review

The unchanged [final sign-off](audits/exact-source-signoff.txt) records review of the entire source with SHA-256 757d0ba430e52cfcfd98c5e78afe59150970e7897e99516efdb92adc42d1ab21, including the theorem statements, proofs, dependency boundary and bibliography. The reviewer independently reconstructed that exact source and rebuilt its ten-page PDF.

The public source updates only the three status locations approved by that certificate. EDITORIAL_CHANGES.md, editorial-status-changes.json and REVIEW_PROVENANCE.json identify the old and new hashes. Running verify_review.py reverses those substitutions in memory and verifies the reviewed source hash and certificate bytes. The certificate is review evidence, not a theorem assumption or external peer review. Gaussian-data and matched-layer projects remain outside its scope.
