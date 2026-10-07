# Density overlap and a sharp boundary phase diagram for moment-controlled Brenier stability


**Supplement, 7 October 2026:** [Critical boundary stability with slowly varying factors](../../notes/critical-boundary-slow-variation/manuscript.pdf), [source](../../notes/critical-boundary-slow-variation/manuscript.tex), and [scope/build record](../../notes/critical-boundary-slow-variation/README.txt). This extends the critical construction to an implicit exact modulus, including a necessary log-log correction. The v1 paper below is preserved unchanged.

**Version 1, 2026-10-07.** Complete written research proof, prepared with AI assistance. Not independently peer reviewed or proof-assistant formalized.

[11-page PDF](v1/paper.pdf) · [Complete source](v1/main.tex) · [Proof audit](v1/PROOF_AUDIT.md) · [Exact finite checks](v1/verification/check_exact.py) · [Versioned release](https://github.com/mxym/math/releases/tag/density-overlap-20261007-v1)

## Main result: the critical regime is resolved

For the explicit fixed strongly log-concave source family with first marginal proportional to `x^beta exp(-x^2/2)` on x>0 and smooth infinitely vanishing transverse marginals, the optimal uniform transport-map modulus on bounded pth-moment target classes is determined for every beta>=0 and p>2 in every dimension d>=2.

- Below `beta=2/(p-2)`: the exact power is `(beta+1)(p-2)/(2p+(beta+1)(p-2))`.
- Above it: the exact power is one third.
- At equality: the exact modulus is `w^(1/3) (1+log(1/w))^((p-2)/(3p))`. The logarithm is necessary, and its exponent cannot be reduced.

These are two-sided bounds for every sufficiently small w. The critical lower bound simultaneously matches all central AND outer cell masses in a multiscale family of actual global convex potentials. The number of target atoms grows; fixed-cardinality critical sharpness is not asserted. The theorem classifies this source family, not all log-concave sources.

## General method and finite Fisher information

A new bounded density-overlap loss replaces the untruncated density-translation ratio in the previous interpolation argument. The standalone convex-gradient interpolation theorem requires no log-concavity or positive density. Sobolev regularity of the appropriate density root gives one-third transport stability under the stated source potential estimate.

Finite Fisher information, defined globally by sqrt(r) in W^(1,2), suffices for bounded fourth moments and every higher moment order. The threshold four is sharp for an assertion covering all strongly log-concave sources with finite Fisher information. A classical score integral confined to the interior is not enough when the density jumps at its support boundary.

## Dependencies and reproducibility

The transport upper bounds use manuscript 001 v3's all-P2 centered-potential estimate, pinned at `5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3`, source blob `0007edf5e28e4b4b0d34b2043cffd6e13e9f5aed`. Lower bounds and the independent interpolation theorem do not use that estimate. The signed-square/minimum-weight and earlier rare-cell mechanisms are credited to 001 v3 and 007 v2. The release bundle includes the pinned dependency source, bibliography, and PDF, together with provenance and upstream license notices.

From `v1/`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
cp main.pdf paper.pdf
python3 verification/check_exact.py --cases 80 --max-scales 6 --output verification/exact_checks.json
python3 -O verification/check_exact.py --cases 10 --max-scales 3 --output verification/optimized_checks.json
```

Local checks passed 1920 density-loss/root inequalities, 960 signed-square identities, 320 interpolation inequalities, and six complete rational multiscale constructions with 3 through 13 atoms per target, including 454 pairwise cell intersections. The finite construction uses an explicitly distinguished rational auxiliary density, not the smooth theorem density. It verifies exact mass matching and map/coupling identities; it does not certify an analytic infinite-limit argument. The repository workflow replays the checks and builds the publication artifacts.

The uploaded source and verifier match the locally tested Git blobs `3b2882cef1a65e890549332c5c9014af9dc5f245` and `dd5fb49fd2035e2b23641e294b7c1ecf1c1ecd53`. All historical manuscripts are preserved. No novelty certification, journal-tier claim, or additional license for new material is implied.
