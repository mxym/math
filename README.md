# One-sided completion for punctured ADE root equators

For every finite reduced simply-laced crystallographic root system, and every subset of its signed roots, the proof classifies when any feasible same-hemisphere pair remains compatible after adjoining antipodes. There is no bound on the number of deletions, and reducible root systems are included. The theorem classifies a local geometric operation, not an unrestricted kissing number.

- [Main ADE classification](KissingADEProjectivizationClassification.md) and [elementary D-type argument](KissingDnProjectivizationObstructions.md).
- Run `python3 verify-kissing-ade-projectivization.py` and `python3 verify-kissing-dn-projectivization-obstructions.py` for exact standard-library replays.
- Run `python3 kissing_ade_independent_exact_audit.py` for a separate full Weyl-orbit replay (Python 3.9+ and Node.js 18+, no packages). Add `--quick` to keep exact chamber reconstruction and the E6 and E7 full orbits but skip the E8 full-orbit pass.
- Run `sha256sum -c SHA256SUMS` to verify archive bytes.

The earlier D-type result is included as a dependency and not counted twice. The related earlier geometry notes referenced by the proof are included for context. Root-polytope structure for intact systems is classical; see [Cellini–Marietti](https://doi.org/10.1093/imrn/rnu070). The seven-dimensional conditional consequence about retaining 68 of 72 E6 roots still requires the stated assumptions and is not claimed sharp or universal.

Research source: [c050df3](https://github.com/mxym/math/commit/c050df3521c4658fe258f72a8c2ca330a02b74d8).
