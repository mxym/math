# Exact indistinguishability of Haar transcripts at the birthday scale

Compare classical transcripts from independent Haar pure states with transcripts from copies of one Haar pure state. Each measurement sees one copy, may use arbitrary fresh ancillas and earlier classical results, and keeps no quantum state between rounds.

For dimension d and t rounds, write `alpha = product_{j=0}^{t-1}(1+j/d)`. If `alpha-1 <= 1/64` (in particular, if `d >= 64 t^2`), the exact largest transcript total variation is

    (1 - 1/alpha) product_{j=0}^{t-1}(1-j/d).

This value is achieved by measuring every copy in one fixed orthonormal basis. The proof gives an exact conditional deficit bound, rather than just a bound on the order of the testing bias.

We also give the exact value at three rounds for **each** finite dimension. The fixed same-basis procedure remains optimal for d=2 and d>=6, but classical feed-forward strictly improves on it for d=3,4,5. The comparison in those dimensions is with the same-basis procedure, not with every nonadaptive POVM.

The negligible-distance statement in [AICR c/0104](https://aicr.info/c/0104/) already follows from published adaptive single-copy purity-testing bounds. The increments here are the exact finite optima in the stated regimes. We study the two abstract Haar/mixed-state transcript laws only, not general purity testing, multi-copy measurements or an implemented cryptographic system. See [PROOF.md](PROOF.md), [SOURCES.md](SOURCES.md), and the two checkers via `./replay.sh`.
