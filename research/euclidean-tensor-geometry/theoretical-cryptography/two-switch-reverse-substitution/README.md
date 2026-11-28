# Sharp reverse substitution for two-switch pair regions

Khazaei's [ePrint 2026/2652](https://eprint.iacr.org/2026/2652) proves a universal single-substitution factor 1/2 and gives one construction with factor 8/9. Here the worst factor is exactly **8/9** when both access structures have at most four participants, with a non-dummy replaced participant and a nonempty inner access structure. The same lower bound applies to any size under an explicit pair-region hypothesis; some orientations give **exact reversal**.

The proof gives a closed formula for the factor on these convec regions. Its main step is a pair of Shannon-inequality telescopes on a two-level chain of authorization changes. No search or finite enumeration is needed for the theorem. The sharp example is Khazaei's, not a new construction. This does not settle the universal minimum reverse factor or the recursive Csirmaz question in his §9.

See [PROOF.md](PROOF.md) for the exact hypotheses and [SOURCES.md](SOURCES.md) for attribution. Run `bash replay.sh` to verify the certificates, small-family witness patterns, and linear counting examples. The checks are independent of numerical linear programming.
