# Octary scalar representations for binary three-fold matroids with a long line

A rank-three matroid with a three-fold linear representation over the binary field has a scalar representation over **F₈** if its simplification has a line with at least five points. Rank at most two also has no obstruction. As a consequence, every dealer port of such a matroid has an ideal F₈-linear secret-sharing scheme, preserving the whole matroid rather than only one dealer's qualified sets.

The proof combines a known partial-spread dichotomy with an affine extension argument. In the non-Desarguesian five-point case, any noncollinear outside triangle leaves just seven possibilities for extra affine points. Three compatible pairs and one isolated point account for all extensions, and explicit scalar coordinates realize them. The theorem is proved algebraically; the finite checkers independently verify the local configurations.

This is a restricted positive result for the eight-symbol question in Beimel–Ben-Efraim–Farràs–Moya, ePrint 2026/1794 §1.4. It does **not** classify all eight-symbol schemes, all rank-three matroids without a five-point line, or higher-rank binary three-fold representations. Any remaining simple rank-three counterexample within the binary three-fold class has at most 28 points.

See [PROOF.md](PROOF.md) and [SOURCES.md](SOURCES.md). Reproduce with `bash replay.sh`.
