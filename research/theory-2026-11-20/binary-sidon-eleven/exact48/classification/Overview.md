# Eleven-dimensional 48-point Sidon sets: one affine class

**Theorem.** Every 48-point Sidon subset of the binary vector space of dimension eleven is affinely equivalent to the known Chen construction. The size result [in the preceding paper](../README.md) gave maximum 48; it did not classify the extremizers.

- There are exactly **three** binary linear `[47,36,5]` codes up to coordinate permutation, obtained by selecting a point from one of the three point orbits of the unique extremizer. There is exactly **one** binary linear `[48,36,6]` code. Its 6,768 minimum supports form a `2-(48,6,90)` design whose permutation group has order 80. This does not classify arbitrary designs with those parameters.
- Every six-variable APN function of **maximum linearity 32** belongs to the single CCZ class `D7`. This is not a classification of all six-variable APN functions.
- The unrestricted dimension-twelve Sidon interval is now **66–81**. The upper bound follows from the unique extension of a 48-point section and five exact signed Fourier-moment certificates excluding the remaining size-82 shape. The exact maximum remains open. In particular the optimal binary `[81,69]` minimum distance is **4**, closing the 4–5 gap in [Grassl’s table](https://www.codetables.de/BKLC/BKLC.php?q=2&n=81&k=69): a distance-at-least-five code would give a size-82 Sidon set by adjoining zero to its parity-check columns, and distance four is achievable.

[Complete expansion and finite proof](README.md) · [Frozen replay archive](Sidon_extremizers_11D_48_v1.zip)

SHA-256: `54cc84b038f8336c78a781e1b5a47ac736477036574f712656e76a939ec43474`.

The two independent exact search engines each cover 4,100 largest-half-30 anchor keys and 6,646 largest-half-31 anchor keys with no surviving 48-point set. The separate high-anchor search covers 208 anchors and verifies explicit maps for all 186 completions. The archive contains raw per-anchor stops, matching counts, source and checksums. After extraction, use `python3 -O run.py structural ledgers high derived corollaries --jobs=2` for a quick end-to-end check of the recorded data and corollaries, or `python3 -O run.py 30 31 --jobs=4` to rerun the complete low-anchor searches. The latter is not the ledger-only check.
