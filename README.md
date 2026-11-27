# Quantum Latin square cardinalities in orders 9, 11, and 23

Explicit constructions filling gaps in Yuyuan Zhang, Mingzhen Lv, and Haitao Cao, [On the possible cardinalities of quantum Latin squares](https://arxiv.org/html/2607.19969v2), Table 6. Cardinality counts distinct rays, modulo complex phase.

- [Order 9](order-9/README.md): thirteen new attainable cardinalities close all the remaining gaps. Together with prior results, the exact spectrum is 9 through 81 except 10.
- [Order 11](order-11/README.md): five formerly uncertain cardinalities are realized (66, 106, 113, 115, 119). A fixed Björck-Hadamard/row-permutation family is classified exactly; the unrestricted order-11 problem remains open.
- [Order 23](order-23/README.md): an explicit cardinality-528 square closes the last gap. With prior results the exact spectrum is 23 through 529 except 24.

Run each folder's `sh replay.sh` as documented. The order-9 replay uses the separately published Lampio–Östergård–Szöllősi Aalto catalog `BH-9-6.txt` (not redistributed here), and checks its SHA-256 before using it; an offline copy can be supplied by path. Order 11 includes two independent orbit enumerations. Source revisions:
- order-9: `53ff806bce2c701378308fed1e74842cb0d937f7`
- order-11: `de787deb28c09fd31941b83e9a47a64e543c68a8`
- order-23: `69a002a9a06523153067aa93d2f336f4867527b2`

Run `sha256sum -c SHA256SUMS` for archive integrity. Previously published results that complete the spectra are credited in the papers' source notes.
