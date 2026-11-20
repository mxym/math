# The Watrous two-qubit basis requires three copies for exact collective LOCC discrimination

Read **watrous.pdf** (4 pages) for the proof; **watrous.tex** is the complete LaTeX source. **check.py** optionally replays the exact polynomial calculations using Python 3 with SymPy: run `python -O check.py`. The proof does not assume a numerical solver or search over detector families.

## Result and scope

For the orthonormal two-qubit basis in [Bandyopadhyay, arXiv:2610.16138v2](https://arxiv.org/html/2610.16138v2), two same-label copies are insufficient for perfect discrimination by local operations with classical communication, even allowing joint actions on both qubits inside each laboratory. Three copies suffice. The comparison with the two copies sufficient for collective separable measurements relies on Bandyopadhyay's existing construction. The last proposition includes a single consistent countably infinite LOCC transcript with a measurable exact decision. No claim is made about positive minimum error in the topological closure of LOCC.

[Download the manuscript, source and exact replay](Watrous_Three_Copies_Exact_LOCC.zip), SHA-256 `5b903dc2d76fdef9707ba83042a0a472f4c994185c06d367451f1c49605fa019`. This resolves [the exact collective LOCC question in Section 7 of Bandyopadhyay's preprint](https://arxiv.org/html/2610.16138v2) for the Watrous basis, not just a bounded number of local turns. The proof distinguishes a single infinite transcript with an exact decision from a sequence of unrelated approximate protocols; it does not rule out the latter.
