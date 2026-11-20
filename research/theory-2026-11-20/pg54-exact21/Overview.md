# PG(5,4): exact maximum and two extremal classes

The largest 4-general set has **21 points**. Exactly **two** projective collineation classes attain the bound. Equivalently, the optimal distance of a quaternary linear `[22,16]` code is **4**, not 5. These answer both questions in [Lu, Yang, Fu and Song, §8](https://arxiv.org/html/2610.03272v1#S8). The unrestricted binary dimension-12 Sidon problem is separate.

[Proof PDF](proof.pdf) · [Proof source](proof.tex) · [Complete source and replay ZIP](PG54_exact21_two_orbits_v1.zip)

ZIP SHA-256: `ef31b9a23cdf8ec8409ae218d57f879b2b72acc60c2a27abd0eb377a9cf46ce4`.

The two searches are exhaustive and have no solver or time cutoff. Run `bash replay/replay.sh` with GNU C++17 and Python 3; see [the expected result](EXPECTED.txt) and the [frozen package notes](README.md). [The representative point sets](replay/extrema21.txt) are separated by their counts of nine-point hyperplanes (63 for Pavese's set and 72 for the other). A disjoint 21-set mentioned in Lu et al.'s positive control is not claimed there to be in a distinct orbit. The 2002 constacyclic example in Grassl's table has the same hyperplane spectrum as Pavese's set. No global priority claim is made.

[One-kernel linear replacement](single-kernel/README.md) extends the 21-line upper bound to binary two-dimensional blocks whose images under quotienting by one included block lie in a common quaternary spread. The replacement lemma preserves all originally direct subfamilies over any finite-degree field extension; it does not prove code equivalence or an unrestricted Sidon bound.
