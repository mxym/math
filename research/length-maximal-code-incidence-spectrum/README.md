# An incidence-spectrum obstruction for length-maximal codes

Alderson's [2026 paper](https://arxiv.org/abs/2604.03784v2) asks whether the divisibility condition for length-maximal codes of dimension at least three can be strengthened. The answer is **yes**, whether or not the code is linear: for every integer alphabet size \(q\ge2\), if \(s\le q-2\), then \(s+2\mid q\). In particular, the highlighted \((13,125,10)_5\) code does not exist.

The same obstruction answers the full-weight subquestion in dimension four: at \(s=q-1\), a length-maximal code of size \(q^4\) exists **only for \(q=2\)**, where the extended binary Hamming code realizes it. In particular it excludes the \((22,256,16)_4\) candidate and the higher alphabet sizes in the paper's Table 3.

The key is that a \(0/1\) symbol-incidence matrix has low rank, while its Gram matrix is an integer distance matrix plus a scalar diagonal. A rational eigenvalue forced by a kernel must be integral.

[Proof](PROOF.md) · [Sources and scope](SOURCES.md) · [Reproducible checks](RESULTS.txt)

These are necessary conditions and a complete answer to the stated full-weight subcase, not a classification of all length-maximal codes. The MDS cases and the broader existence question for nonlinear codes are not settled here.

Replay: run <code>sh replay.sh | diff -u RESULTS.txt -</code> with Python 3 and a POSIX shell.
