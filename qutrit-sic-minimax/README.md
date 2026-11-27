# Qutrit SICs do not minimize maximal intrinsic randomness

Every qutrit symmetric informationally complete measurement
has maximal intrinsic min-entropy \(\log_2 6\) when optimized
over the input state. We give an explicit, unbiased nine-outcome
rank-one MIC whose maximum is **strictly smaller**. The
separation holds over all pure and mixed inputs in the
specified intrinsic-randomness model, not just tested states.

This answers negatively the higher-dimensional question in
§7 of [Curran, arXiv:2605.18291v1](https://arxiv.org/html/2605.18291v1).
It does not contradict Curran's qubit result or assert an
optimum among qutrit MICs. The physical setup and unrelated
optimality criteria for SICs are outside the claim.

The argument compares the largest squared overlap between a
unit input and the nine measurement vectors. A simple SIC
moment identity gives the reference value \(1/2\). An exact
three-vector determinant separation localizes all inputs close
to the reference minimum. A small explicit perturbation then
strictly raises the overlap in those neighborhoods without
losing the gap elsewhere.

[Proof](PROOF.md) · [Sources and scope](SOURCES.md) ·
[Verification output](RESULTS.txt)

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~

The first checker uses exact Eisenstein integers and rational
inequalities. The second independently assembles the effects,
checks their exact rank and Gram entries, and computes direct
55-digit Born overlaps as finite checks. The complete proof
does not depend on sampling.
