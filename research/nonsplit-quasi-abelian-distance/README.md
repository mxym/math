# Quasi-abelian distance supplement: nonsplit and bounded-exponent groups

The [archived split-elementary theorem](https://github.com/mxym/math/blob/b9ca8e3573888ffc25cae820bf0545f6efcb1dda/research/split-quasi-abelian-distance-collapse/PROOF.md) already proves deterministic vanishing relative distance, including O(1/m) over F_q[(Z/2)^m] for odd q, and resolves the principal coding assertion of AICR c/0105. Its Fourier-cube method is not a new claim here.

This supplement extends it to arbitrary coprime bounded group exponent, including nonsplit character fields and q=2, for all quasi-abelian modules of fixed index and positive rate. The new steps are taking a cube inside a coset of an elementary torsion subgroup and descending a codeword by trace. A separate result gives an explicit independent-band probability bound for uniform systematic codes through any coprime elementary abelian quotient. In particular, it gives relative distance O(1/m) with high probability for the nonsplit binary-coefficient, ternary-group example. Here m is the elementary rank, not the block length.

These are coefficient-Hamming statements only. They do not analyze syndrome decoding, deployed parameters, or the security of any protocol. The concrete large-field bounds in the source papers are not contradicted.

Run: sh replay.sh | diff -u RESULTS.txt -
