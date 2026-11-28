# Exact randomness support for cycle multi-secret sharing

For every simple cycle \(C_n\) of length \(n\ge4\) and every nonempty
allowed binary secret domain \(D\subseteq\{0,1\}^n\), the minimum dealer
randomness support is exactly one of \(1,2,3,4\). Use the first applicable
line:

| States | Condition |
|---|---|
| 1 | Every active vertex touches an edge on which endpoint XOR is constant on \(D\). |
| 2 | Some edge has constant endpoint XOR, or the XOR of all \(n\) bits is constant on \(D\). |
| 3 | Some signed sum \(\sum_i\epsilon_i x_i\) with all \(\epsilon_i\in\{-1,1\}\) is constant modulo 3 on \(D\). |
| 4 | Otherwise. |

An active vertex is one whose secret takes both values on \(D\).
The two-state bound follows from the known one-bit cycle criterion.
The new steps are the exact three-state criterion despite allowing
unequal source probabilities, and a universal scheme with two uniform
random bits, one- or two-bit edge labels and perfect privacy.

The result treats the cycle case of the larger-graph direction in
Marszalik, *The Price of Privacy*, arXiv:2610.10002v1 §V. The cost is
support size, not Shannon entropy, and the protected view belongs to
one vertex at a time. It is not a statement for arbitrary graphs,
coalitions, or approximate privacy.

Run **bash replay.sh** with Python 3 and sha256sum. The proof is analytic;
the checkers exhaust small local distributions and verify finite instances
of the constructions independently.
