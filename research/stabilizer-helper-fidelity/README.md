# Exact classical assistance for blind stabilizer helper codes

Take a prime-\(p\) stabilizer code encoding \(m\) qudits, with a
helper \(A\), a target \(B\) holding exactly \(m\) physical qudits,
and an unavailable region \(C\). Suppose the three individual
erasures \(A,B,C\) are correctable. This includes a blind helper
scheme and a single target of the same dimension as the secret,
with at least one other shareholder. The helper can measure
arbitrarily, but may send only a classical message to \(B\).

There is a uniquely determined invertible map \(b\) from logical
Pauli labels to the \(B\)-part of representatives cleaned off \(C\).
Let \(2r\) be the rank of the difference between the symplectic form
induced by \(b\) and the logical symplectic form. For a message alphabet
of size at most \(L\), the exact best entanglement fidelity is
\[
            F_e^{(L)}=\min\{p^{-r},\,L/p^{2m}\}.
\]
The result holds against arbitrary helper POVMs and target recovery
channels; commuting Pauli measurements and local Clifford corrections
attain it. In particular, perfect one-way recovery is possible exactly
when \(b\) is symplectic. The minimum message entropy for unconstrained
optimal fidelity is \((2m-r)\log_2 p\). The same rank governs the
minimum effective helper size: every such map can be realized in this
three-region setting with exactly \(2m-r\) effective helper qudits.

We recover the known single-logical-qubit, single-target-qubit recovery
statement. Holding the other printed rows fixed, the one-entry repair of
Example 3 in arXiv:2609.00234v1 gives three exact fidelities \(1,1,1/3\).
A separate algebra check identifies and corrects one misprinted Pauli
in that example's generator table; the theorem does not depend on it.

This is an exact one-way recovery theorem for the stated equal-dimension
stabilizer setting, not a claim for larger targets, nonstabilizer
encodings, additional entangled assistance, or two-way LOCC.

See [proof](PROOF.md), [sources](SOURCES.md) and [replay](RESULTS.txt).
Run `sh replay.sh` with Python 3.10 or later and NumPy.
