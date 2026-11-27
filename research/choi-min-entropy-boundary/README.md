# When a channel's conditional min-entropy matches its Choi state's

The equality for a unitary mixed with global white noise
and a conditioning qubit is known. It does **not** extend
to all mixtures of two unitaries: the mixture of identity
and controlled-Z on two qubits gives a strict gap at every
nontrivial weight. At weights 60:40 the state trace cost is
exactly \(6/5\), while the channel cost is at least
\(1388/1105>6/5\). Both claims have exact rational certificates.

The same analysis gives an equality criterion for global
white noise in arbitrary conditioning dimension, and exact
costs for orthogonal controlled blocks. A qubit--qutrit
example shows why the known qubit hypothesis matters.
Separately, local depolarizing noise composed before or
after the unitary on a conditioning qubit **does** preserve
equality. This is a composition theorem, not a statement
about replacing the entire channel by a different product
channel.

[Proof](PROOF.md) · [Sources and scope](SOURCES.md) ·
[Exact verification output](RESULTS.txt)

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~

One checker uses exact rational support-matrix dominance
and trace witnesses. The other constructs the Choi
coefficients directly from gates and verifies the Pauli
character actions and the independently lifted 60:40
certificate. The general proofs require no solver or
finite enumeration.
