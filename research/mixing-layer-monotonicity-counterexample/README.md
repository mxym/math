# A mixing layer can increase pairwise-independence distance

We give an exact finite counterexample to a pattern-independent mixing monotonicity principle for key-alternating substitution-permutation networks.

The state has two 3-bit words. Three keyed applications of one explicit bijective S-box are used, with independent uniform round keys. Inserting the single field-linear shear
\[
L(x,y)=(x,x+y)
\]
between the first two S-box layers increases the total-variation distance from pairwise independence, for one fixed distinct input pair, from \(109/252\) to \(19/36\). The increase is exactly \(2/21\).

This does **not** refute the AES-specific 192-round conjecture of Liu, Pelecanos, Tessaro and Vaikuntanathan. It answers only the clean artificial-counterexample subquestion isolated around that conjecture: adding a linear layer is not monotone in this distance for arbitrary fixed S-boxes and insertion patterns. No deployed cipher, key schedule, attack, or concrete security claim is studied.

See PROOF.md and SOURCES.md. Reproduce the exact transition calculation and a separate full enumeration of all \(64^3\) independent key triples with:

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~
