# The complete order-nine quantum Latin square cardinality spectrum

Every integer from 9 to 81 except 10 is the cardinality of a quantum
Latin square of order nine. We give constructions for all thirteen
uncertain cases in Zhang–Lv–Cao, arXiv:2607.19969v2, Section 5, Table 6:

\[
\{34,60,61,62,65,66,67,68,69,70,71,73,74\}.
\]

Nine use two matrices selected from the catalog of sixth-root
Hadamards of order nine (with explicit indices and row permutations).
Cardinality 73 uses a three-value Hadamard on the additive group of
the field of nine elements. For 34, 61 and 67, a block splice in
\(\mathbb C^4\oplus \mathbb C^5\) gives explicit squares and analytic
counts. Each of the thirteen is independently checked over exact
algebraic number fields, all Gram matrices and all cell pairs.

[Proof and construction](PROOF.md) · [Precise sources](SOURCES.md) ·
[Witness index](witnesses.json) · [Exact replay output](RESULTS.txt)

Run with Python 3 and either a network connection for the public
source catalog or a local copy of the attachment:

~~~sh
sh replay.sh | diff -u RESULTS.txt -
sh replay.sh /absolute/path/to/BH-9-6.txt | diff -u RESULTS.txt -
~~~

The third-party attachment is not bundled. The verifier canonicalizes
its 17 text records to 1496 bytes of ASCII with LF terminators, checks
the expected SHA-256, and independently validates the Hadamard
property of every record. The three block constructions and their
checker do not require external files or an internet connection.

The remaining attainability cases are cited from the order-nine row
of Table 6, not claimed new. The known general exclusion of order
plus one is quoted as Theorem 1.1(1) in the same source.
