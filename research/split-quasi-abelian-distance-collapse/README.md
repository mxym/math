# Vanishing distance of fixed-index split quasi-abelian codes

Fix a finite field \(\mathbb F_q\) with \(q>2\), a prime \(p\mid(q-1)\),
and an index \(\ell\). Over the growing groups \(C_p^d\), **every**
positive-rate family of quasi-abelian codes of index \(\ell\) has
relative minimum Hamming distance tending to zero. This is a deterministic
statement, without a systematic-form or generator-distribution hypothesis.
The upper bound is \(O(d^{-\log_2(p/(p-1))})\) at rate bounded away from
zero. For odd \(q\) one can choose \(p=2\), giving \(O(1/d)\).

This disproves the arbitrary-group growing-size GV claim formalized in
[AICR c/0105](https://aicr.info/c/0105/) by a split, semisimple group
family. The case \(p=2\) over odd \(q\) also addresses the fixed-index,
fixed-field distance question in [Li et al. 2026/939](https://opencryptology.org/2026/939.pdf),
for their family \(C_2^d\). It does not contradict the finite-parameter
large-field bound in that work, the fixed-group/increasing-index theorem
of Fan and Lin, or the successful cyclic families of Gaborit and Zémor.
The published modular obstruction uses a different, same-characteristic
hypothesis. See [SOURCES.md](SOURCES.md).

These are abstract Hamming-distance bounds, not decoding procedures,
concrete protocol evaluations, or statements about cryptographic security.
The analytic proof is [PROOF.md](PROOF.md). Independent exact checks on
small coefficient spaces can be run with
`sh replay.sh | diff -u RESULTS.txt -` (Python 3, standard library only).
