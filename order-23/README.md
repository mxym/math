# The missing cardinality 528 for quantum Latin squares of order 23

There is an explicit quantum Latin square of order 23 with 528 distinct
rays. It has exactly one repeated ray, in cells (0,1) and (1,0), using
zero-based indices. Its entries are given by one phase, the nonzero quadratic
residues modulo 23, and a single permutation of 23 coordinates.

Zhang–Lv–Cao, [*On the possible cardinalities of quantum Latin squares*,
v2](https://arxiv.org/html/2607.19969v2#S5), mark 528 as the sole uncertain
order-23 cardinality in Table 6. Combining their table and the known
impossibility of cardinality 24 (their Theorem 1.1(1)) with this construction
gives the exact order-23 spectrum: the integers from 23 to 529 inclusive,
except 24. Only existence at 528 is the new result in this note.

[PROOF.md](PROOF.md) gives the exact construction and verification.
[verify_bits.py](verify_bits.py) checks the directed column-difference
intersection using two integer masks per difference.
[verify_direct.py](verify_direct.py) independently checks all 46 bases and
all 139,656 pairs of cells using exact quadratic-field arithmetic, without
using the difference-mask criterion. Both include controls with different
permutations. Reproduce both with Python 3.10 or later:

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~

See [SOURCES.md](SOURCES.md) for precedent, exact scope, and source checks.
