# Five missing order-11 quantum Latin square cardinalities

We give explicit quantum Latin squares of order 11 with cardinalities
**66, 106, 113, 115, and 119**. Each is a mixed Schur product of a
two-value Björck circulant Hadamard and a specified row permutation of
it. All five cardinalities are marked uncertain in the order-11 row
of Zhang–Lv–Cao, arXiv:2607.19969v2, Section 5, Table 6.

We also classify the **cardinality image of this one construction** as
the row permutation varies over all \(11!\) choices. Its exact image is
\[
  \{66,105,106,113\}\ \cup\ \{115,116,117,118,119,120,121\}.
\]
Two independent orbit enumerations yield the same exact count of
permutations for each cardinality. This is not the full spectrum of
order-11 quantum Latin squares; in particular, absence from this
construction says nothing about unrestricted nonexistence.

[PROOF.md](PROOF.md) gives the formulas, the explicit witnesses, and
both enumeration reductions. [SOURCES.md](SOURCES.md) credits prior
constructions and records the check on the status of the five cases.
[RESULTS.txt](RESULTS.txt) records the complete histogram and exact
independent Gram/ray checks. Replay with Python 3 and a C++17 compiler
(GCC or Clang). The writable temporary directory must also permit
executing the two compiled verifier binaries; set TMPDIR if needed.

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~
