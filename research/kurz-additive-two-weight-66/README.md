# A projective additive quaternary two-weight code of length 66

A set of 198 projective binary points defining the \([198,10,\{96,112\}]_2\) code in SageMath's Chen database entry partitions into 66 pairwise disjoint projective lines. The explicit partition in **partition.tsv** gives a projective \(\mathbb F_2\)-additive quaternary \([66,5,\{48,56\}]_4\) code, with 825 nonzero words of weight 48 and 198 of weight 56. This answers both questions in Sascha Kurz's arXiv:2412.14615v3 Remark 18 for the specified public point-set representative.

The code is strictly additive: its 66 binary codelines admit no common field-scalar action that could make the code \(\mathbb F_4\)-linear, even after local relabeling and coordinate permutation. The proof uses an exact 99-rank binary linear system, checked by two independent implementations. This is consistent with the previously known nonexistence of an \(\mathbb F_4\)-linear projective code of these two-weight parameters.

The finite certificate is self-contained; it does not require SageMath, any solver, or a live network. Reproduce the two checks with Python 3 and GNU sha256sum:

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~

For optional provenance replay on the unchanged upstream generator, see SOURCES.md. The source database is not shipped in this package.
