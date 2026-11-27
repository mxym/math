# A nonlinear partial spread for Gorodilova's Conjecture 3

[Conjecture 3 of Gorodilova (2020)](https://arxiv.org/pdf/2005.10788#page=6) is false as stated, including in dimension five. For every odd \(n=2m+1\ge5\), take the graph of \(x\mapsto\operatorname{Tr}_{4/2}(x_1x_2)\) on \(\mathbb F_4^m\). It is the union of \((2^{n-1}-1)/3\) binary 2-spaces with pairwise intersection \(\{0\}\). Its intersection with every linear codimension-two subspace has even size, so all the conjecture's plane counts are even. It is not any hyperplane.

[The proof](PROOF.md) also identifies the exact parity condition as a binary second-moment condition. In dimension five it classifies all such point sets, not their decompositions: they are the 31 linear hyperplanes and 13,888 nonlinear quadratic graphs, one linear-equivalence class of each kind. An independent exact-cover calculation checks that classification.

No quadratic APN function is asserted to realize these point sets as zero sets of an ortho-derivative component. In fact, the all-even examples cannot arise that way. This only disproves the separately worded geometric Conjecture 3. The main component-degree Conjecture 2 of the same article was proved by Carlet and Thornburgh; see [source notes](SOURCES.md).

## Reproduce

Python 3.10+ and a POSIX shell, no downloads or third-party packages:

    sh replay.sh | diff -u RESULTS.txt -

The general result and the dimension-five classification are proved in the text. The scripts are independent finite checks, not a prerequisite for either conclusion.
