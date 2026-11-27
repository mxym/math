# Where level-optimal OR search trees are logarithmic or linear

This answers the open broader-workload question after Theorem B.1 of
Etemad, Mahmoody and Evans ([ePrint 2018/052](https://eprint.iacr.org/2018/052)),
recorded as [AICR c/0016](https://aicr.info/c/0016/). It concerns their
Algorithm 2, which minimizes the cost of a perfect matching separately
at each level, not their best-first algorithm.

* **Logarithmic guarantee beyond disjunctions.** An arbitrary
  disjunctive workload can be mixed with monotone combinations of
  any fixed number \(B\) of shared disjunctive tests. For every
  minimum-matching tie rule, the result costs at most
  \((2^B+2)\log_2 n\) times the best tree of any shape. The proof
  also works with a finite join-semilattice summary.
* **Bounded query width alone is not enough.** Pure two-keyword
  conjunction workloads can force every level-optimal output to
  be linearly worse than the best tree. The exact asymptotic
  coefficient of the worst ratio, divided by \(n\), is
  \(\gamma=\sum_{h\ge1}2^{-h}(1-2^{1-2^{h-1}})=0.358885765068\ldots\).
  For unrestricted monotone workloads the coefficient is \(1/2\).
  The bad first matching is unique, and the lower bounds do not
  depend on later matchings. The lower instances can be generated
  with a polynomial-size dictionary.
* These coefficients concern sum of internal local costs. If the
  root visit is counted and one compares the resulting expected
  visited-node counts, the coefficients are \(2\gamma/3\) and
  \(1/3\), respectively.

See [PROOF.md](PROOF.md) for exact model and proof and
[SOURCES.md](SOURCES.md) for source mapping. This is a mathematical
cost analysis; it says nothing about cryptographic privacy, leakage,
or any deployed system.

Reproduce two independent small-case and structural checks with
`sh replay.sh | diff -u RESULTS.txt -`.
