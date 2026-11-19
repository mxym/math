# Even trees maximize every finite even-pattern count in rooted binary trees

**For every pair of integers $n\ge k\ge1$, the even tree $E_n$ on $n$ leaves contains at least as many leaf-induced copies of $E_k$ as any other rooted binary tree on $n$ leaves.** Here “even” means that at every branch the two child leaf counts differ by at most one. To count a copy, choose $k$ leaves, root their spanning subtree at their lowest common ancestor, and suppress every unary vertex. For example, at $k=6$ the pattern has two three-leaf branches; the result compares its counts at *each* host size $n$, not just their limiting proportions.

This proves the finite binary conjecture of [Czabarka, Székely and Wagner](https://arxiv.org/pdf/1601.07149) (Conjecture 1 of the preprint). They already determined the asymptotic inducibility, and the finite balanced-quartet case $k=4$, including uniqueness, was subsequently established by Coronado, Mir, Rosselló and Valiente. We make **no general uniqueness or higher-arity claim**. This differs from [the double-caterpillar upper-boundary result](../double-caterpillar-profiles/README.md), which concerns two simultaneous limiting densities rather than a single finite count.

## Why comparing pattern sizes helps

Start by balancing the two children of an arbitrary tree. Re-pair their four branches so that the *new* children have sizes differing by at most one. Whether this exchange increases the count depends on how consecutive even patterns grow with host size. The proof establishes both facts by induction: the inequalities already known for smaller hosts justify the exchange; extremality at the new size then proves the next growth inequalities. The result also gives nonnegative two-by-two minors of $A(n,k)$, the array of even-pattern counts in even hosts.

Two specific precedents matter here. Coronado and coauthors already used comparisons among four grandbranches for $k=4$. Both growth inequalities from deleting and duplicating a leaf are those of Czabarka, Dossou-Olory, Székely and Wagner for optimal counts. The multi-order comparison and the root-spanning estimate are what close the induction. See the [full proof](FULL.md) and [sources and scope](SOURCES.md).

## Reproduce the finite part

The proof reduces the unbounded pair of size parameters to an explicit finite base for a growth inequality. The [standard-library Python verifier](fullcert.py) checks 1,373,505 integral minors and 1,365,630 quantitative gaps. A [separate C++/GMP verifier](independent.cpp) recomputes the same integers by adding split contributions over tree depths rather than using the author's size recurrence. A third, optional [exchange check](exchangecheck.py) replays the two-level identity including ties and empty branches. These supplementary examples are not the proof of the exchange.

From this directory, run:

```sh
sha256sum -c SHA256SUMS
python3 -BO fullcert.py > replay.txt && diff -u FULL-CHECKS.txt replay.txt
python3 -BO exchangecheck.py > exchange.txt && diff -u EXCHANGE-CHECKS.txt exchange.txt
```

The independent implementation additionally requires a C++17 compiler and the GMP C/C++ libraries on an LP64 platform:

```sh
g++ -std=c++17 -O2 independent.cpp -lgmpxx -lgmp -o even-tree-check
./even-tree-check > independent.txt && diff -u INDEPENDENT-CHECKS.txt independent.txt
```

The [separate internal review](REVIEW.md) identifies the frozen proof hash and addresses the support endpoints, both parities and quantitative error. This is an AI-assisted working paper with an independent internal AI check, not external peer review or proof-assistant verification. No priority guarantee is made.
