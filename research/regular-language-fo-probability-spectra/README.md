# The first-order probability spectrum of every infinite regular language

**Yongxian Zhang · research draft · 19 November 2026.** Fix a regular language and choose a word uniformly at each nonempty length. First-order predicates see the positions, their order and their letters, not the states of an automaton. Which numbers can be the ordinary, full-sequence limiting probability of an individual sentence?

* If every eventually occupied length residue grows exponentially, the answer is exactly $[0,1]\cap\bigcap_s\mathbb Q(r_s^P)$. Here $P$ is a common cycle-period multiple, and $r_s$ is the largest component growth rate available at residue $s$. In particular, a pure length-count asymptotic $c n^d r^n$ with $r>1$ gives exactly $[0,1]\cap\mathbb Q(r)$.
* If even one occupied residue has polynomial growth, the answer is a **computable finite set of rational numbers**. A shared finite truth assignment must yield the same limit on all polynomial residues. An [example](EXAMPLE.md) has the probability $1/2$ on each phase separately, yet no single first-order sentence attains it on the whole sequence.
* **Small permutation classes.** For every exponentially growing small class of permutations the two-order spectrum is exactly $[0,1]\cap\mathbb Q(r)$, not merely dense. Here the existence of a limit for every sentence was already known. This corollary uses Markström–Räty's explicitly stated, **sketched** two-way coding theorem. The exact polynomial small-class spectrum was already obtained by Falgas-Ravry, Markström, Räty and Skerman.

[Exponential/hidden-state proof](WORDS.md) · [Polynomial and mixed proof](POLYNOMIAL.md) · [Small-class application](SMALL.md) · [Full source comparisons](SOURCES.md) · [First internal review](REVIEW.md) and [polynomial review](POLYNOMIAL-REVIEW.md).

The regular-language result describes the range of sentences **whose probabilities converge**, not a convergence law for every word sentence in every regular language. It uses observable words to find and reset the appropriate component type even when the states of the given automaton are invisible. The previous [geometric-grid note](../geometrically-griddable-fo-probabilities/README.md) supplies the field-coin simulation after regeneration; the earlier geometric hypothesis does not cover every small permutation class.

AI-assisted research and independent internal AI checking, not external peer review. No priority guarantee. Standard-library finite sanity checks (not proofs of the general theorems):
```sh
sha256sum -c SHA256SUMS
python3 -B -O check.py | diff -u CHECKS.txt -
```
