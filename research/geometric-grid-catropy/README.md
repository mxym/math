# When geometric-grid sampling attains class growth

The growth of a permutation class counts **all** permutations in it. Sampling independent points from one fixed permuton may distinguish exponentially fewer possibilities in the Shannon entropy sense. This note characterizes exactly when that loss can be avoided for a finite signed geometric grid with uniform mass on each prescribed diagonal.

Join two nonempty cells when they share a row or a column. A component is a **star** if all its cells lie in one row or one column (a single cell counts). Write $g$ for the class growth rate, the largest of the component growth rates.

* The supremum of the sampling entropy per point over positive cell masses equals $\log_2 g$ exactly when at least one component of largest growth is a star.
* An actual choice with every cell positive **attains that growth bound** exactly when all components are stars with the same number of cells. Their totals may be chosen arbitrarily; inside each component the masses must be equal.
* More generally every connected component attains its own optimum with positive masses on every cell. For several components, the global supremum is the largest component optimum; it is attained with positive mass everywhere exactly when the optima tie. The proof gives uniform finite-error approximations, not closed formulas for general nonstar optima.

These statements address the segment-uniform part of [Borga–Féray–Winkler, §8.3, Problem 8](https://arxiv.org/html/2611.12104v1#S8.SS3). They do not address nonuniform measures along the segments, arbitrary singular permutons, or neighborhood large deviations.

Read the [proof](PROOF.md), [source and overlap comparison](SOURCES.md), and [independent internal review](REVIEW.md). This is an AI-assisted research draft and the independent review is internal, not external peer review. No priority claim.

To replay the optional finite checks, from this directory use Python 3.10+ (standard library only):
```sh
sha256sum -c SHA256SUMS
python3 -B -O check.py | diff -u CHECKS.txt -
```
The checks enumerate guarded trace switches, signed refinements, recovery of block traces and finite mask identities. They are not a proof for arbitrary grid sizes or word lengths.
