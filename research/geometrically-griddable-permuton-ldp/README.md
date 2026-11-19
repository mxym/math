# A permuton large-deviation principle for geometrically griddable classes

Choose a permutation uniformly from the order-$n$ members of an infinite hereditary class that fits inside a fixed finite geometric grid. How many members of the class have a plot close to a specified limiting shape? The [whole-grid proof](PROOF.md) and [subclass corollary](SUBCLASSES.md) give the exponential count for shrinking weak neighborhoods, and a speed-$n$ large-deviation principle with a good rate function.

**Two different entropies enter.** A time profile $p(t)$ records the proportions of cell letters in a word encoding the permuton. For a whole grid, the local counting exponent at $\mu$ is
\[
  S(\mu)=\max_{\Phi p=\mu}\int_0^1 e(p(t))\,dt,
\]
where $e$ counts traces with approximately prescribed letter frequencies. Its pressure is given by the weighted clique polynomial. Thus the base-two rate function is $\log_2 g-S(\mu)$ for class growth $g$. For an arbitrary geometrically griddable class, the analogous exponent is the largest of the exponents for the finitely many undotted cores given by Albert–Atkinson–Bouvel–Ruškuc–Vatter's structural theorem.

The entropy per point of a permutation sampled from $\mu$ itself is instead $C(\mu)=\int_0^1 h(p(t))\,dt$ for **any** representing profile, where $h$ is the iid-letter trace entropy. For a connected nonstar whole grid, even the largest possible $C(\mu)$ over its entire limit class is strictly below $\log_2 g$; some neighborhoods nevertheless have the full counting exponent. The rate need not be given by subtracting catropy from log growth.

This addresses [Borga–Féray–Winkler, Problems 6 and 8](https://arxiv.org/html/2611.12104v1#S8.SS3) for this family, not for all permutation classes or arbitrary singular permutons. No uniqueness of the typical shape is asserted. The [earlier segment-uniform result](../geometric-grid-catropy/) is used, not restated as a new contribution.

[Sources and theorem-by-theorem comparison](SOURCES.md) · [Internal whole-grid review](REVIEW.md) · [Internal subclass review](SUBCLASSES-REVIEW.md). This is an AI-assisted research draft, independently checked internally, not externally peer-reviewed. No guarantee of priority.

Finite checks (Python 3.10+, standard library; not a substitute for the limiting arguments):
```sh
sha256sum -c SHA256SUMS
python3 -B -O check.py | diff -u CHECKS.txt -
```
