# One or three eligible 22-cocliques and ten short-population tuples

Suppose neutral norms 18 and 24 are the only types present among the twelve selected unit types. In each maximal determinant-49 extension there are **one or three** eligible 22-cocliques and **400 to 448** eligible oriented norm-18 labels. At rank 42 these are graph-wide counts. At rank 40 the total graph-wide norm-18 count lies between 2,500 and 2,800.

Fix an extension. Use the raw folded counts $W$ in the [residue-balance theorem](two-type-residue-balance.md). Write $M=W_{2,22}$ for the count of eligible 22-cocliques, $B=W_{0,14}$ for the count of oriented Fano roots, and $S$ for the number of unit charge-one labels of squared norm 23 in this extension. These count actual labels, since each has residual norm zero in the anisotropic plane. The [site-translation dictionary](../affine-witness.md) gives
$$W_{1,23}=99+7B+S.$$
The 99 original marks and the seven translates per oriented Fano root all have a nonunit entry and are distinct. The translates preserve the seven-component.

On this two-type face, the nine [short moment equations](rank36_three_types.py) imply the identity
$$W_{2,34}=1080+14B-9W_{1,23}-42M.$$
The named types use their unit counts in building those nine equations; the four columns in this identity are raw. The equations apply in each individual extension at either rank. The [checker](two_type_short_counts.py) verifies the identity by exact rational rank after setting the other ten selected unit populations to zero. Nonnegativity of $W_{2,34}$ now gives
$$42M+49B+9S\le189.$$

The residue-balance theorem gives an odd positive integer $M$, an integer $W_{0,18}$ and the identity
$$6W_{0,18}=291+5M+16B+2S.$$
Also $B$ is an even nonnegative integer by negation. These conditions admit just the following tuples. Each entry in a list corresponds to the entry in the same position in the adjacent lists.

| $M$ | $B$ | $S$ | $W_{0,18}$ | $W_{2,34}$ |
|---:|---:|---|---|---|
| 1 | 0 | 2, 5, 8, 11, 14 | 50, 51, 52, 53, 54 | 129, 102, 75, 48, 21 |
| 1 | 2 | 1, 4 | 55, 56 | 40, 13 |
| 3 | 0 | 0, 3, 6 | 51, 52, 53 | 63, 36, 9 |

In particular, three eligible cocliques preclude any eligible Fano root. An eligible Fano root forces a single eligible coclique. Each signed norm-4 residue class has exactly $W_{0,18}$ norm-18 labels. Multiplication by eight gives the eligible oriented population. Graph-wide the mean of $W_{0,18}$ multiplied by $7^{(44-r)/2}+1$ gives $N_{18}$ by [isotropic-subspace averaging](../affine-witness.md). At rank 42 the discriminant plane is already anisotropic, so there is just one extension and every 22-coclique is eligible.

At rank 40, let $m_0$ count the graph's 22-cocliques with zero original seven-class, and let $h$ count maximal extensions containing three eligible cocliques. There are 50 extensions, corresponding to the isotropic lines of the four-dimensional minus space. A zero-class coclique belongs to all 50. Each coclique with nonzero isotropic class belongs to its unique isotropic line, since the quotient of its perpendicular by the line is anisotropic. Thus the graph has exactly $50+2h-49m_0$ cocliques. In particular it has between 50 and 150 when $m_0=0$.

Run `python3 two_type_short_counts.py` with python-flint. The tuples are necessary counts. Their realization by a graph remains open.
