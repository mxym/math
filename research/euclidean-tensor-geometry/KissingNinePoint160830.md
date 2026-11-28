# A sharper nine-point quartic bound removes the double-nine kissing template

Let $X=\{x_i\}$ be nine unit vectors in any Euclidean dimension, with every distinct inner product at most $1/2$. Write $f(t)=t^4-t^2/4$ and
\[
 h(X)=\min_{p\geq 0,\ \sum p_i=1}\sum_{i,j}p_ip_j f(x_i\cdot x_j).
\]
A strict edge joins two vertices with inner product below $-1/2$. This is an optimized-weight result, **not** an upper bound of the same value for uniform weights.

**Theorem.** In every dimension, $h(X)\le 0.160830$. In fact $h(X)\le0.159800$ unless its strict graph is one of ten explicit nine-vertex graphs. This improves the [previous all-dimensional upper bound $0.161$](https://github.com/mxym/math/blob/0af4adc189728c7d1abe67825746bc5a9c4be53c/research/euclidean-tensor-geometry/KissingNonagonSymmetryBreaking.md); it does not determine the sharp nine-point maximum. The earlier rank-five example has $h(X)>0.158737$.

**Six-dimensional consequence.** If a 75-point kissing code in $\mathbb R^6$ has no 36 disjoint strict pairs, its component orders **cannot** be $(1,9,9,27,29)$. That removes one of the [six previous possibilities](https://github.com/mxym/math/blob/b6aced61e83a9f6c6b8956aa59f2f53241d96e38/research/euclidean-tensor-geometry/KissingSixHybridCycleComplement.md). Five remain:
~~~
1,7,7,27,33    1,7,7,29,31    1,7,9,29,29
1,7,11,27,29   1,9,11,27,27
~~~
In the last list, the nine must be one of the ten graphs. We do not rule out 75 points, prove the existence of any list, or change the unrestricted kissing-number bound.

## From the continuous configurations to ten exceptional graphs

A strict triangle is impossible: its three vectors would have a sum with negative squared norm. If five vertices are independent, their uniform measure has energy at most $(3/4)/5=0.15$, as $f\le0$ on $[-1/2,1/2]$. The exhaustive graph census generates the remaining 290 triangle-free isomorphism classes with independence number at most four. Of these 170 are factor-critical, meaning deletion of each single vertex leaves a perfect matching.

For the other 120, the [previous barrier reduction](https://github.com/mxym/math/blob/1a6fdc1dc8d4a4a1df7aef313b34e9c21b472400/research/euclidean-tensor-geometry/KissingNinePointCapacityAnd127Matching.md) gives separated blocks $7+1$ after one deletion or $5+1+1$ after two. A canonical Tutte–Berge barrier leaves odd factor-critical components; a non-singleton triangle-free such component has order at least five. Their independence numbers sum to at most four, leaving exactly these alternatives. Allocate mass to the blocks in proportion to their reciprocal upper energies. The previously verified seven- and five-point bounds $0.2015$ and $0.252$ yield reciprocal energy at least $1/.2015+4/3$ or $1/.252+8/3$, respectively. Both exceed $1/.1598$. Discarded vertices simply get zero mass.

The [standalone proof-producing replay](verify_kissing_nine_160830.py) stores each of the 170 representatives as nine neighbor bit masks; bit $j$ of row $i$ means an edge $ij$. In its frozen zero-based ordering the ten exceptions to the stronger bound are:
~~~
10, 13, 37, 44, 50, 54, 58, 59, 104, 112
~~~
These are ten classes **allowed by the proof**, not ten examples above $0.159800$. The census reconstructs the graph family by an independent-neighborhood extension, canonicalizes it by partition refinement plus individualization, tests all one-deletion matchings, and compares its set of canonical forms with the fixed representatives. The longest numerical search is class 10: vertices 6 and 8 are joined by internally disjoint paths $6,0,4,8$; $6,1,5,8$; and $6,2,7,3,8$.

## What the continuous calculation proves

For each graph use all 36 off-diagonal Gram entries as variables. Start at $[-1,-1/2]$ on strict edges and $[-1/2,1/2]$ elsewhere, deliberately retaining both copies of the boundary. Simultaneous relabeling by graph automorphisms justifies lexicographic order cuts. Signed spherical triangle inequalities tighten intervals, with integer-square-root certificates. This permits all Gram ranks; six dimensionality enters only in the application.

Each leaf uses a nonnegative integer combination of three types of valid inequality: a test probability with integer weights summing to 600; an orbit order; and $v^TGv\ge0$ for an integer vector $v$. A convexity secant, a constant maximum, or a certified quartic Bernstein upper bound on each closed interval majorizes $f$ by an affine function. After combination, the upper bound of the resulting affine expression on the entire box is checked by exact integers. Leaves either give a test with energy at most the stated target, in the sense that not all probability tests can exceed it, or contradict Gram feasibility. Recursive subdivisions cover both closed children. LP duals and eigensolvers **suggest** cuts and multipliers, never settle their signs. The source rejects optimized Python mode because assertions verify integer square roots and probability weights.

The completed run used 59,086 cells for the 160 classes at $0.159800$ and 36,102 cells for the ten at $0.160830$. Total: 95,188 cells, 47,678 integer-dual leaves, one incompatible-interval leaf, maximum depth 28. Class 10 alone used 19,279 cells and 9,640 integer-dual leaves. Replays may discover different valid trees with a different linear algebra backend.

## The 75-point contradiction

In $\mathbb R^6$, the constant zonal coefficient of $f$ is $1/48$ and the other coefficients are nonnegative. Between different strict components all quartic costs are nonpositive. Combining local witnesses by reciprocal-energy weighting therefore gives a total charge budget of 48. Use the [certified order-27 charge](https://github.com/mxym/math/blob/5c34aa6bc59244f3ed2a33ea1b224ae6d5b7b2a0/research/euclidean-tensor-geometry/KissingSixSeventyFiveExtension.md) and [order-29 charge](https://github.com/mxym/math/blob/70aeadbd0f6859eda06452177fb39cebd763eec1/research/euclidean-tensor-geometry/KissingSixStrictPairCover.md), rounded down:
\[
 \frac43+\frac{2}{0.160830}+16.540366+17.692255
   =48.00144\ldots>48.
\]
For the list $(1,9,11,27,27)$, a nine not on the ten-class list would instead contribute at least $1/.1598$; the other charges are at least $4/3$, $7.329707$, and $2(16.540366)$. This ten-class restriction does not automatically extend to $(1,7,9,29,29)$, whose other charges are smaller.

**Replay** (normal Python 3.10 or later, NumPy, SciPy, and threadpoolctl):
~~~sh
python3 verify_kissing_nine_160830.py census
python3 verify_kissing_nine_160830.py budget
python3 verify_kissing_nine_160830.py 0          # one quick class
python3 verify_kissing_nine_160830.py 10         # the longest class
python3 verify_kissing_nine_160830.py            # full proof, or split classes across workers
~~~
