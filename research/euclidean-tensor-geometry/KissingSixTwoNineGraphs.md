# Two remaining nine-point strict graphs in the 75-point six-dimensional matching obstruction

Write $h(A)=\min_p\sum_{ij}p_ip_j f(x_i\cdot x_j)$, with $f(t)=t^4-t^2/4$ and $p$ a probability on $A$. A strict edge has inner product below $-1/2$; its **strength** is the negative of that product. The [single- and double-heptad theorem](https://github.com/mxym/math/blob/c66c69d6b1c4c940eaa459936bbb12cc79198f87/research/euclidean-tensor-geometry/KissingSixTwoHeptadsAndSeventyFive.md) leaves two component-size lists for a 75-point six-dimensional kissing code **if** it has no 36 disjoint strict pairs. Here the geometry and sign graph of the small nontrivial component can be further restricted.

* In the list $(1,7,11,27,29)$ the seven-component is a chordless cycle, and **every one of its seven edge strengths lies strictly between $.64898$ and $.9841$**.
* In the list $(1,9,11,27,27)$ the nine-component is **one of just two abstract graphs**. The first consists of two vertices connected by three internally disjoint paths with lengths $3,3,4$. The second is a subdivision of $K_4$: in the edge order $AB,AC,AD,BC,BD,CD$ the path lengths are $2,1,4,1,1,2$. In each graph six edges are forced to have strength above $.71932$; every edge has strength below $.9994$, with more stringent bounds for most individual edges in the replay. No other nine-vertex graph is possible in this obstruction.

The energy improvement underlying this classification is valid **in every ambient dimension**: excluding the two stated abstract graphs, any nine-point kissing code has $h\le .159960$. There is no claimed global improvement on the unrestricted $.160830$ without these exceptions. Neither nine-point graph is excluded here, nor is the seven-point template.

## Continuous proof of the graph alternatives

The [previous nine-point census](https://github.com/mxym/math/blob/054956776e97821735ab35e67cf32b7fa74ac0c2/research/euclidean-tensor-geometry/KissingNinePoint160830.md) gives $h\le .159800$ except for ten possible factor-critical graphs. It includes the independent-five and non-factor-critical cases, not just the 170 labeled representatives of the surviving triangle-free census. For eight of the ten exceptional graph classes the [additional exact Gram runs](verify_kissing_six_two_nine_graphs.py) give $h\le .159960$:

| census class | 13 | 37 | 50 | 54 | 58 | 59 | 104 | 112 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| continuous cells | 1,785 | 12,671 | 2,509 | 3,617 | 2,063 | 2,611 | 1,571 | 2,737 |

There are 29,564 cells in all. Each terminal bound uses a nonnegative integer combination of probability tests, positive semidefinite Gram inequalities and coordinate order relations, exactly as in the pinned predecessor. Closed boxes include threshold contacts; no geometrical symmetry assumption or numerical optimum is needed. Suppressing the degree-two vertices of the remaining census classes 10 and 44 gives exactly the two graphs described above.

The [sharp-star component charge estimates](https://github.com/mxym/math/blob/751d856566e3df18af8907927f3b2c3bd4d57865/research/euclidean-tensor-geometry/KissingSharpQuarticStars.md) force $h>.1960992$ on the seven component of the first list, or $h>.1599666$ on the nine component of the second. Thus $.159960$ is strictly small enough in the latter case.

## Why individual edges are forced both toward and away from antipodality

In a graph of order $2m+1$ call an edge $uv$ **critical here** if the vertices other than $u,v$ contain an independent $(m-1)$-set having no edges to $u$ or $v$. On that induced set the pair distribution of uniform weights has self-cost $(3/4+f(a))/2$ for strength $a$; the other vertices give $m-1$ singleton charges $4/3$ each. With nonpositive cross costs, masses proportional to these charges give
\[
                    1/h\ \ge\ \frac{2}{3/4+f(a)}+\frac{4(m-1)}3 .
\]
This is the inequality in the direction appropriate to a minimum-energy measure. Inserting the lower bounds for $h$ forces $a>.64898$ or $a>.71932$ respectively. On the odd cycle all edges are critical; the checker finds exactly six in each of the two nine-graphs.

For the upper cutoff, suppose an edge has strength $a\ge r>1/2$. A third vertex cannot have strong edges to both endpoints. If it has a strong edge to one endpoint, that strength is at most
\[
                       V(r)=\frac{r+\sqrt{3(1-r^2)}}2 .
\]
Indeed the third point is at angle at least $60^\circ$ to the other endpoint, which is at angle $\arccos a<60^\circ$ to the negative of the first endpoint. The spherical triangle inequality proves the bound, monotone in $r$. It is attained for a suitable planar three-point configuration; the companion inner product is then $1/2$.

Let $S$ be any independent $s$-set disjoint from the selected endpoints and let $k$ of its vertices have an edge to the pair. Put $A=3/4$, $D=3/(4s)$ and $C=k f(V(r))/(2s)$. For uniform measures on the pair and on $S$ these are upper bounds on the two self-energies and the cross-energy. One may alternatively take $D$ from a universal bound on the remaining set, using its optimizing probability and $C=f(V(r))/2$ irrespective of the masses. If $h>T$, a proposed $r$ is excluded whenever
\[
     C<T,\qquad (T-C)^2>(A-T)(D-T),\qquad D>T .
\]
These inequalities make a mixture of the two measures have energy below $T$: the quadratic form of their $2\times2$ energy matrix minus $T\mathbf1\mathbf1^T$ is negative on some strictly positive vector. For the seven-cycle, deleting an edge's two endpoints leaves a five-path whose alternating triple has $s=3,k=2$; $r=.9841$ is excluded. For order nine all edge-specific cutoffs follow using the independent sets and the previous seven-point bound $D=.201$ as an alternative. The checker rounds the square root **up** before the rational tests.

**Replay.** In the research directory run `python3 verify_kissing_six_two_nine_graphs.py` for the budget, path lengths, six critical edges and individual cutoffs. Run with `charts` to regenerate all eight continuous proofs, or `charts 37` for a single class. It imports the [pinned predecessor's proof-producing verifier](https://github.com/mxym/math/blob/054956776e97821735ab35e67cf32b7fa74ac0c2/research/euclidean-tensor-geometry/verify_kissing_nine_160830.py). NumPy, SciPy and threadpoolctl are required; run normal Python without `-O`.
