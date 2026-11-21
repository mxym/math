# Excluding Seidel rank 34 for the Conway 99-graph

**Theorem.** For a strongly regular graph with parameters $(99,14,1,2)$ the rank of $2A-J+I$ over $\mathbb F_7$ cannot be 34. At that rank the marked lattice would require at least **426,124** signed eigenvectors on eighteen sites. The graph itself allows at most **357,280**. With the [earlier exclusions](../triangle-rank-32/README.md), the remaining ranks are $36,38,40,42$. All statements apply without a symmetry hypothesis.

## An upper bound at every rank

Let $t$ be an integral $-4$ eigenvector of squared norm eighteen. Its support is 4-regular bipartite on nine positive and nine negative sites. Choose a positive root $o$ and let $Q$ be its four negative neighbors. Use the notation $z_{ab}$ for the common neighbor of $a,b\in Q$ other than $o$. Its two neighbors in the neighborhood of $o$ are exactly $a,b$. The six labels are distinct. They cannot be negative, since each sees two negatives. Let $D\subseteq\binom Q2$ index the positive labels. The eight positive sites other than $o$ have twelve incidences with $Q$. Each sees at most two of $Q$ and exactly the $|D|$ labels see two. Thus $4\le|D|\le6$. [Signed-support and rooting lemmas](../short-support-packing/README.md)

Fix $o,Q,D$ and consider two distinct vectors in that family. Their squared distance is at least fourteen. If the omitted pairs miss a vertex $a\in Q$, the distance is at least sixteen. Indeed the two vectors agree throughout the neighborhood of $a$ whenever it contains a nonzero entry of either vector: that support consists precisely of $o$ and the three positive labels incident with $a$. The vectors also agree throughout the neighborhood of $o$, and agree at $o$ and $a$. If their difference had norm fourteen, both adjacent vertices $o,a$ would therefore lie outside and miss its Fano support. Two such vertices cannot be adjacent. For a vertex missing the support, its two common neighbors with each of the seven positive sites exhaust its fourteen neighbors: these common neighbors are all different because same-sign Fano pairs are saturated inside the support. Every one of the fourteen therefore sees the support. Squared norms of integral zero-sum vectors are even, proving the distance bound.

Write $E=(3I-A+J/9)/7$, the orthogonal projector onto the $-4$ eigenspace. For a set $B$ of coordinates where all vectors in a family have the same restriction $v$, their projections on the span of $Ee_i$ for $i\in B$ coincide. If $E_B$ is invertible this common projection has squared norm $d=v^tE_B^{-1}v$, by the Gram formula. If the family has size $M$ and minimum squared distance $\delta$, subtract its common projection. The resulting points all have squared norm $18-d$. Summing all unordered squared distances gives at most $M^2(18-d)$, by subtracting the squared norm of the sum of the points. Therefore
$$M\le\left\lfloor\frac{\delta}{\delta-36+2d}\right\rfloor$$
whenever the denominator is positive.

Take all fourteen neighbors of $o$ for the first coordinates in $B$, with prescribed value $-1$ on $Q$ and zero elsewhere. Their edges are the seven mate pairs. If the six labels induce no edge, append all six labels, with $+1$ on $D$ and zero elsewhere. In every other case append only the labels indexed by $D$. Those labels induce no edges, since they are positive. The only new edges in either matrix join each appended label to its two prescribed parents. Exact inversion gives the following entries. The omitted-pair types are unordered up to permuting the four sites of $Q$.

| Omitted pairs | $\delta$ | $d$, six appended | cap | $d$, only positives appended | cap |
|---|---:|---:|---:|---:|---:|
| Two sharing a site | 16 | $1421/108$ | 2 | $1085/92$ | 4 |
| Two disjoint | 14 | $1337/108$ | 5 | $231/20$ | 12 |
| One | 16 | $1421/108$ | 2 | $553/44$ | 3 |
| None | 16 | $161/12$ | 2 | $161/12$ | 2 |

When the six labels are independent there are $12,3,6,1$ choices in the four rows, giving at most 53 vectors. Otherwise choose one actual edge of the labels. Its two endpoints cannot both belong to $D$. If the two label pairs share a parent, the remaining multiplicities are $7,2,2,0$, giving at most 58. For disjoint label pairs they are $8,1,2,0$, giving at most 50. There are $99\binom74 2^4$ rooted seeds and each oriented vector is counted at its nine positive sites. Hence $N_{18}\le 99\cdot560\cdot58/9=357280$.

## The rank-34 lower bound

Use the [marked lattice and counts](../rank-34-short-support/README.md), with $x_j,y_j$ counting norm $2j$ in its scaled dual and primal lattices, respectively. At rank 34,
$$12343996x_7+1922857x_8+135344x_9=-80275368544+22827x_{10}+8987x_{11}+9440291y_2+962507y_3+40082y_4.$$
The verifier checks the identity on the same 15-dimensional space of weight-22 forms: for general $x$ the constant is $-1479919805y_0+\sum_{j=0}^6 c_jx_j$, where
$$c=(-78795448739,-28040798234,-9508092231,-3043912550,-908471795,-248073595,-60256182).$$
Use $x_0=y_0=1$, $x_1=\cdots=x_6=0$, and $x_7=N_{14}, x_8=N_{16}, x_9=N_{18}$.

The lower bounds $y_2\ge462$, $y_3\ge41058$, $y_4\ge3156588$ and nonnegativity give the required right-hand side. The [packing bounds](../short-support-packing/README.md) give $N_{14}\le990$ and $8N_{16}+14N_{14}\le77616+24\cdot851$. The maximum of $12343996N_{14}+1922857N_{16}$ in this relaxation occurs at $N_{14}=990$ because $12343996>14\cdot1922857/8$. Substitution gives
$$N_{18}\ge\frac{115346399395}{270688}>426122.$$
The count is even by sign reversal. Its least possible value exceeds the upper bound above.

Run `python3 verify.py` in this directory to replay every inversion, the seed counts, the Fourier relation and the final arithmetic. The preceding linked notes contain the graph-mark count and signed-vector packing replays.
