# Two fixed negacyclic rows suffice for worst-case Hamming hardness

Two ring rows are enough, and are minimal, in a fixed-odd-modulus worst-case Hamming problem. The hardness construction does not repeat rows or blank out unused coordinates. It uses the support of an exact signed grid circulation to recognize partitions into three-vertex paths.

## 1. Statement

At a dyadic square dimension \(d=W^2\), where \(W\ge4\) is a power of two, set
\[
 R=(\mathbb Z/q)[X]/(X^d+1),\qquad D_x=1-X,\quad D_y=1-X^W .
\]
The coefficient-Hamming decision problem
\[
 \min_{s\in R}\bigl(\operatorname{wt}(y_x-D_xs)
                      +\operatorname{wt}(y_y-D_ys)\bigr)\le B
\tag{1}
\]
is NP-complete for every fixed odd \(q\) divisible by 3. Both public rows are distinct weight-two units specified by \(d\) alone. Only the explicit target \((y_x,y_y)\) and integer threshold \(B\) vary. For \(q=3\) it is also NP-hard to return an exact maximizer of the coefficientwise wrapped-Gaussian likelihood at rational phases \(y_x/3,y_y/3\) for any fixed positive width, since the two nonzero residual phases have equal likelihood strictly below that at zero.

In contrast, with **one** public row and any fixed odd modulus, the coefficient-Hamming decision problem is in deterministic polynomial time, even allowing a nonunit row supplied as part of the input. This is a statement about this least number of rows for the fixed-modulus worst-case optimization problem (and for the ternary grid likelihood), not about samples drawn from a ring learning distribution.

## 2. Cross difference and signed graph

Both \(D_x,D_y\) are units: for \(h\mid d\), the product of \(1-X^h\) and \(\sum_{j=0}^{d/h-1}X^{hj}\) is \(1-X^d=2\). Define
\[
                      \partial(e_x,e_y)=D_y e_x-D_x e_y .
\tag{2}
\]
Because the two multipliers commute and \(D_x\) is a unit,
\[
              \ker\partial=\{(D_xs,D_ys):s\in R\}.
\]
Indeed an element \((v_x,v_y)\) of the kernel satisfies \(v_y=D_yD_x^{-1}v_x\), and the reverse inclusion follows by commuting. Every \(z\in R\) is a possible value of \(\partial\) since the \(e_y\) map is invertible by itself. Consequently the optimum in (1) is exactly
\[
       \min\{\operatorname{wt}(e_x)+\operatorname{wt}(e_y):
                           \partial(e_x,e_y)=\partial(y_x,y_y)\}.
\tag{3}
\]

Draw the coefficient vertices as \(i=x+Wy,\ 0\le x,y<W\). A coordinate of \(e_x\) gives one edge from \(i\) to \(i+W\bmod d\); a coordinate of \(e_y\) gives one from \(i\) to \(i+1\bmod d\). The two coefficients in the corresponding column of (2) are opposite signs unless this shift crosses the negacyclic endpoint \(d\), when they are the same sign. This includes the horizontal edge from the last coefficient to the first and the vertical edges joining the bottom and top of the square. Row-end horizontal edges from one row to the next also remain in the graph, even when their opposite signs are ordinary. Every non-grid-neighbor edge is incident only to boundary vertices. Between vertices strictly inside the square the graph is the ordinary nearest-neighbor grid, with opposite column signs. No boundary constraints are dropped.

Let \(T\) be a set of strictly interior vertices (terminals), put \(N=|T|\), and let \(a=q/3\in\mathbb Z/q\), of additive order three. Let \(z\in R\) have coefficient \(a\) at precisely the terminals and zero elsewhere. For every \((e_x,e_y)\) with \(\partial(e_x,e_y)=z\), look at the graph of its nonzero coordinate edges and their endpoints. Every terminal lies in this graph. For a connected component with \(k\) terminals, \(v\) nonterminals and \(E\) edges, \(E\ge k+v-1\).

* If all the component's columns have opposite signs, summing their equations over its vertices gives \(ka=0\). Hence \(k\) is a multiple of 3. For \(k>0\), \(E\ge k-1\ge 2k/3\), with equality exactly for \(k=3,v=0,E=2\).
* If a same-sign column is used, the component contains a boundary nonterminal. For \(k>0\), \(E\ge k>2k/3\). This count does not presume a zero total charge, so it covers arbitrary cycles through the twisted boundary.
* A component without terminals that contributes any support edges adds strictly positive cost.

A component at equality therefore consists of a three-vertex path of terminals in the ordinary grid. Conversely each path of three terminals carries the demanded charge on its two edges: on each edge choose the nonzero value giving its leaf coefficient \(a\), so the center receives \(-2a=a\). By summing over disjoint paths we obtain all demands. Thus
\[
 \min_{\partial(e_x,e_y)=z}\bigl(\operatorname{wt}(e_x)+\operatorname{wt}(e_y)\bigr)
 \ge 2N/3,
\qquad
 \text{equality iff the induced grid on \(T\) has a \(P_3\)-partition}.       \tag{4}
\]
In particular, adding neutral vertices, extra helical grid edges, and twisted sign edges cannot improve the equality threshold.

There is also a quantitative packing consequence. If a component with terminals is not one of the three-vertex paths at equality, its excess cost \(E-2k/3\) is at least \(k/6\). For an ordinary component with \(k\ge6\) this follows from \(k/3-1\ge k/6\); for \(k=3\) its excess is at least one; for a same-sign component the preceding bound gives at least \(k/3\). Let \(P(T)\) be the maximum number of terminals covered by vertex-disjoint three-vertex grid paths. Then (3) for such \(z\) is at least \(2N/3+(N-P(T))/6\), since the equality components collectively cover at most \(P(T)\) terminals. This is a support inequality, not a claim of hardness for constant fractional approximation on the fixed grid.

## 3. Reduction and Gaussian likelihood scope

[Van Bevern et al., Partitioning Perfect Graphs into Stars, §6, Theorem 8](https://igm.univ-mlv.fr/~bulteau/pdf/BBBCFNW-jgt16.pdf) prove NP-hardness of partitioning induced grid graphs of maximum degree three into paths on three vertices. The paper's grid input uses exactly Manhattan-distance-one adjacency on its vertex set, and its reduction produces coordinates. It is enough to use inputs with \(N\) divisible by 3; the other inputs are automatically negative. Even if arbitrary original integer coordinates are allowed, sort each axis's distinct values and replace every successive gap by \(1\) if it was \(1\) and by \(2\) otherwise. Equalities and unit differences are preserved on each axis, with no new unit differences between nonconsecutive values. The resulting grid widths are \(O(N)\). Translate and pad to the interior of the least fitting power-of-two square, so \(d=O(N^2)\).

Use the given grid vertices as \(T\), define \(z\) as in §2, and set \(y_x=0,\ y_y=-D_x^{-1}z\), giving \(\partial(y_x,y_y)=z\). This is a polynomial-time transformation of the hardness-instance data; \(D_x^{-1}\) is the fixed geometric sum divided by 2. Set \(B=2N/3\). Formula (4) proves both directions, and membership in NP follows by direct verification of a coefficient label's Hamming cost. For \(q=3\) the scalar wrapped Gaussian \(f_b(x)=\sum_j b^{j^2}e^{2\pi i jx}\) is even and positive, and \(f_b(0)>f_b(1/3)\) for \(0<b<1\) by its strictly positive nonconstant Fourier weights. The \(1/3,2/3\) residuals therefore cost the same positive loss in log likelihood. An exact continuous-likelihood maximizer on these inputs is an exact Hamming minimizer, with no real threshold comparison needed.

## 4. Why a single row is different

For an arbitrary single public row \(A\), the possible prediction vectors form the ideal \(AR\). At fixed \(q\) the factors stabilize in a fixed dyadic base dimension \(d_0\). For each odd prime \(p\mid q\), every mod-\(p\) factor at higher dyadic \(d\) is \(F(X^g)\) for some factor \(F(T)\) at \(d_0\), with \(g=d/d_0\); this follows from the eventual exact doubling of \(\operatorname{ord}_{2d}(p)\). The coprime lifts modulo prime powers substitute in the same way. All ideals in each lifted local factor are powers of \(p\) by its residue field and finite freeness. Consequently every ideal \(J\) of \(R\) is an extension of a fixed-base ideal \(J_0\), with
\[
                          J=\bigoplus_{j=0}^{g-1}X^j J_0
\tag{5}
\]
as disjoint coefficient groups. See [the detailed fixed-type argument, §3](https://github.com/mxym/math/blob/3e3d636250444949f79182a2cb9dafbea4a03786/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-coordinate-degree-frontier.md).

This decomposition can be located in polynomial time for the ideal \(AR\): in each fixed prime-power factor reduce the coefficient groups of \(A\) modulo the corresponding fixed-base lifted factor, then read the lowest coefficient valuation across those groups. It is the valuation of the higher-dimensional ring component, because its standard coefficient positions split into those base groups. These finitely many valuations identify the base ideal. Each term of the nearest-word Hamming cost now involves only a single group of \(d_0\) coefficients and can be minimized over the constant-size set \(J_0\), independently of the other groups. Summing the group minima gives the exact decision in polynomial time. The bounded base length relies on \(q\) being fixed and odd; it is not an assertion for arbitrary code representations, arbitrary growing moduli or arbitrary real likelihood comparison.

## 5. Prior work and scope

[Apte et al., Cycle Codes and Decoded Quantum Interferometry, §3.1, Theorem 2](https://arxiv.org/abs/2609.40036v1) prove NP-completeness of minimum-weight syndrome decoding for nonbinary cycle codes with a graph that varies with the instance. That prior work uses charge-based support counting, which also motivates (4). Here the graph is fixed by dimension, all non-ordinary edges and their signs are retained, only the demand is changed, and the charged-grid reduction yields a single rank-one negacyclic code with two specified blocks. The earlier [constant-row likelihood note](https://github.com/mxym/math/blob/72abb9dc114dc8019493847788157336bd735079/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-constant-row-likelihood-hardness.md) used six or twelve rows and had a separate ETH and additive approximation theorem. Its stronger quantitative complexity assertions do not transfer automatically to this two-row result.

This does not show hardness or easiness of a random-design Ring-LWE instance, and does not provide a decoder for a real scheme. It is an exact worst-case finite optimization statement with deliberately fixed arithmetic and synthetic input data.
