# Triangle parity sharpens the grid cap to 119

The [cube exclusion](cube-fibers.md#at-most-one-rectangle-per-equal-bad-prism-pair) gives \(R\le H\), where \(R\) counts good-prism rectangles and \(H\) counts unordered pairs of distinct equal-mark bad prisms. Let \(G\) count grids, \(P\) prisms, \(B=P-6G\) bad prisms, and \(g_T\) the number of grids through triangle \(T\). This implies \(G\le119\) with an additional parity count. No rank or automorphism hypothesis is needed.

Put \(D_g=\sum_T\binom{g_T}{2}\), \(E=\sum_T(g_T-3)(g_T-4)\) and \(n_i=|\{T:g_T=i\}|\). We have \(g_T\le6\), \(\sum_Tg_T=6G\), and 231 triangles, so
\[
4D_g=72G-5544+2E.
\]
The [path budget](bad-prisms.md#rectangles-of-good-prism-mates) and \(R\le H\le B\) give \(4D_g\le3696-P+2B\), or \(84G+2E\le9240+P\).

Each vertex is on exactly seven triangles. The sum of their \(g_T\) is twice the number of grids through that vertex, because each such grid has two lines through the vertex. Since seven is odd, at least one of these triangles has even \(g_T\). Each triangle covers at most three vertices, so at least 33 triangles have even \(g_T\). The exact total degree gives
\[
n_0+n_2+n_4+n_6
=6G-693+4n_0+2n_1+2n_2-2n_5-2n_6
\le6G-693+E.
\]
The last step follows from \(E=12n_0+6n_1+2n_2+2n_5+6n_6\). Hence \(E\ge726-6G\). Substituting gives \(72G\le7788+P\le8639\), one less than \(72\cdot120\).

## Consequences for the short shells

At \(P=851\), the cap implies \(B\ge137\), hence [\(y_2\ge462+2\lceil B/3\rceil\)](bad-prisms.md) gives \(y_2\ge554\). The uniform bounds from the [cube calculation](cube-fibers.md#at-most-one-rectangle-per-equal-bad-prism-pair) improve to
\[
y_3\ge44,672,\qquad y_4\ge3,742,746.
\]
In fact the cube calculation's linear relaxations \(70224-25P-36G\) and \(4838526-588P-5004G\) already imply the claimed bounds except at the corner \((P,G)=(851,119)\). At that corner \(B=137\), \(H\le136\) since the equal-mark classes have size at most three, and the exact upper bound on the relevant equal-mark collision pairs is
\[
d\le136+\min\bigl(15\cdot119,\lfloor(3696-851+2\cdot136)/4\rfloor\bigr)=915 .
\]
Substitution in the [shell formulas](triangle-pair-packing.md#consequences-for-the-short-lattice-shells) gives the displayed bounds. The corner is not asserted to be realized by a graph. None of the four possible ranks is decided by this parity argument.

The later [three-prism rectangle obstruction](rectangle-class-forest.md) uses this parity bound with a stronger rectangle count to reduce the grid cap further, to **118**.
