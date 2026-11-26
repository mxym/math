# Exact unit-distance tile-color counts for thick parallelogram grids

**Yongxian Zhang.** AI-assisted development and internal verification.

Let \(a,b\in\mathbb R^2\) be independent and let
\[
T_{ij}=ia+jb+\{sa+tb:0\le s,t<1\},\qquad (i,j)\in\mathbb Z^2.
\]
A tile coloring is constant on each of these half-open tiles and must give different colors to any two points at distance exactly one. Suppose the two perpendicular heights \(\operatorname{dist}(a,\mathbb R b),\operatorname{dist}(b,\mathbb R a)\) are at least \(1/2\). Write \(D=\max(\|a+b\|,\|a-b\|)\). The least number of colors is **9** if \(D<1\), **8** if \(D=1\), and no such coloring exists if \(D>1\). The 8 and 9 also persist for vertex-fixed sufficiently small periodic curvilinear deformations when both heights are strictly greater than \(1/2\).

## The tile conflict graph

We may negate one generator to make \(a\cdot b\ge0\): for the lower bounds one may work only with tile interiors and relabel them, and for the upper bounds the open difference-coordinate intervals are unchanged by reversing a half-open convention. Thus \(D=\|a+b\|\). For two tiles with index difference \((p,q)\) all possible displacement vectors are precisely
\[
(p+s)a+(q+t)b,\quad -1<s,t<1.
\]
This open parallelogram is connected; if it contains vectors of norms strictly above and below one it contains a unit vector. Conversely, if its vectors all have norm \(>1\), no unit conflict occurs. The strict norm witnesses can also always use two interior points. For \((0,0)\), all four corners of the closed displacement domain have norm at most \(D\); strict convexity of the squared norm for independent \(a,b\) gives norm \(<D\) at every interior point. If \(D>1\), continuity and a displacement near a longest corner give two interior points in one tile at distance one.

For any nonzero index difference a norm above one is possible. Indeed choose one nonzero index, say \(p\), and a corner in the closed displacement domain with first coefficient of magnitude \(|p|+1\ge2\). Its projection perpendicular to \(b\) has magnitude at least one. The two choices of second coefficient have distinct parallel projections along \(b\), so at least one choice gives norm strictly greater than one. Move slightly into the open domain. In the other direction, if \(|p|\ge3\) or \(|q|\ge3\), then every open-domain displacement has a perpendicular projection of magnitude strictly greater than one, by the corresponding height bound. Such an offset is never a conflict.

For \((p,q)\ne(0,0)\) with \(|p|,|q|\le2\), choose the displacement in the closed domain whose coefficient in each position is zero when that index has magnitude at most one, and the sign of the index otherwise. Its norm is zero, a side length, or a diagonal length. If \(D<1\) all these norms are below one; if \(D=1\) the only exceptions are the two longest-diagonal shifts, \(\pm(2,2)\), and also \(\pm(2,-2)\) in the orthogonal case. Side lengths are strictly less than \(D\) by the sign choice and independence. Each exceptional shift has no unit conflict: both signed coefficients have magnitude strictly larger than one and both displacement directions have nonnegative inner product, with signs chosen according to the shift. Thus its norm is strictly larger than the corresponding diagonal length one.

## Exact color counts

For \(D<1\) a \(3\)-by-\(3\) block is a nine-clique. Coloring by the two indices modulo three attains nine, since any distinct same-color pair differs by at least three in some index.

For \(D=1\) and \(a\cdot b>0\), any \(3\)-by-\(3\) block permits only one pair of repeated colors and hence requires eight. The color \(i+3j\bmod 8\) attains eight: among distinct indices differing by at most two in each coordinate, equal color occurs only at shifts \(\pm(2,2)\).

For \(D=1\) and \(a\cdot b=0\), a putative seven-coloring has to identify both pairs of opposite corners of every \(3\)-by-\(3\) block, since no other pairs may repeat. These identities force periods \((2,2)\) and \((2,-2)\). The period subgroup has index eight in \(\mathbb Z^2\), with quotient map \((i,j)\mapsto(i-j\bmod 4,j\bmod2)\). The seven nonzero quotient elements have forbidden difference representatives
\[
(1,0),\ (2,0),\ (-1,0),\ (0,1),\ (1,1),\ (-1,1),\ (-2,1).
\]
Translation invariance makes the quotient graph a clique, so seven is impossible. The same \(i+3j\bmod8\) coloring as in the acute case is a valid eight-coloring.

## Persistence under curved periodic deformations

Suppose both heights are strictly above \(1/2\), and let \(F\) be a homeomorphism commuting with the lattice translations and equal to the identity in a fixed open neighborhood of every lattice vertex. For all sufficiently small \(\sup_x\|F(x)-x\|\), the exact same color counts apply to the tiles \(F(T_{ij})\). For the lower bounds, each conflict used above admits strict witnesses on both sides of norm one in the original tile interiors. There are finitely many offsets; periodicity and connectedness preserve those conflicts after a sufficiently small deformation. The combinatorial lower bounds use only presence of those conflicts, not absence of the other edges.

For the upper bounds, pairs with an index difference at least three in one coordinate have a uniform positive gap above one, by the strict height assumption. For \(D<1\) there is also a uniform gap below one inside a tile. For \(D=1\), the remaining critical upper-bound pairs are within one tile (largest distance one on closures) and between tiles offset by \((2,2)\) or \((-2,-2)\) (smallest distance one on closures in the reflected index convention). Within one closed tile, norm-one pairs can occur only at opposite vertices of a longest diagonal. This follows from strict convexity in either point when the other is fixed. Between the two closed tiles the nearest displacement is uniquely the vector on the corresponding longest diagonal, since its two nonnegative coefficients are at least one and the generators have nonnegative dot product. The extremizing pair is again a pair of vertices. Outside the product of the fixed vertex neighborhoods, compactness gives a positive gap for each of these finitely many pair types. Inside those neighborhoods the map leaves both points unchanged, and the original half-open convention excludes equality. Hence the stated upper colorings transfer. Periodic perturbations supported near the interiors of edges, away from vertices, can give curved tile boundaries.

## Scope

This computes the exact minimum for tile-constant colorings in the stated family, not the Hadwiger–Nelson chromatic number of the plane. In particular it excludes six colors here without requiring periodicity of the color assignments. [Sokolov–Voronov, Theorem 2](https://arxiv.org/html/2502.01958v1) already excludes six colors for polygonal map colorings, which is a much broader polygonal class; the additional conclusions here are the sharp values 8 and 9 for these grids and stability for the specified curved deformations. Compare the off-diagonal six-color constructions of [Mundinger–Pokutta–Spiegel–Zimmer](https://arxiv.org/abs/2404.05509), which impose a different forbidden distance in one color. No claim of exhaustive priority is made.
