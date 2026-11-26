# The Ekeland–Hofer–Zehnder volume inequality for every parallelotope

**Yongxian Zhang.** AI-assisted proof development and internal verification; no priority claim.

**Theorem.** For every full-dimensional parallelotope \(K\) in standard \(\mathbb R^{2n}\),
\[
c_{\rm EHZ}(K)^n\le n!\,\mathrm{vol}_{2n}(K).
\]
Here a parallelotope means any affine image of a cube, not necessarily a symplectic affine image. Equality holds for all planar parallelotopes. In dimension four it holds exactly when the six absolute symplectic pairings of the four normalized facet normals consist of a common positive value on a four-cycle and zeros on the two missing edges, with a nondegenerate pairing matrix. In every dimension \(2n\ge6\) the inequality is strict.

The only symplectic input is [Haim-Kislev's centrally symmetric facet formula, Corollary 1.2](https://arxiv.org/html/1712.03494), which is a formula for the full EHZ capacity, not an affine capacity (see also [Berezovik, Theorem 3.7](https://link.springer.com/article/10.1007/s40316-025-00251-0)). This does not settle centrally symmetric weak Viterbo in general. The unrestricted inequality is false by [Haim-Kislev–Ostrover](https://annals.math.princeton.edu/2026/203-2/p05). Symmetric Lagrangian products already admit a different Mahler/billiard argument; arbitrary parallelotopes are not necessarily symplectomorphic by linear maps to Lagrangian product parallelotopes. Bounded primary-source searches did not find the arbitrary-parallelotope theorem or the equality characterization below.

## 1. Pair and triple tests

Translate \(K\) to its center and write \(K=\{x:|\langle v_i,x\rangle|\le1,\ i=1,\ldots,2n\}\) with independent normalized normals. Let \(S_{ij}=\omega(v_i,v_j)\), \(M=1/c_{\rm EHZ}(K)\), and \(x_{ij}=|S_{ij}|/(4M)\). The facet formula expresses \(M\) as the maximum of \(\sum_{i<j}t_i t_j\omega(w_i,w_j)\), over orderings of one signed representative of each normal pair, and nonnegative weights summing to one. To obtain this normalization from Corollary 1.2, use unit normals \(n_i\), support numbers \(h_i\), set \(v_i=n_i/h_i\) and \(t_i=2|\beta_i|h_i\), and absorb the signs into the representatives. The prefactor \(1/4\) cancels the quadratic scaling. In particular two weights \(1/2,1/2\) give \(0\le x_{ij}\le1\).

Any three normals can be signed and ordered so that their three pairings in the sum are nonnegative. Indeed, choose an order with positive product of the three pairing signs (an adjacent swap reverses this product); then sign changes can make all three signs positive. Zero entries can be given temporary arbitrary signs. The two largest pairings have a common vertex. Applying weights \(1/2\) at that vertex and \(1/4,1/4\) at the others gives
\[
 2x+2y+z\le4,
\]
where \(1\ge x\ge y\ge z\ge0\) are the three magnitudes. The ordered tetrahedron has vertices \((0,0,0),(1,0,0),(1,1,0),(1,1,1)\). Cutting by this inequality removes the last vertex, creates \((1,2/3,2/3)\) and \((4/5,4/5,4/5)\), and retains the other three. Convexity gives \(x^2+y^2+z^2\le2\), with equality only at \((1,1,0)\).

We also need a slight strengthening when all three magnitudes are \(\ge1/2\). Weights \(3/8,5/16,5/16\) similarly give \(30x+30y+25z\le64\). Intersecting the ordered tetrahedron \(1\ge x\ge y\ge z\ge1/2\) with this halfspace gives six vertices:
\[
(1/2,1/2,1/2),\quad (1,1/2,1/2),\quad
(1,34/55,34/55),\quad(1,43/60,1/2),\quad
(64/85,64/85,64/85),\quad(103/120,103/120,1/2).
\]
Each has squared norm strictly less than \(9/5\). Hence the squared norm of such a triangle is at most \(9/5\); when all three magnitudes are \(<1/2\) it is at most \(3/4\).

## 2. Dimension four and equality

For \(n=2\) sum the first triangle bound over the four triangles of \(K_4\). Each edge is counted twice, so \(\sum_{i<j}x_{ij}^2\le4\). Since the three terms in the Pfaffian are products of opposite edges, \(2|ab|\le a^2+b^2\) gives \(|\mathrm{Pf}(S)|\le\sum_{i<j}S_{ij}^2/2\le32 M^2\). The determinant of the matrix of normals has absolute value \(|\mathrm{Pf}(S)|\); therefore \(\mathrm{vol}_4(K)=16/|\mathrm{Pf}(S)|\), proving the claim.

Equality forces every triangle's magnitudes to be \((1,1,0)\), so the zeros form a perfect matching and the support is its complementary four-cycle. Conversely, suppose all four supported entries have absolute value \(m>0\) and the other entries vanish. Nondegeneracy forces the two nonzero Pfaffian products to add, giving \(|\mathrm{Pf}(S)|=2m^2\). In the facet formula the objective is bounded above by \(m\,t(A)t(B)\le m/4\), where \(A,B\) are the two color classes of the four-cycle, and the pair test gives \(M=m/4\). This proves exactly the stated equality condition. For example, use normals \(e_{q_1},e_{q_2},e_{p_1}+e_{p_2},e_{p_1}-e_{p_2}\). In the planar case both the capacity formula and volume equal \(4/|S_{12}|\).

## 3. Higher dimensions

Hadamard's inequality applied to the rows of \(S\), and then arithmetic–geometric mean on squared row norms, gives
\[
 |\mathrm{Pf}(S)|\le
 \left(\frac{\sum_{i<j}|S_{ij}|^2}{n}\right)^{n/2}.
\]
Each edge of \(K_{2n}\) is in \(2n-2\) triangles, so \(\sum x_{ij}^2\le (2n)(2n-1)/3\). Combining this with \(\mathrm{vol}_{2n}(K)=4^n/|\mathrm{Pf}(S)|\) gives
\[
 \frac{c_{\rm EHZ}(K)^n}{n!\,\mathrm{vol}_{2n}(K)}
 \le \frac{[2(2n-1)/3]^{n/2}}{n!}.
\]
This is \(49/54<1\) at \(n=4\) and decreases thereafter: the ratio of successive bounds is \(\sqrt{(4n+2)/3}\,(1+2/(2n-1))^{n/2}/(n+1)<2\sqrt{(4n+2)/3}/(n+1)<1\) for \(n\ge4\), using \(n/(2n-1)\le4/7<\log 2\).

For \(n=3\), color the edges of \(K_6\) by whether \(x_{ij}\ge1/2\). Every nonmonochromatic triangle uses two mixed wedges, and each vertex is center of at most six mixed wedges, since its two color degrees sum to five. Thus there are at most 18 nonmonochromatic triangles, and at least two monochromatic triangles have squared sum \(\le9/5\). The other triangles have squared sum \(\le2\), so \(\sum x_{ij}^2\le (40-2/5)/4=99/10\). Hadamard gives a ratio at most \((33/10)^{3/2}/6<1\).

## 4. Why the affine cylinder bound cannot substitute

Choose a real normal basis with all six \(|S_{ij}|=1\) and \(|\mathrm{Pf}(S)|=3\), possible by congruence of nondegenerate alternating forms; e.g. prescribe all upper-triangular entries \(+1\) except \(S_{13}=-1\). Every switching and ordering leaves at least one subtractive edge: the all-positive skew pattern has absolute Pfaffian 1. For a fixed signed ordering, transfer the combined weights on the endpoints of a subtractive edge to one endpoint or the other. As a function of the split, the objective is convex, so one endpoint choice does not decrease it. Hence the optimum is achieved on at most three vertices, and is exactly \(1/3\) by the equal-weight triangle test. Here \(c_{\rm EHZ}=3\), \(\mathrm{vol}=16/3\) and the ratio is \(27/32\).

For any affine symplectic transformation, write the two covectors of its canonical-plane projection as \(u=\sum_i a_i v_i\) and \(v=\sum_i b_i v_i\). The image of \(K\) is the planar zonotope generated by the segments \([-(a_i,b_i),(a_i,b_i)]\); its area is \(4\sum_{i<j}|a_i b_j-a_j b_i|\). Since \(|\omega(u,v)|=1\), the triangle inequality bounds this area below by \(4/\max |S_{ij}|=4\). Every circular cylinder containing that affine image therefore has capacity at least 4, whose square exceeds \(2\,\mathrm{vol}=32/3\). This is only a lower bound on the *affine* cylindrical capacity, not on the full embedding capacity. Also all six pairings are nonzero, which precludes a linear symplectic equivalence to a Lagrangian product of polygons: the normalized normals of each polygon would give an isotropic pair.
