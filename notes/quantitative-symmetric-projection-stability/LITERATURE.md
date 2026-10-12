# Cone-volume and stability comparison

This focused comparison records which primary statements were checked and why
their hypotheses or conclusions differ from the symmetric upper-end problem.
None of the quantitative results below is imported into the supplement's
proof. The direct entry005 v2–v4 inputs are pinned separately in
[DEPENDENCIES.md](DEPENDENCIES.md). The comparison is not an exhaustive review
of the projection-body or random-simplex literature.

## Exact subspace concentration and complementary factors

K. J. Böröczky, E. Lutwak, D. Yang and G. Zhang, *The logarithmic Minkowski
problem*, J. Amer. Math. Soc. **26** (2013), 831–852,
[DOI: 10.1090/S0894-0347-2012-00741-3](https://doi.org/10.1090/S0894-0347-2012-00741-3).
The [primary author manuscript](https://www.renyi.hu/~carlos/minkowski0-prob.pdf),
Theorem 1.1, characterizes nonzero finite even Borel cone-volume measures by
subspace concentration, including complementary-subspace support at equality.
It is an existence characterization; the paper explicitly leaves uniqueness
untreated. It neither selects blocks of dimension at most two nor provides a
rate in the scalar deficit \(1/2-a(K)\).

K. J. Böröczky and M. Henk, *Cone-volume measure of general centered convex
bodies*, Adv. Math. **286** (2016), 703–721,
[DOI: 10.1016/j.aim.2015.09.021](https://doi.org/10.1016/j.aim.2015.09.021),
extends subspace concentration to centroid-zero bodies. The equality case
corresponds to complementary Minkowski factors; its U-functional consequence
has a parallelotope equality class. The
[primary author manuscript](https://www.renyi.hu/~carlos/cone-volume-bodies-advances.pdf)
was checked for these statements. The normal-block restriction to dimensions
one and two in entry005 v4 uses additional short-circuit information.

## Stability from mass on an exact subspace

K. J. Böröczky and M. Henk, *Cone-volume measure and stability*, Adv. Math.
**306** (2017), 24–50,
[DOI: 10.1016/j.aim.2016.10.005](https://doi.org/10.1016/j.aim.2016.10.005).
The numbering here is that of the
[final author manuscript dated 23 September 2016](https://www.renyi.hu/~carlos/cone-volume-stability.pdf),
not the differently numbered 2014 arXiv version.

For a centered body in \(\mathbb R^d\), Theorem 1.1 assumes an actual
\(k\)-dimensional proper subspace \(L\) with
\[
V_K(L\cap S^{d-1})>\frac{k-\varepsilon}{d}|K|.
\]
It gives a complementary-factor approximation with homothetic distance
\(O_d(\varepsilon^{1/(5d)})\) and volume distance
\(O_d(\varepsilon^{1/5})\). The constants and smallness threshold are
dimension-dependent and stated existentially. Theorem 1.2 has containment
exponent \(1/(6d)\) in the line case. Theorem 1.3 gives a parallelotope
sandwich with exponent \(1/(6d)\) from U-near-minimality. These results apply
to general convex bodies.

The premise concerns exact subspace mass. Also, U integrates the indicator of
linear independence, whereas the present invariant uses determinant magnitude
after radial rescaling. Its equality target includes arbitrary symmetric
planar factors, so U-stability is not the same endpoint statement.

## Why the exact-subspace premise cannot be supplied directly

For even integers \(p\ge4\), let
\[
K_p=\left\{x\in\mathbb R^d:\sum_i|x_i|^p\le1\right\}.
\]
The inclusions
\(d^{-1/p}[-1,1]^d\subset K_p\subset[-1,1]^d\) imply convergence to the
cube and hence \(a(K_p)\to1/2\) by the pinned continuity result.
Nevertheless, \(V_{K_p}\) has zero mass on every proper linear subspace.
Indeed, on each open coordinate octant the boundary has positive Gaussian
curvature and its Gauss map is a diffeomorphism onto the corresponding
spherical octant. The omitted coordinate-zero boundary sets have surface area
zero. Therefore \(S_{K_p}\), and hence \(V_{K_p}\), is absolutely continuous
with respect to spherical area.

Thus a small upper deficit need not provide any positive mass on an exact
proper subspace. The supplement estimates distance to blocks instead, then
recovers an actual product geometrically. This observation concerns the
hypothesis of the proof route, not the validity of a quantitative modulus.

## Inverse cone-volume stability with hyperplane symmetries

K. J. Böröczky and A. De, *Stable solution of the Logarithmic Minkowski
problem in the case of hyperplane symmetries*, J. Differential Equations
**298** (2021), 298–322,
[DOI: 10.1016/j.jde.2021.07.002](https://doi.org/10.1016/j.jde.2021.07.002).
The checked full text is
[arXiv:2101.03395v2](https://arxiv.org/html/2101.03395v2), 10 March 2021.

Theorem 1.2 assumes invariance under a Coxeter group with no nonzero fixed
points. For reducible actions it requires a quantitative tube concentration
margin at every proper invariant subspace; its support-function estimate has
Wasserstein exponent \(1/(95d)\). The margin fails at saturation of a proper
invariant product block. Arbitrary centrally symmetric planar factors need not
have the assumed Coxeter symmetries.

The introduction also uses volume-normalized unconditional vertex-truncated
cubes: cone-volume Wasserstein error is \(O_d(\varepsilon)\), while containment
loss is \(\Omega_d(\varepsilon^{1/d})\). This is a related cap-volume
mechanism. The supplement instead computes the scalar upper deficit and bounds
distance to the entire affine one-/two-dimensional product class, rather than
to a fixed cube. Example 1.4 shows weak-measure collapse under anisotropic
squeezing for volume-one bodies satisfying zero cone mass on the specified
equator. That hypothesis must be retained.

## Surface-area reconstruction

H. Abdallah and Q. Mérigot, *On the reconstruction of convex sets from random
normal measurements*, [arXiv:1402.5010v1](https://arxiv.org/html/1402.5010v1),
20 February 2014. Theorem 3.1 controls translation-adjusted Hausdorff distance
by the \(1/d\) power of a convex-dual distance between surface-area measures,
for nearby zero-mean data. Its constants depend on dimension, total surface
area and weak rotundity.

This is an inverse theorem for \(S_K\). Cone-volume data is
\(h_K S_K/d\) and contains an unknown support-function factor. The supplement
constructs the product of block projections and uses the first mixed-volume
formula directly; it does not infer surface-area closeness from cone-volume
closeness or invoke this reconstruction theorem.

## Near-constant cone density

Y. Hu and M. N. Ivaki, *Stability of the cone-volume measure with near constant
density*, Int. Math. Res. Not. **2025**, no. 6, rnaf062,
[DOI: 10.1093/imrn/rnaf062](https://doi.org/10.1093/imrn/rnaf062).
Theorem 1.1 was checked in
[arXiv:2408.06172v2](https://arxiv.org/html/2408.06172v2), 1 March 2025.
For smooth strictly convex bodies with the stated translation and mean-width
normalization, it gives an \(L^2\) estimate toward a ball proportional to the
square root of the cone-density ratio oscillation. Its input is near-constant
density and its target is spherical. Product endpoint measures can have
singular limits, so these hypotheses do not bridge the present endpoint gate.

## Projection-body and recent mixed-volume comparisons

C. Saroglou, *Volumes of projection bodies of some classes of convex bodies*,
Mathematika **57** (2011), 329–353,
[DOI: 10.1112/S0025579311001860](https://doi.org/10.1112/S0025579311001860).
Only the primary publication record and abstract were available for the
comparison. The author PDF could not be obtained. No formula or theorem from
that paper is imported, and this limited access does not establish that its
projection-body results are disjoint from the present result.

Yu-De Liu, Ge Xiong and Kai-Wen Yang, *Sharp quantitative stability for the
Minkowski first inequality via a quadratic estimate for the cone-volume
measure*, Adv. Math. **492** (2026), 110886,
[DOI: 10.1016/j.aim.2026.110886](https://doi.org/10.1016/j.aim.2026.110886).
The author names, title and publication data were verified from the publisher's
[DOI-registry deposit](https://api.crossref.org/works/10.1016/j.aim.2026.110886).
A [primary author talk announcement](https://zyxy.ecnu.edu.cn/86/ea/c36096a755434/page.htm)
describes an antipodal cone-volume quadratic estimate and strong mixed-volume
inequalities. The complete paper was not obtained, so no precise theorem,
constant or exponent from it is asserted or used.

## Source extent and limits

| Primary source | Extent of the checked material |
| --- | --- |
| Böröczky–Lutwak–Yang–Zhang, 2013 | Full author manuscript available; Theorem 1.1, complementary-support condition and stated uniqueness scope checked. |
| Böröczky–Henk, 2016 | Full author manuscript available; centered subspace concentration, equality geometry and U-functional consequence checked. |
| Böröczky–Henk, 2017 | Final author manuscript available; definition and Theorems 1.1–1.3 checked against that version's numbering. |
| Böröczky–De, 2021 | Full arXiv v2 available; Theorem 1.2, truncation comparison and Example 1.4 checked; published metadata verified independently. |
| Abdallah–Mérigot, 2014 | Full arXiv v1 available; Theorem 3.1 and dependence of inverse constants checked. |
| Hu–Ivaki, 2025 | Full arXiv v2 available; Theorem 1.1 and its normalizations checked. |
| Saroglou, 2011 | Publication record and abstract only; full-text comparison remains incomplete. |
| Liu–Xiong–Yang, 2026 | Publisher-deposited metadata and author talk description only; full-text comparison remains incomplete. |

The two full-text limits affect the breadth of the comparison. Neither paper
is a dependency of the proof. Exact arithmetic checks likewise do not validate
the infinite analytic arguments or resolve the unreviewed literature.
