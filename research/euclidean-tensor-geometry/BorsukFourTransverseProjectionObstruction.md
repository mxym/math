# Regular contact simplex: a projection obstruction, and a cross-star odds identity

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Normalize a centered equilateral triangle to have unit radius. Its diameter is \(\sqrt3\), and divide by \(\sqrt3\) at the end for diameter-one coordinates.

## An exact 12-point obstruction to transverse projection colorings

Let \(a_1,a_2,a_3\) and \(b_1,b_2,b_3\) be unit regular triangles in orthogonal two-planes \(P,W\) of \(\mathbb R^4\). Set \(x_{ij}=-a_i/2+\sqrt3\,b_j/2\), and \(X = \{a_i\}\cup\{x_{ij}\}\). All 12 points lie on the unit sphere. Directly:
- \(d^2(a_i,a_k)=3\) if \(i\ne k\).
- \(d^2(a_i,x_{ij})=3\), whereas \(d^2(a_k,x_{ij})=3/2\) if \(k\ne i\).
- \(d^2(x_{ij},x_{k\ell})=(3/4)\mathbf1_{i\ne k}+(9/4)\mathbf1_{j\ne\ell}\).

Hence the diameter is exactly \(\sqrt3\). The unit ball is minimal since for every center \(y\) the average of the three squared distances to \(a_i\) is \(1+\|y\|^2\). The triangle is a legitimate three-contact support, not just an arbitrary selected plane.

A coloring is *projection-factored* when all nonplanar points with the same orthogonal projection onto \(W\) receive the same color, while planar points are treated freely. Every such diameter-avoiding coloring of \(X\) uses at least six colors. Indeed each column \(j\) must be monochromatic; two columns have different colors since a pair in them from different rows is diametric. Every apex \(a_i\) is diametric to one point in each column, hence may use none of their three colors. The apices require three distinct colors. Six is attainable within this restriction (one color for each column and one for each apex). Unrestricted the set needs exactly three colors: use distinct colors for the apices and a cyclic shift of those three colors for the three rows of witnesses. In particular this is not a counterexample to \(b(4)=5\).

This obstructs *every* adaptive partition factoring through the full transverse projection of all nonplanar points, even allowing radius, arbitrary discontinuities, and independent treatment of the contacts. Some planar-coordinate dependence on nonplanar points is indispensable.

The same construction works in \(\mathbb R^{2k-2}\), \(k\ge3\). Use two orthogonal unit regular simplices with \(k\) vertices each. With \(c=1/(k-1)\) use \(x_{ij}=-ca_i+\sqrt{1-c^2}\,b_j\). Then \(D^2=2+2c\); the apex \(a_i\) is diametric to all of row \(i\) and non-diametric to all other rows (squared distance \(2-2c^2\)). For witnesses indexed by \((i,j)\) and \((i',j')\), the squared distances are \(D^2[c^2\mathbf1_{i\ne i'}+(1-c^2)\mathbf1_{j\ne j'}]\). Thus projection-factored methods need \(2k=(2k-2)+2\) colors, one over the conjectural dimensional target, while the set itself needs only \(k\).

## Cross-star exclusion for the spherical boundary

For compatible unit-spherical points \(x=(u,w)\) with the contact triangle in \(P\), \(u\cdot a_i\ge-1/2\) for all \(i\). Thus \(u=\sum p_i a_i\) for a unique probability vector \(p\): explicitly \(p_i=(1+2u\cdot a_i)/3\). Consequently \(\|w\|^2=(3/2)(1-\|p\|^2)\), and two unit points with probabilities \(p,q\) obey
\[
d(x,y)^2\le3\quad\Longleftrightarrow\quad
w\cdot z+(3/2)p\cdot q\ge0.
\]
A star \(S_i\) of diametric neighbors of \(a_i\) is \(p_i=0\). Consider \(x\in S_i,y\in S_j\) for \(i\ne j\) and \(w,z\ne0\). Their only common positive coordinate is \(p_k,q_k\), where \(k\) is the third index. If their transverse angle \(\phi\) is obtuse, the distance condition implies
\[
\operatorname{odds}(p_k)\operatorname{odds}(q_k)\ \ge\ 4\cos^2\phi,\qquad
\operatorname{odds}(t)=t/(1-t).
\]
This follows by substituting \(p\cdot q=p_kq_k\), \(\|w\|=\sqrt{3p_k(1-p_k)}\) and its counterpart for \(q\).

Fix any transverse direction \(e\) and \(0<\alpha<\pi/6\). Among the six cells indexed by \(S_i\) and the two angular windows of halfwidth \(\alpha\) about \(e,-e\), at least one cell is empty in every pairwise compatible spherical set. Otherwise choose six points \(x_i^\pm\) and multiply the six cross-star inequalities \(x_i^+\) vs \(x_j^-\) for \(i\ne j\); every point contributes odds of its two complementary entries exactly once, whose product is one. This contradicts \(1\ge(4\cos^2(2\alpha))^6>1\). At \(\alpha=\pi/6\) with closed windows equality may occur: place the windows so the three transverse directions of the grid above include one endpoint in each of the two windows, separated by \(2\pi/3\). Then all six cells are inhabited, proving that threshold sharp.

A defect extension works inside the ball. Put \(\tau=(1-\|x\|^2)/3\), and \(p_i=(1+2u\cdot a_i)/3+\tau\). For \(x\) compatible with the contacts, \(p_i\ge0\), \(\sum p_i=1+3\tau\), and \(p_i=0\) exactly for a diametric neighbor of \(a_i\). For \(y\) with parameters \(\sigma,q,z\), the distance constraint is
\[
w\cdot z+(3/2)p\cdot q\ge(9/2)\tau\sigma.
\]
An \(i\)-star point with complementary coordinates \(p_j,p_k\) satisfies \(\|w\|^2=3[p_jp_k-3\tau(1+\tau)]\). For \(w\ne0\) define the fiber efficiency \(E(x)=\|w\|^2/(3p_jp_k)\in(0,1]\). For different stars and obtuse transverse angle,
\[
(p_k/p_j)(q_k/q_i)\ge4E(x)E(y)\cos^2\phi.
\]
Thus the same six-cell exclusion applies to the subset of stars with efficiency at least \(\eta\) if \(2\eta\cos(2\alpha)>1\). The inequality need not govern low-efficiency star points; indeed all three stars may contain all directions at low efficiency. Taking the full rings \(-0.7a_i+\sqrt{0.11}\,b\) for unit \(b\in W\) gives norm squared \(0.60\) and same apex squared distance 3; wrong apex squared distance \(0.90\) and cross-ring squared distance at most \(1.91\).

## Scope

This is an obstruction to a specific dimension-reduction strategy, plus a quantitative compatibility rule for contact stars. It does not close the contact-star assignment in ProofAtlas BP4-T24, and does not settle \(b(4)=5\). ProofAtlas currently describes a five-sector strict cover away from contacts and records the contact-star assignment as open: https://www.proofatlas.ai/collaboration/borsuk-problem-r4/. See https://arxiv.org/abs/2611.17375 and https://arxiv.org/abs/2611.16775 for the general bound. The local comparison baselines are the dense contact net and explicit low-radius strip, which neither require nor imply this factorization.
