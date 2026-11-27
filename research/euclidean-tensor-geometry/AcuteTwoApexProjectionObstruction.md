# Two interior projections cannot acutely extend a nearly flat symmetric spherical base

**Theorem.** Let \(S=-S\subset\mathbb R^m\) be a finite spanning set, with all sites on a sphere of radius \(R>0\) about the origin. Fix a nonempty compact set \(K\subset\operatorname{int}\operatorname{conv}(S)\). There is an \(\varepsilon>0\) such that the following configuration in \(\mathbb R^{m+1}\) cannot be acute: a labelled point within \(\varepsilon\) of each \((v,0)\), \(v\in S\), together with two further points whose projections onto \(\mathbb R^m\) lie in \(K\). Their heights are unrestricted.

For an orthogonal three-dimensional box, this excludes ten-point acute configurations obtained from its eight nearly flat corners and two added points with a fixed interior projection margin. The result also holds for boxes in any dimension and for arbitrary spanning symmetric spherical bases. It does not exclude projections approaching the boundary, other geometries, or a general ten-point acute set.

[Gerencsér–Harangi](https://arxiv.org/abs/1709.03411) use one added point in their acute construction. [Novik](https://sites.math.washington.edu/~novik/publications/cs2neighb.pdf) uses two antipodal added points for the weaker almost-acute property. The issue here is perturbation to a genuinely acute set. No publication priority is asserted.

## Compactness, the support function, and the two heights

Suppose an acute sequence exists with maximal base displacement \(\epsilon\to0\). A point inside \(\operatorname{conv}(S)\) has norm strictly less than \(R\), and compactness gives
\[
\gamma=\min_{x\in K}(R^2-\|x\|^2)>0.
\]
Choose \(\kappa=\sqrt{\gamma}/2\). If an apex \((x,t)\) had \(|t|\le\kappa\), its dot product at the apex between any two opposite original base sites would be \(\|x\|^2+t^2-R^2\le-3\gamma/4\). This persists for sufficiently small uniform base perturbations because these candidate endpoints and apices are bounded. Thus both apex heights have magnitude at least \(\kappa\).

Let \(h_S(u)=\max_{v\in S}u\cdot v\). There is \(\rho>0\) such that \(x+\rho\overline B\subset\operatorname{conv}(S)\) for all \(x\in K\), where \(\overline B\) is the unit ball. Suppose the two heights have the same sign; after reflection write the apices \(P=(x,t)\), \(Q=(y,s)\) with \(t\ge s\ge\kappa\). For \(u=x-y\), choose \(v\in S\) that minimizes \(u\cdot v\). Then \(u\cdot(v-y)\le-\rho\|u\|\). At \(Q\), the horizontal contribution to the angle subtended by \(P\) and the perturbed \(v\)-site is at most \(-(\rho-\epsilon)\|u\|\); the vertical contribution is nonpositive as \(t-s\ge0\) and the base height is at most \(\epsilon<s\). This is incompatible with acuteness, including when \(u=0\).

So relabel the apices as \(P=(x,t)\), \(Q=(y,-s)\) with \(t,s\ge\kappa\). At any perturbed base site \((b,h)\), acuteness gives
\[
 (t-h)(s+h)<(x-b)\cdot(y-b)\le (2R+\epsilon)^2 .
\]
The left side is at least \((t-\epsilon)(s-\epsilon)\), so both heights are uniformly bounded. Pass to a subsequence. The base is now the exact \(S\), the projections are still in \(K\), the heights are still positive, and all relevant angles are nonobtuse. The angle at each apex between an antipodal base pair yields
\[
 t^2\ge A=R^2-\|x\|^2,\qquad s^2\ge B=R^2-\|y\|^2.
\]
Next minimize the dot product between the apices at a base site. Central symmetry and the common radius give
\[
 ts\le R^2+x\cdot y-h_S(x+y).
\]
The ball margin gives
\[
 h_S(x+y)\ge \max\{x\cdot(x+y),\,y\cdot(x+y)\}+\rho\|x+y\|.
\]
Consequently
\[
 \sqrt{AB}\le ts\le \min(A,B)-\rho\|x+y\|\le\sqrt{AB}.
\]
Everything is equal, so \(x+y=0\), \(A=B\), and \(t=s=\sqrt{A}>0\). Thus the limiting configuration is centrally symmetric, with its pair directions spanning the full \(\mathbb R^{m+1}\). This is a necessary equality description; it is not a claim that every such symmetric limit is nonobtuse for every \(S\).

## A spanning centrally symmetric limit is impossible

For completeness write the approximate opposite pairs as \(a_i\pm u_i\), and let \(D\) be the diameter of the pair midpoints \(a_i\). Inspect the angles at the two ends of either pair, subtended by the other pair. Adding the two resulting squared-norm inequalities gives
\[
 |(a_i-a_j)\cdot u_i|+|(a_i-a_j)\cdot u_j|<\|a_i-a_j\|^2
\]
in an acute configuration. In particular \(D>0\). For a diameter-realizing difference \(b=a_i-a_j\), decompose it via any third midpoint \(a_k\) and apply this inequality to obtain \(|b\cdot u_k|<2D^2\). The bound for \(k=i,j\) already follows from one comparison. Since the limiting half-diagonals span, \(\alpha=\min_{\|z\|=1}\max_k |z\cdot u_k|\) is bounded below by a positive constant along the sequence. Hence \(\alpha D<2D^2\), impossible as all approximate pair midpoints converge to zero. This is the same rigidity inequality as in the [hypersimplex note](AcuteHypersimplexObstruction.md).
