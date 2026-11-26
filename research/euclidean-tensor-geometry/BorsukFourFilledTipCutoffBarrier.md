# A filled-edge obstruction to strict cyclic tip separation

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

This note concerns the regular triangle, filled edge fibers, odds \(z=s/(1-s)\) measured from the terminal apex of an oriented edge, and diameter \(D=\sqrt3\) in [the full-edge routing theorem](BorsukFourFullEdgeSpindle.md). That theorem proves strict separation between tips of the preceding edge and main points of the outgoing edge for suitably small cutoffs under a local sphericity assumption. Here is an exact obstruction to dropping that assumption in the cross-separation step, even with independent cutoffs on the three edges. It is **not** a five-coloring obstruction.

**Proposition.** There is a compact diameter-\(D\) subset of the full filled edge locus consisting of the three apices and a sequence \((p_n)_{n\ge0}\) with \(z_n\downarrow0\). Its point \(p_n\) is on edge \(i=-n\bmod3\), and \(p_{n+1},p_n\) are diametric. For any choice of three positive cutoffs each below \(z_0\), label a point a tip if its odds are below its edge cutoff and main if above, with either label allowed at equality. At least one diametric pair consists of a preceding-edge tip and an outgoing-edge main point. This holds no matter how small the cutoffs are.

**Construction.** Put \(k=93/100,\ a=7/100\), and let \(v_n\in W\) have length \(\sqrt{k}\) and angle \(-4\pi n/5\) about a fixed reference ray. Define
\[
p_n=\frac{a_{i+1}+z_n a_i+\sqrt{3z_n}\,v_n}{1+z_n},
\qquad i=-n\bmod3.
\]
The repeated letter \(a\) as a scalar in intermediate formulas means \(7/100\); the vectors are always subscripted. Each point is on the filled fiber, strictly inside the unit sphere. If \(p,q\) are nonapex points on edges \(i,i-1\) of this form, put \(r=\sqrt{z_p/z_q}\), \(t=z_q\), and let \(\theta\) be their transverse angular difference. Multiplying the deficit identity
\[
D^2-\|p-q\|^2
=\Delta_p+\Delta_q+3\lambda_p\cdot\lambda_q+2w_p\cdot w_q
\]
by \((1+z_p)(1+z_q)/(3z_q)\) gives the exactly equivalent sign test
\[
G(r,t,\theta)
=r^2+a r^2\frac{1+t}{1+r^2 t}
+a\frac{1+r^2t}{1+t}+2kr\cos\theta. \tag{1}
\]
Here \(\lambda_p\cdot\lambda_q=s_p(1-s_q)\) and \(\Delta_p=3a z_p/(1+z_p)^2\).

Choose \(z_0=1/1000\). Given \(z_n\), choose \(r_n\in[1.35,1.36]\) such that
\(G(r_n,z_n/r_n^2,4\pi/5)=0\), and put \(z_{n+1}=z_n/r_n^2\). To check existence, write \(\kappa=-\cos(4\pi/5)=(1+\sqrt5)/4\), with \(0.809<\kappa<0.8091\) by rational squaring. At \(t=0\), \(G=(1+a)r^2+a-2k\kappa r\); its value at \(1.35\) is less than \(-0.0113\), and at \(1.36\) is more than \(0.0023\). On the entire bracket its change for \(0\le t\le1/1000\) is at most \(a t|r^2-1|(r^2+1)<0.00018\), by subtracting the two rational fractions from their values at zero. The opposite endpoint signs persist with \(t=z_n/r^2\), so continuity gives the root. Thus the odds decrease to zero and all successive pairs are exactly diametric by (1).

**All other distances.** Same-edge distances are at most \(D\) by the one-edge bound in the full-edge theorem; every apex is compatible with the entire filled edge locus. For remaining cross pairs put \(p=p_j,\ q=p_\ell\), with edges \(i,i-1\), and let \(d=\ell-j\), so \(d\equiv1\bmod3\), \(\theta=4\pi d/5\) up to sign, and \(r^2=z_j/z_\ell\). If \(d\ge4\) then \(r\ge1.35^4>2\), which gives \(G>0\) in (1) even replacing \(\cos\theta\) by \(-1\). If \(d=-2,-5,-8\), then \(\cos\theta\ge0\), again giving \(G>0\). If \(d\le-11\) then \(r\le1.35^{-11}<0.037\), and \(G\ge0.07/1.001-1.86(0.037)>0\). These exhaust the cases besides \(d=1\). Thus the union with the three apices is compact and has diameter exactly \(D\).

Since \(p_0\) is main and all sufficiently late points are tips, the first tip on the sequence follows a main point. Its edge is the preceding edge of that main point, and the pair is diametric. In particular the no-cross-diameter lemma in the spherical proof cannot hold for arbitrary filled compact sets with any three sufficiently small positive cutoffs. This does not prevent an angular spare-color repair. Indeed the example itself has three strict pieces: each terminal apex with the entire sequence on its incoming edge. In each of these compact pieces, all odds other than the apex are at most \(1/1000\), so no pair has reciprocal odds or can be diametric.
