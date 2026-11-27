# Sharp first Fourier zeros of strongly log-concave densities, with a hexagonal lift bound

A single prescribed Fourier zero puts an exact upper bound on the curvature of a strongly log-concave real density. It is attained by a truncated Gaussian, not by the optimum for an entire set of integer Fourier zeros. For the hexagonal lattice, a separate two-fiber argument significantly improves the unrestricted lift upper bound, and the natural construction from optimal scalar factors has an exact upper limit within the two-factor model.

These are statements about Euclidean probability and uniform reduction on a flat torus. They do not construct a preimage algorithm or analyze a scheme. The lift problem is from [Letwin–Reis–Rothvoss, *Strongly log-concave measures and lattices*](https://arxiv.org/abs/2610.29238); see also [the exact scalar uniform lift](strongly-logconcave-lattice-lift-sharp.md) and [the directional saturation criterion](lattice-lift-directional-saturation.md) for the distinct requirement of **all** integer Fourier zeros. For general preservation of strong log-concavity under projections, see [Saumard–Wellner, §3.2](https://pmc.ncbi.nlm.nih.gov/articles/PMC4847755/).

## 1. The sharp single-zero constant

A density \(f\) is \(\alpha\)-strongly log-concave if \(f(x)e^{\alpha x^2/2}\) is log-concave, allowing zeros. Use \(\widehat f(s)=\int f(x)e^{2\pi i s x}\,dx\). Let \(A_{\rm z}\) be the unique positive root of
\[
 J(A)=\int_0^{3/4} e^{-A x^2/2}\cos(2\pi x)\,dx=0.
 \tag{1}
\]
An exact interval certificate below gives \(5.94378<A_{\rm z}<5.94379\).

**Theorem.** If \(s\ne0\) and \(\widehat f(s)=0\), then \(\alpha\le A_{\rm z}s^2\). At equality, up to translation and null sets, the only density is the normalized
\[
 e^{-A_{\rm z}s^2 x^2/2}\,{\bf 1}_{|x|\le 3/(4|s|)} .
 \tag{2}
\]
The supremum in the smooth strictly positive class is still \(A_{\rm z}s^2\), but is not attained. The density need not be even for the upper bound or uniqueness.

**Root and cumulative sign.** Scaling and reflection reduce to \(s=1\). Multiplying \(J(A)\) by \(e^{A/32}\) makes its integrand the product of \(\cos(2\pi x)\) and \(e^{A(1/16-x^2)/2}\). The derivative of that product is positive except at isolated points, since the cosine and \(1/16-x^2\) have the same sign on \((0,3/4)\). The integral therefore increases strictly. It starts negative at \(A=0\), since \(J(0)=-1/(2\pi)\), and becomes positive: the integral on any fixed inner positive subinterval of \([0,1/4)\) grows without bound after this multiplication, and the negative part is bounded in magnitude. This proves existence and uniqueness of the root.

Define
\[
 F_A(r)=\int_0^r e^{-A x^2/2}\cos(2\pi x)\,dx.
\]
Its positive-radius local minima occur at \(r=3/4+k\), \(k\ge0\). For \(A>0\) these minima strictly increase with \(k\): between consecutive ones the second half-period's cosine is the negative of the first half-period's, and the Gaussian envelope is strictly smaller. The limit at infinity is strictly positive when \(A\ge A_{\rm z}\) (already bounded below by the second local minimum). It follows that for \(A>A_{\rm z}\) the cumulative integral is positive for every \(0<r\le\infty\). At \(A=A_{\rm z}\), it is nonnegative, with exactly one zero in \(0<r\le\infty\), at \(r=3/4\).

**One-sided mixtures and equality.** Take an upper semicontinuous representative and translate a mode to zero. A bounded mode exists: for the log-concave residual, an affine supporting upper bound at an interior point supplies a Gaussian tail envelope. From strong log-concavity,
\[
 f(tx)\ge f(0)^{1-t}f(x)^t e^{A t(1-t)x^2/2},\qquad 0<t<1.
\]
Using \(f(tx)\le f(0)\) and letting \(t\downarrow0\) shows \(h(x)=f(x)e^{Ax^2/2}\le h(0)\). The log-concavity of \(h\) then makes it nonincreasing along each ray from zero. A nonnegative bounded nonincreasing function on a half-line is a positive mixture of initial-interval indicators, allowing a constant term as the interval of infinite length. This follows directly by taking its superlevel sets (equivalently its Stieltjes measure). Apply this separately to \(h(x)\) and \(h(-x)\), \(x>0\). In the real part of the Fourier transform each component of either mixture contributes \(F_A(r)\). Interchange with the mixture is justified by the integrable Gaussian envelope. Above \(A_{\rm z}\) the real part is strictly positive, since \(f\) is a probability density.

At equality, both mixtures must use only radius \(3/4\) apart from zero-length components, so \(h\) is constant on each of the two half intervals and zero outside. If one side has height \(a_+\) and the other \(a_-\), the imaginary part is proportional to
\[
 (a_+-a_-)\int_0^{3/4}e^{-A_{\rm z}x^2/2}\sin(2\pi x)\,dx .
\]
The integral is strictly positive: match the negative interval \([1/2,3/4]\) against \([0,1/4]\) by translation through \(1/2\), where the Gaussian weight is larger, and retain the positive remainder. Hence \(a_+=a_-\), proving uniqueness and (2). Conversely (2) is strongly log-concave at the stated parameter, has the desired zero, and has no smaller positive zero by the upper bound just proved. Convolution with a centered Gaussian preserves the zero by multiplication of Fourier transforms, and approaches the sharp curvature from below: convolving an \(A\)-strongly log-concave density with variance \(\sigma^2\) gives curvature at least \(A/(1+A\sigma^2)\) by completing the square and Prékopa's theorem. Uniqueness rules out smooth strictly positive equality.

## 2. Hexagonal lifts: a stronger two-fiber obstruction

Let \(L\) be the planar hexagonal lattice scaled so \(\lambda_1(L^*)=1\). Choose a basis \(u,v\) of length \(2/\sqrt3\) and angle \(60^\circ\), and let \(z=(u+v)/3\). Write \(\mathcal A(L)\) for the supremum of the curvature of smooth strictly positive densities that reduce to Haar on \(\mathbb R^2/L\). Then
\[
 6\log 2\ \le\ \mathcal A(L)\ <\ 126/25=5.04 . \tag{3}
\]
The prior rank-one upper bound is \(8\log2\), strictly larger. The exact value inside (3) is not determined.

For the upper bound, translate a mode to zero. The modular identity for a smooth strongly log-concave density holds everywhere by Gaussian tails and continuity:
\(\sum_{\lambda\in L}f(x+\lambda)=1/\det L\).
Define
\[
 h(x)=(\det L) f(x)e^{\alpha\|x\|^2/2}\le1.
\]
As above, \(h\) is log-concave with its maximum at zero; the inequality uses the zero-fiber identity and the bound by the mode. The available total deficit in the two fibers \(z+L,-z+L\) is exactly \(2\delta\), where
\[
 q=e^{-2\alpha/9},\qquad
 \delta=\sum_{x\in z+L}e^{-\alpha\|x\|^2/2}-1.
\]
Specifically, the sum of \((1-h(x))e^{-\alpha\|x\|^2/2}\) over either fiber is \(\delta\); the Gaussian sums of the two fibers coincide by negation.

In the coordinates of \(u,v\), the nearest three vectors of \(z+L\) are
\[
 (1/3,1/3),\ (-2/3,1/3),\ (1/3,-2/3)
\]
of squared length \(4/9\), of weight \(q\). The next three are
\[
 (-2/3,-2/3),\ (4/3,-2/3),\ (-2/3,4/3)
\]
of squared length \(16/9\), of weight \(q^4\). Let \(D_0,D_1\) be the sums of the six deficits \(1-h(x)\) over the corresponding shells of the two opposite fibers (each shell contains also the three negatives). Then
\[
 q D_0 + q^4 D_1\le 2\delta. \tag{4}
\]
The origin is the midpoint of each of the three opposite pairs in the first shell. If \(x\) is a midpoint of \(x_1,x_2\), log-concavity and \(h\le1\) give
\(h(x)\ge\sqrt{h(x_1)h(x_2)}\ge h(x_1)+h(x_2)-1\).
Applying this to all three pairs and averaging gives \(h(0)\ge1-D_0/3\). The six points of the second shell form a regular hexagon whose side midpoints are exactly the six shortest lattice vectors \(\pm u,\pm v,\pm(u-v)\). For example \(u\) is the midpoint of \((4/3,-2/3)\) and \((2/3,2/3)\); the other cases follow by \(60^\circ\) rotations. Each vertex is used twice. Thus the sum of \(h\) over the shortest lattice vectors is at least \(6-2D_1\). Their Gaussian weight in the zero fiber is \(q^3\), so that fiber implies
\[
 6q^3\le D_0/3+2q^3 D_1
        \le (2/q)(qD_0+q^4D_1)
        \le 4\delta/q .
\]
Hence any such lift requires
\[
 \delta\ \ge\ \tfrac32 q^4. \tag{5}
\]
This couples the two nontrivial fibers to a third; the Gaussian envelope in a single fiber would give only \(\delta\ge0\).

For a rational certificate at \(\alpha=126/25\), the Gaussian mass in \(z+L\) is \(q\sum_k c_k(q^3)^k\), where
\(k=m^2+n^2+mn+m+n\) is a nonnegative integer, and \(c_0,c_1,c_2,c_3=3,3,6,0\) by finite enumeration. One may bound \(c_k\le9(k+1)\): the norm shell is at radius \(\|u\|\sqrt{k+1/3}\), and disjoint disks of radius \(\|u\|/2\) bound the points in that ball by \((2\sqrt{k+1/3}+1)^2\). Let \(q_l=3262/10000\), \(q_u=3263/10000\), \(w=q_u^3\). The positive Taylor series and a geometric tail bound give \(q_l<e^{-28/25}<q_u\). Summing the tail from \(k=4\) now gives the strict rational bound
\[
 \delta\ \le\ q_u\left(3+3w+6w^2
         +9w^4\left(\frac5{1-w}+\frac{w}{(1-w)^2}\right)\right)-1
 \ <\ \tfrac32 q_l^4 .
 \tag{6}
\]
This contradicts (5). Because the inequality is strict with continuous terms, the obstruction holds also on an interval of parameters immediately below \(126/25\); stronger curvature implies this smaller curvature, giving the strict supremum bound. No rotational symmetry of the lift was assumed.

## 3. What independent optimal scalar factors can certify

Let \(A=8\log2\) and \(f_*\) be the [sharp one-dimensional uniform lift](strongly-logconcave-lattice-lift-sharp.md), of support \([-1,1]\). It is useful here that \(\widehat f_*\) has no zero in \((-1,1)\). To check this directly, on \([0,1/2]\) write \(w(r)=A r e^{-A r^2/2}=-f_*'(r)\). On the other half \(-f_*'(1-r)=w(r)\). Integration by parts and pairing the two halves make the sign of \(\widehat f_*(s)\) for \(0<s<1\) the sign of
\[
 \sin(\pi s)\int_0^{1/2} w(r)\cos(2\pi s(r-1/2))\,dr .
\]
The integral is at least its value at \(s=1\), since cosine decreases on \([0,\pi]\). This latter integral is strictly positive: pair \(r\in(0,1/4)\) with \(r'=1/2-r\), where the cosine reverses sign and \(w(r')>w(r)\). Indeed
\(\log(r'/r)\ge 2(r'-r)/(r'+r)=4(r'-r)\) while the opposing contribution to the log ratio is \((A/2)(r'^2-r^2)=(A/4)(r'-r)<4(r'-r)\). This proves the claim. The signed Fourier transform convention and reflections give the same result for negative \(s\).

Suppose \(X=\sum_j b_jZ_j\) with independent \(Z_j\) of density \(f_*\), and suppose its reduction modulo the hexagonal \(L\) is uniform. Every nonzero \(a\in L^*\) has zero characteristic coefficient, so at least one \(j\) satisfies \(|\langle a,b_j\rangle|\ge1\). In particular, this is necessary for all three unoriented shortest directions of \(L^*\), whose unit representatives have pairwise absolute inner product \(1/2\). If some \(b_j\) meets the threshold for two such directions, then \(\|b_j\|^2\ge4/3\): orient the two unit vectors so both projections are positive, then their sum has norm at most \(\sqrt3\) and has pairing at least \(2\) with \(b_j\). If no vector meets two thresholds, at least three distinct \(b_j\) have length \(\ge1\), and the trace of \(\sum b_j b_j^{\mathsf T}\) is at least three. In either case
\[
 \lambda_{\max}\left(\sum_j b_j b_j^{\mathsf T}\right)\ge4/3. \tag{7}
\]
The standard strong-log-concavity bound for such a linear image, obtained by whitening its two output coordinates and using Prékopa on an orthogonal projection, is curvature at least \(A/\lambda_{\max}(\sum b_j b_j^{\mathsf T})\). Equation (7) limits **that certificate** to \(3A/4=6\log 2\). With exactly two factors spanning the plane it also limits the **actual** curvature, since the map is invertible and the log density is exactly the transported quadratic on the image of the central open square where \(f_*\) is Gaussian. We do not claim actual curvature is no higher than the certificate for more than two factors.

The two-factor bound is attainable: choose \(u=(2/\sqrt3,0)\), \(v=(1/\sqrt3,1)\) as above, and \(b_1=u,\ b_2=(0,1)\). For a dual vector \(a\), if \(\langle a,u\rangle\ne0\) it is a nonzero integer and kills the first scalar coefficient. Otherwise \(\langle a,b_2\rangle=\langle a,v\rangle\) is a nonzero integer and kills the second. The resulting product is uniform modulo \(L\) and has curvature \(3A/4\). Gaussian smoothing retains uniformity while approaching this parameter, giving the lower bound in (3).

For comparison with §1, if arbitrary scalar factors have given curvature parameters \(\alpha_j>0\), scale their coefficient vectors to \(b_j/\sqrt{\alpha_j}\). A required Fourier zero along a shortest dual direction then forces a projection of at least \(1/\sqrt{A_{\rm z}}\) in magnitude. The same argument gives \(\lambda_{\max}(\sum b_j b_j^{\mathsf T}/\alpha_j)\ge4/(3A_{\rm z})\), so this more general projection certificate is at most \(3A_{\rm z}/4\). This is not an upper bound for arbitrary projected laws' actual curvature; it identifies what the standard independent-factor certificate can establish.

**Replay.** Run `python3 verify-slc-fourier-zero-hex.py`. The verifier uses exact rational Taylor bounds for the root bracket and (6), verifies the small shifted shell counts and six midpoint identities, and makes no floating-point decisions. The extremal arguments are analytic.
