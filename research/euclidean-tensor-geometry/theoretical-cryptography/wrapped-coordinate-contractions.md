# Wrapped-Gaussian leakage under metric and coordinate contractions

Let \(\mathbb T=\mathbb R/\mathbb Z\), with distance \(d_{\mathbb T}(x,y)=\min_{z\in\mathbb Z}|x-y+z|\) and probability Haar measure. For \(s>0\), let \(h_s\) be the circle density of real Gaussian width \(s\) reduced modulo \(\mathbb Z\); the unwrapped density is \(s^{-1}\exp(-\pi x^2/s^2)\). On \(\mathbb T^D\) use any product \(H(y)=\prod_{j=1}^D h_{s_j}(y_j)\). Given a finite labeled set of shifts \(A=(a_i)\) and fixed nonnegative weights \(w_i\), let
\[
       W_H(A,w)=\int_{\mathbb T^D}\max_i w_i H(y-a_i)\,dy .                 \tag{1}
\]
With prior weights summing to one this is an average posterior guessing probability in the standalone additive observation model; with unit weights its logarithm is the worst-case channel leakage bound used for min-entropy estimates. The claims below give positive statistical bounds for specified noise and support geometries, not a claim about a cryptographic scheme or computational problem.

**Theorem.**
1. If for every coordinate \(j\) and labels \(i,\ell\),
   \[
       d_{\mathbb T}(b_{ij},b_{\ell j})\le
       d_{\mathbb T}(a_{ij},a_{\ell j}),
   \]
   then \(W_H(B,w)\le W_H(A,w)\) for all priors, weights and widths. In particular the statement applies to every geodesic contraction on a circle.
2. On the square torus with equal widths \(s\), decreasing only the total geodesic distance is **not** enough, even for two equally weighted labels. Let \(a=(1/12,1/12)\) and \(b=(1/9,0)\). Then \(d(0,b)<d(0,a)\), but for every \(s\) with \(e^{-\pi s^2}\le 1/1000\),
   \[
                 W_H((0,b),(1,1))>W_H((0,a),(1,1)).
   \]
   For sufficiently small \(s\) the inequality is reversed.
3. On one circle with unit weights and \(n\ge2\) labels, the unconstrained maximum is attained exactly at equally spaced centers, up to rotation and relabeling. If the centers must lie in a common arc of length \(0\le L\le1\), the exact maximum is
   \[
       F_s(1-L_0)+(n-1)F_s(L_0/(n-1)),\qquad
       L_0=\min(L,1-1/n),\quad F_s(g)=2\int_0^{g/2}h_s(t)\,dt.             \tag{2}
   \]
   In particular the bound accounts for a finite number of possible labels, rather than replacing their support by an entire continuous ball.

**Prior and application scope.** The unwrapped distance comparison underlying this question is closely related to Gaussian versions of the Kneser–Poulsen phenomenon, such as [Aishwarya and Li, *The Kneser–Poulsen Phenomena for Entropy*](https://doi.org/10.1093/imrn/rnaf140), which compares convolution entropy in Euclidean space, and [Bezdek and Connelly, *On the weighted Kneser–Poulsen conjecture*](https://pi.math.cornell.edu/~connelly/Slepian-2.pdf). The envelope in (1), on a number-field quotient torus, is the integrand in the no-leakage-to-noisy-observation min-entropy comparison of [Lin, Wang, Zhuang and Wang, *Hardness of Entropic Module-LWE*, Lemmas 10 and 14 and Corollary 3](https://pure.tudelft.nl/ws/portalfiles/portal/186654080/1-s2.0-S0304397524001683-main.pdf). We isolate what pairwise geometry controls in the orthogonal-product wrapped model. No higher-dimensional Euclidean Kneser–Poulsen volume result or new hardness theorem is asserted; nor is coordinatewise contraction claimed to be necessary.

## 1. Circle arcs with unequal radii

A helpful elementary fact is that a contraction \(a_i\mapsto b_i\) in the circle distance cannot increase the measure of a union of arcs of respective fixed radii \(r_i\). Allow empty or whole-circle arcs; endpoint conventions are immaterial to length. If the original union has full measure there is nothing to prove. Otherwise select a cut in an open gap and lift the original arcs to intervals with centers \(a'_i\in(0,1)\), all contained in that interval.

Order the \(a'_i\) from left to right and choose lifts \(b'_i\in\mathbb R\) successively, always following a shortest arc from the previous target center. If source centers coincide, their targets coincide and take the same lift. For adjacent labels in this order,
\[
 |b'_{i+1}-b'_i|=d_{\mathbb T}(b_{i+1},b_i)
                  \le d_{\mathbb T}(a_{i+1},a_i)
                  \le a'_{i+1}-a'_i .
\]
The triangle inequality along the order gives \(|b'_i-b'_\ell|\le|a'_i-a'_\ell|\) for all labels. The lift need not preserve their order.

Split the original real interval union into its connected components. For a group of intervals in one such component its length is
\(\max_{i,\ell}(|a'_i-a'_\ell|+r_i+r_\ell)\), the diameter of the union; \(i=\ell\) is allowed. The convex hull length for the same group of lifted target intervals is no larger by the pairwise lift inequality, whether or not that union is connected. Summing over the original components bounds the whole lifted target union length by the original measure, and projection onto the circle cannot increase length. This proves the fact for unequal radii and arbitrary label maps, without assuming continuous motion or a shared cut for source and target arcs.

By Poisson summation \(h_s(x)=\sum_{k\in\mathbb Z}\rho^{k^2}e^{2\pi i kx}\) with \(\rho=e^{-\pi s^2}\). The [Jacobi product for \(\theta_3\)](https://dlmf.nist.gov/20.5.E3) gives factors \(1-\rho^{2n}\) and \(1+2\rho^{2n-1}\cos(2\pi x)+\rho^{4n-2}\), \(n\ge1\). They are positive and the second type is strictly decreasing on \(0\le x\le1/2\). The convergent positive product is strictly decreasing too (use the ratio of the first such factor and bound every other ratio by one). The superlevel sets of \(w_i h_s(x-a_i)\) are therefore arcs centered at \(a_i\), empty, or the whole circle, with radii dependent only on the level and \(w_i\). Integrating their union measure over the level by the layer-cake formula proves the weighted circle case of part 1.

For the product, change one coordinate of the centers at a time. At each fixed value of the other output coordinates, all of their kernel factors multiply each \(w_i\) by a fixed nonnegative number, identical before and after this one-coordinate change. Apply the weighted circle inequality and integrate the other coordinates. This proves the product statement. The argument also works with arbitrary nonnegative circle kernels whose superlevel sets are centered arcs; the Gaussian form is needed for the explicit square-torus reversal and the strictness asserted in the spacing result.

## 2. A strict square-torus reversal

For two unit-weight labels (1) is \(1+\tfrac12\|H-\tau_z H\|_1\), where \(\tau_z\) is translation by \(z\); write \(D_s(z)\) for the total variation term. For \(0<\rho=e^{-\pi s^2}\le10^{-3}\) the one-dimensional Fourier tail beyond \(k=\pm1\) is at most
\[
             2\sum_{k\ge2}\rho^{k^2}\le 2\rho^4/(1-\rho^5)\le3\rho^4 .
\]
Thus the two-dimensional density equals \(1+2\rho(\cos(2\pi x)+\cos(2\pi y))+R(x,y)\), with
\(\|R\|_\infty\le4\rho^2+6(1+2\rho)\rho^4+9\rho^8\le 5\rho^2\). Subtract a translate, apply the reverse triangle inequality in \(L^1\), and use the sine difference identity. For independent uniform angles \(U,V\) this gives
\[
 \left|D_s(z)-2\rho\,\mathbb E\big|
                 \sin(\pi z_1)\sin U+\sin(\pi z_2)\sin V
                             \big|\right|\le5\rho^2.                   \tag{3}
\]
Now \(\mathbb E|\sin U|=2/\pi\), and
\(\mathbb E|\sin U+\sin V|=8/\pi^2\): use \(2\sin((U+V)/2)\cos((U-V)/2)\), whose two absolute factors are independent under Haar on the angle torus modulo \(\pi\). Indeed the linear map to that torus is a surjective group homomorphism and maps Haar to Haar. The leading expectation in (3) is \((2/\pi)\sin(\pi/9)\) for \(b\), and \((8/\pi^2)\sin(\pi/12)\) for \(a\). Their difference exceeds \(7/1000\). To certify the sign, the first is at least \(2/9-10/2187\) by \(\sin x\ge x-x^3/6\) and \(\pi^2<10\); the second is at most \(2(2450/1000-1414/1000)/(986/100)\) by \(\sqrt6<2450/1000,\sqrt2>1414/1000,\pi^2>986/100\). Rational subtraction gives the asserted lower bound. The finite remainder error on the difference of \(D_s\)'s is at most \(10\rho^2\), so \(D_s(b)-D_s(a)>0\) on the stated width range. Meanwhile \(d(0,b)^2=1/81<1/72=d(0,a)^2\).

For clarity, the small-width ordering can be checked on any fixed full lattice torus. Let \(g_s\) be the unwrapped spherical Gaussian density and \(z\) a shift with geodesic length \(d_0=\min_{\lambda\in\Lambda}\|z+\lambda\|>0\). Write \(I_s\) for the overlap, \(1-D_s(z)\). For a shortest representative \(v\), data processing by wrapping gives a lower bound
\(I_s\ge2\overline\Phi(\sqrt{2\pi}\|v\|/(2s))\), using the Euclidean bisector formula for two equal-covariance Gaussians. Also \(\min(\sum_i p_i,\sum_j q_j)\le\sum_{i,j}\min(p_i,q_j)\) for nonnegative sequences, because if the first total is smaller then summing the pointwise bounds \(\sum_j\min(p_i,q_j)\ge p_i\) gives the claim. Apply this inequality to the two periodized densities and integrate on a fundamental domain. Grouping pairs of periods by their difference unfolds the integral, giving
\[
    I_s\le\sum_{\lambda\in\Lambda}
          2\overline\Phi(\sqrt{2\pi}\|z+\lambda\|/(2s)).
\]
The logarithmic leading rate of both bounds is \(s^2\log I_s\to-\pi d_0^2/4\), by the Gaussian tail rates and lattice summability. Explicitly the upper bound is at most \(2\exp(-\pi d_0^2/(4s^2))\sum_\lambda\exp(-\pi(\|z+\lambda\|^2-d_0^2)/4)\) for \(s\le1\); the sum is finite and independent of \(s\). The shorter \(b\) has larger overlap than \(a\) for small enough \(s\) and hence smaller \(D_s\), as claimed. This endpoint comparison does not assert a unique crossover.

## 3. Sharp one-circle finite support bound

In the unit-weight case the maximum density at a point comes from a closest center. Order the labeled centers around the circle and write \(g_1,\ldots,g_n\) for the cyclic gaps, permitting zeros. On each gap the closest-center distance is the minimum of the distances along that gap to the two endpoints. Any path to another center is at least as long as the distance to one of these endpoints. Hence (1) equals \(\sum_i F_s(g_i)\). The function \(F_s\) is strictly concave on \([0,1]\) since \(F_s'(g)=h_s(g/2)\) strictly decreases. Jensen gives the unconstrained result and its equality case. 

Containment in an arc of length \(L\) is equivalent to there being a gap of length at least \(1-L\). For a fixed such gap \(g\), Jensen maximizes the contributions of the other gaps by setting them equal to \((1-g)/(n-1)\). The resulting function is nonincreasing for \(g\ge 1/n\), since its derivative is \(F_s'(g)-F_s'((1-g)/(n-1))\le0\). This gives (2), and the listed gap sizes are attained by equally spacing the centers along the arc of length \(L_0\) including its endpoints. The case \(L=0\) gives a single distinct center and envelope one.

**Replay.** Run `python3 verify-wrapped-coordinate-contractions.py`. It tests the arc inequality on finite exact rational configurations, the equal-weight gap optimization on a rational grid, and the rational signs in the broad-width reversal. No actual system or samples from a deployed protocol are considered.
