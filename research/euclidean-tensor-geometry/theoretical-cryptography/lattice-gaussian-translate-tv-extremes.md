# Exact total variation extremes for a lattice Gaussian and its translate

**Scope:** comparison of two abstract probability laws on the same infinite Euclidean lattice. There is no reduction modulo a finite ring, cryptosystem, secret, or algorithmic claim.

## 1. Sharp bounds at every width

Let \(P\) assign mass proportional to \(e^{-\|x\|^2/2}\) to \(x\) in a full-rank Euclidean lattice \(\Lambda\). Let \(Q=P+v\) for nonzero \(v\in\Lambda\), and put \(t=\|v\|\), \(a=t^2/2\), \(q=e^{-a/4}\). Define the periodized Gaussian
\[
             \Theta_a(x)=\sum_{j\in\mathbb Z}e^{-a(j+x)^2}.
\]
Then, in every dimension,
\[
 \boxed{\qquad
  \frac{1+q}{\Theta_a(0)+\Theta_a(1/2)}
   \ \le\ \operatorname{TV}(P,Q)\ \le\ \frac{1}{\Theta_a(0)}.
   \qquad}                                               \tag{1}
\]
No smoothing or lattice-shape hypothesis is required. Both endpoints are exact:

* The upper endpoint occurs exactly when \(\Lambda=\mathbb Z v\perp(\Lambda\cap v^\perp)\).
* The lower endpoint occurs exactly when
  \(\Lambda=\mathbb Z (v/2)\perp(\Lambda\cap v^\perp)\).
* If \(v\) is required to be primitive, the lower endpoint remains the infimum in every dimension at least two, but is never attained.

For weights \(e^{-\|x\|_M^2/2}\) with \(M\succ0\), the same result holds with \(t=\sqrt{v^TMv}\), and orthogonal sums are understood in the \(M\) inner product. Under the usual lattice-width convention \(e^{-\pi\|x\|^2/s^2}\), \(a=\pi\|v\|^2/s^2\).

If the initial center is arbitrary rather than a lattice point, the lower bound in (1) need not hold. In that case the exact unrestricted interval is instead \([q/\Theta_a(1/2),\,1/\Theta_a(0)]\). Both endpoints come from a primitive orthogonal line with the initial center at, respectively, a half-step or a lattice point in that line.

## 2. Reduction to a circular phase law

Write \(v=d v_0\) for \(d\ge1\) and \(v_0\) primitive. The projection of \(\Lambda\) onto \(v^\perp\) is a full-rank lattice \(\Gamma\) in that subspace, as can be seen by extending \(v_0\) to an integral basis. Choose a linear section on this projected basis. A fiber over \(y\in\Gamma\) has \(d\) progression classes modulo \(\mathbb Z v\), whose normalized axial offsets modulo 1 are \(\ell(y)+j/d\), \(j=0,\ldots,d-1\), for a real linear functional \(\ell\). Consider the phase measure \(\mu\) obtained by drawing \(y\) with weights \(e^{-\|y\|^2/2}\) on \(\Gamma\), and choosing these \(d\) offsets uniformly. For every integer \(k\) its Fourier coefficient is
\[
 \widehat\mu(k)=\mathbf1_{d\mid k}
    \frac{\sum_{y\in\Gamma}e^{-\|y\|^2/2}e^{-2\pi i k\ell(y)}}
         {\sum_{y\in\Gamma}e^{-\|y\|^2/2}}\ \ge0,          \tag{2}
\]
with strict positivity when \(d\mid k\). This is Poisson summation on the centered projected Gaussian: modulating the Gaussian shifts its everywhere-positive Fourier transform. The choice of section does not affect \(\mu\).

Set \(f_a(x)=\exp(-a\,\operatorname{dist}(x,\mathbb Z)^2)\). A unimodal probability sequence \((p_j)\) on \(\mathbb Z\) has TV distance to its one-step shift equal to \(\tfrac12\sum_j|p_j-p_{j-1}|=\max_j p_j\), by telescoping on both sides of the maximum. On each progression along \(v\), this distance is \(f_a(x)/\Theta_a(x)\), where \(x\) is its phase. The two distributions have equal marginal weight on each progression, proportional to its transverse Gaussian times \(\Theta_a(x)\). Thus
\[
                 \operatorname{TV}(P,Q)
                       =\frac{\int f_a\,d\mu}{\int\Theta_a\,d\mu}.          \tag{3}
\]
Equivalently, it is the mass of the axial slab \(-t/2\le\langle X,v/t\rangle<t/2\), by the likelihood comparison between \(x\) and \(x-v\).

For \(0\le x\le1/2\), the function \(\Theta_a(x)/f_a(x)=\sum_{j\in\mathbb Z} e^{-a j^2+2a j x}\) is strictly increasing away from 0 by pairing \(j,-j\). The ratio in (3) therefore lies between the two extrema \(q/\Theta_a(1/2)\) and \(1/\Theta_a(0)\), even for phase laws without (2). It reaches the upper endpoint exactly when all phases in the lattice are zero modulo 1, which is the asserted primitive orthogonal decomposition. The sharper centered lower bound needs (2) and the following comparison.

## 3. A strict chord inequality for two theta functions

For \(x\in[0,1/2]\) put
\[
   U_a(x)=e^{a x^2}\Theta_a(x)=\sum_{j\in\mathbb Z} e^{-a j^2+2a j x},
   \qquad
   V_a(x)=e^{a x^2}\Theta_a(x+1/2)=\sum_{j\in\mathbb Z+1/2} e^{-a j^2+2a j x}.
\]
Here \(V_a\) is strictly increasing on \(x>0\). The function \(U_a\), viewed as a function of \(V_a\), is strictly convex on the interior, for every \(a>0\). We prove this by showing that \(U_a'(x)/V_a'(x)\) is strictly increasing.

**Start at large \(a\).** Put \(z=ax\) and \(H(y)=y\coth y\). This function is increasing, satisfies \(H'(y)\le1\), and \(H(y)\le1+y^2\) for positive \(y\). For the derivative bound use \(e^{-y}\sinh y\le y\); for the last inequality differentiate \((1+y^2)\sinh y-y\cosh y\). The logarithmic derivative \(U_a''/U_a'\) is an average of \(2aj\coth(2ajx)\) over integers \(j\ge1\), with positive weights, so is at least \(2a\coth(2z)\). In \(V_a''/V_a'\), the terms have half-integer indices \(j/2\) for positive odd \(j\); the smallest term has slope \(a\coth z\). For the \(j\)-th term the excess over that slope is at most \(2j^2 a\tanh z\). Indeed \(H(jz)-H(z)\le j^2z^2\) for \(z\le1\), and is at most \((j-1)z\) when \(z\ge1\). Use \(\tanh z\ge z/2\) in the first range and \(\tanh z\ge1/2\) in the second, then divide by \(x\). The ratio of its weight in \(V_a'\) to the \(j=1\) term is
\[
    j e^{-a(j^2-1)/4}\frac{\sinh(jz)}{\sinh z}
       \le j^2 e^{-a(j-1)^2/4},
\]
because \(\sinh(jz)/\sinh z\le j e^{(j-1)z}\) and \(z\le a/2\). Consequently, for all sufficiently large \(a\), the total excess in \(V_a''/V_a'\) is less than \(a\tanh z\), uniformly on \(0<x\le1/2\). The identity \(2\coth(2z)=\coth z+\tanh z\) proves the desired strict inequality of logarithmic derivatives at this initial width.

**Propagate to every \(a\).** Use time \(b=1/a\) and treat \(U,V\) as functions of \((b,x)\). Both exponential series solve \(F_b=F_{xx}/4-(x/b)F_x\). Thus \(U_x,V_x\) solve the differentiated equation with the additional zero-order term \(-F_x/b\). If \(R=U_x/V_x\), \(W=R_x\), and \(\beta=V_{xx}/(2V_x)-x/b\), division followed by differentiation gives
\[
       R_b=\tfrac14R_{xx}+\beta R_x,\qquad
       W_b=\tfrac14W_{xx}+\beta W_x+\beta_x W.              \tag{4}
\]
The boundary \(x=0\) has \(W=0\), since \(R\) is even and analytically extends there by canceling a common first-order zero. At \(x=1/2\),
\[
 \frac{U_{xx}}{U_x}-\frac{V_{xx}}{V_x}
 =\frac1a\left(\frac{\Theta_a''(1/2)}{\Theta_a(1/2)}
              -\frac{\Theta_a''(0)}{\Theta_a(0)}\right)\ge0.
\]
The nonnegativity follows because the periodized Gaussian is minimized at \(1/2\) and maximized at 0. For example, Poisson summation and the [Jacobi product](https://dlmf.nist.gov/20.5) express \(\Theta_a\) up to a positive factor as a product of positive factors increasing in \(\cos(2\pi x)\).

On a compact positive time interval, \(V_x\) has a simple zero at \(x=0\) with positive leading coefficient. It follows that \(\beta_x=-1/(2x^2)+O(1)\) as \(x\downarrow0\), so \(\beta_x\) is bounded above uniformly over this interval. Choose \(C\) greater than that upper bound and apply the minimum argument to \(e^{-Cb}W\) in (4). A negative minimum would be at an interior spatial point, away from the singular boundary, where the differential equation contradicts the signs of the derivatives. The nonnegative boundaries and positive initial condition therefore give \(W\ge0\). The interior strong maximum principle gives \(W>0\) in positive later time since it is positive initially. Taking any finite later time proves the asserted strict convexity for every \(a>0\).

Let \(A_0=\Theta_a(0)\) and \(A_1=\Theta_a(1/2)\), so \(A_0>A_1\). The endpoints of the graph just considered are \((V,U)=(A_1,A_0)\) and \((A_0/q,A_1/q)\). The strict chord inequality, after multiplication by \(e^{-a x^2}\), is
\[
 f_a(x)\ \ge\ L\,\Theta_a(x)
       +B\bigl(\Theta_a(x)-\Theta_a(x+1/2)\bigr),           \tag{5}
\]
with equality only at \(x=0,1/2\bmod1\), where
\[
       L=\frac{1+q}{A_0+A_1},\qquad
       B=\frac{A_1-q A_0}{A_0^2-A_1^2}>0 .
\]
Positivity of \(B\) also follows from the strict increase of \(U_a\). Periodicity and reflection extend (5) over the circle.

## 4. Integration, equality and the primitive limit

The shift \(x\mapsto x+1/2\) multiplies the \(k\)-th Fourier coefficient of \(\Theta_a\) by \((-1)^k\). Its Fourier coefficients are all positive, so (2) implies
\(\int(\Theta_a(x)-\Theta_a(x+1/2))\,d\mu\ge0\). Integrating (5) in (3) proves the lower bound of (1).

Equality requires that \(\mu\) be supported on \(\{0,1/2\}\) and give the two points equal weight: the first follows from strictness in (5) and the second from the integral of the theta difference. If \(d=1\) then \(\widehat\mu(1)>0\), excluding equal weights. If \(d>2\), the phase progression over \(y=0\) already has more than two points. Thus equality forces \(d=2\) and every lattice point to have axial projection in \(\mathbb Z(v/2)\). Those two conditions are exactly the orthogonal decomposition in the lower endpoint statement, which also suffices.

The primitive infimum is approached by the planar lattices
\[
     \Lambda_h=\mathbb Z(t,0)+\mathbb Z(t/2,h),\qquad v=(t,0),\qquad h\downarrow0 .
\]
The two phases have weights proportional to the Gaussian masses of the even and odd all-integer transverse indices. Their normalized imbalance is
\[
 \frac{\sum_{k\in\mathbb Z}(-1)^k e^{-h^2 k^2/2}}
      {\sum_{k\in\mathbb Z} e^{-h^2 k^2/2}}
      \sim 2e^{-\pi^2/(2h^2)}
\]
by Poisson summation. This gives the limiting equal phase mixture. At \(h\to\infty\) only the zero phase survives in the limit, giving the other endpoint. Continuity gives every strictly intermediate value with primitive \(v\) already in rank two. Orthogonally adding independent dimensions does not change TV. In rank one with \(v\) primitive only the upper endpoint is possible.

For an off-lattice initial center the same progression argument gives (3) with a different phase measure; (2) can fail. Taking an orthogonal primitive line and placing its center at a half-step realizes \(q/A_1\), below the centered lower endpoint because \(A_1>q A_0\). Arbitrary positive precision \(M\) reduces to the present calculation by \(M^{1/2}\).

The endpoints also have a stability interpretation on the phase circle. For fixed \(a>0\), write \(\delta(x)=\operatorname{dist}(x,\{0,1/2\}\bmod1)\). The pointwise gap in (5) is at least \(c_a\delta(x)^2\) for some \(c_a>0\). In fact the chord slope lies strictly between the limiting slopes of \(U\) as a function of \(V\) at the two endpoints. At zero, \(V(x)-V(0)\) is a positive multiple of \(x^2\) to leading order, while at \(1/2\), \(V(1/2)-V(x)\) is a positive multiple of \(1/2-x\). Strict interior comparison and compactness handle the remaining interval. Also the \(k=1\) Fourier term of \(\Theta(x)-\Theta(x+1/2)\) has positive coefficient, and all contributing phase coefficients are nonnegative. Using \(\int\Theta\,d\mu\le A_0\) in (3)–(5) proves
\[
 \operatorname{TV}(P,Q)-L
       \ \ge\ c'_a\,\mathbb E_\mu\delta(x)^2+c''_a\,\widehat\mu(1)
\]
for positive constants depending only on \(a\). Moving each phase to its nearer endpoint costs at most \((\mathbb E_\mu\delta^2)^{1/2}\) in the circle's \(1\)-Wasserstein distance. Its resulting imbalance is at most \(\widehat\mu(1)+2\pi^2\mathbb E_\mu\delta^2\), by comparison with \(\cos(2\pi x)\). Thus the distance from the phase law to the equal two-point law is \(O_a(\sqrt{\operatorname{TV}-L})\). At the upper endpoint, the strictly decreasing peak ratio has a positive quadratic deficit near zero, so the same argument gives distance to \(\delta_0\) of order at most \(O_a(\sqrt{1/A_0-\operatorname{TV}})\). These are statements about the phase law, not about metric closeness of the full lattices.

## 5. Comparisons and an exact Hellinger bound

The continuous spherical Gaussian translate has TV \(2\Phi(t/2)-1\), where \(\Phi\) is the standard normal cdf. This also results from (3) if \(\mu\) is uniform on the circle. It lies strictly between the endpoints for all \(t>0\), by strictness in (5) and strict decrease of \(f_a/\Theta_a\). Thus the continuous value is neither a universal lower bound nor a universal upper bound for lattice Gaussians.

At small \(t\) the upper endpoint is \(t/\sqrt{2\pi}\) up to an exponentially small relative correction, and the lower endpoint is \(t/\sqrt{2\pi}\,(1-t^2/16+O(t^4))\) by Poisson summation. The continuous correction is \(-t^2/24\) instead. At large \(t\), with \(q=e^{-t^2/8}\), the upper and lower endpoint deficits from 1 are respectively \(2q^4+O(q^8)\) and \(q-2q^2+4q^3+O(q^4)\).

The Bhattacharyya affinity \(A(P,Q)=\sum_x\sqrt{P(x)Q(x)}\), whose complement is squared Hellinger distance in the probability convention, has a simpler exact range. Completing the square at \(v/2\) gives
\[
        A(P,Q)=q\,\frac{\int\Theta_a(x+1/2)\,d\mu}
                         {\int\Theta_a(x)\,d\mu},
       \qquad
        q\,\frac{A_1}{A_0}\ \le\ A(P,Q)\ \le\ q .
\]
The lower bound follows from the minimum and maximum of the two theta functions, with equality on the primitive orthogonal line. The upper follows from (2) or maximal Gaussian mass at lattice centers. In lattice form the ratio is the shifted mass at \(v/2\) divided by the centered mass; equality occurs exactly when \(v/2\in\Lambda\), by the strictly positive dual Gaussian weights. That is weaker than the TV lower-equality condition.

## 6. Prior work and limitations

[Agrawal–Gentry–Halevi–Sahai, Lemma 6 and its proof](https://eprint.iacr.org/2012/714.pdf) identify the axial slab and use a smoothing premise to obtain an error-function upper bound on the translation discrepancy. The unwrapped exact two-sided extremal problem here does not assume smoothing. [Regev–Stephens-Davidowitz](https://arxiv.org/abs/1502.04796) also give general identities and inequalities for periodic Gaussian masses; the specific chord comparison of §3 involves a different pair of normalized heat kernels. The calculation does not extend the bounds unchanged under modular wrapping, changing the covariance between \(P\) and \(Q\), or using off-lattice centers in the centered lower bound. The adjacent checks use only fixed synthetic theta sums and lattice examples; the all-width claim is proved by the parabolic argument. The verifier reports 7,800 exact and 25,516 numerical checks.
