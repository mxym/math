# Exact Gaussian discretization when the unknown center is an integer

Write \(g_t(x)=t^{-1}e^{-\pi x^2/t^2}\), and let \(D_s(n)=e^{-\pi n^2/s^2}/Z_s\) on \(\mathbb Z\), where \(Z_s=\sum_{n\in\mathbb Z}e^{-\pi n^2/s^2}\). An observation has law \(X=\theta+G_t\) for an unknown integer \(\theta\), with \(G_t\) of density \(g_t\). Is there one Markov kernel, given \(X\) but not \(\theta\), whose output has law \(\theta+D_s\) for every integer \(\theta\)? Exact equality of these specified probability laws is required, not statistical closeness. No computational or equivariance restriction is imposed.

**Theorem.**
* If \(s\le t\) there is no such kernel. For all sufficiently large \(t\), there is no such kernel whenever \(s^2\le (1+1/50)t^2\).
* For every \(\epsilon>0\), once \(t\) is sufficiently large as a function of \(\epsilon\), such a kernel exists for every \(s^2\ge(3/2+\epsilon)t^2\).
* The two bounds are also valid on the orthogonal integer lattice \(\mathbb Z^d\), with isotropic input and centered product discrete Gaussian target, at the same one-coordinate widths. The necessary bound follows by keeping other centers zero and marginalizing, and the sufficient bound by independent product kernels.

The exact width ratio between these bounds, including the endpoint \(3/2\), is not determined here. Widths refer to the exponent convention above; actual continuous variance is \(t^2/(2\pi)\).

**Prior and scope.** [Peikert, *An Efficient and Parallel Gaussian Sampler for Lattices*, Theorem 3.1 and §4.1](https://web.eecs.umich.edu/~cpeikert/pubs/pargauss.pdf) and [Lyubashevsky–Peikert–Regev, *A Toolkit for Ring-LWE Cryptography*, §2.4.2](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf) give positive statistically approximate discretization by ordinary Gaussian rounding. [Jia et al., *Hardness of Module-LWE with Semiuniform Seeds from Module-NTRU*, §1.1](https://doi.org/10.1049/2023/2969432) discusses discrete-noise extensions of a continuous-noise model. In this repository, [Gaussian rounding when the center is unavailable](center-blind-gaussian-rounding.md) proved that exact conversion is impossible if the unknown center ranges over any nonempty open set. An integer parameter set has no finite accumulation point, so that argument does not imply the obstruction here; in fact the second part shows exact conversion is possible with added variance. This is an unwrapped comparison of abstract statistical experiments. It does not establish a computationally efficient exact sampler, any claim about exact conversion for finitely many centers or modulo a finite lattice, or any cryptographic hardness or attack claim.

## 1. Reduction to a period-one partition of unity

Assume that a Markov kernel \(K(n\mid x)\) has the stated property. Its translation averages
\[
 K_J(n\mid x)=\frac1{2J+1}\sum_{j=-J}^J K(n+j\mid x+j)
\]
retain the property, by testing the original kernel at center \(\theta+j\). Each fixed integer translation changes the average by \(O(J^{-1})\) uniformly over \(x,n\), from the endpoints of the averaging interval.

For each \(n\) the functions \(K_J(n\mid\cdot)\) belong to the unit ball of \(L^\infty(\mathbb R)\). Weak-star compactness and the separability of \(L^1(\mathbb R)\) give a subsequence converging in that topology for all \(n\), by diagonal extraction. The limits \(K_\infty(n\mid x)\) are nonnegative; every finite sum over \(n\) is at most one almost everywhere. Weak-star testing by \(g_t(x)\) fixes each output mass under center zero, so
\(\int g_t(x)\sum_n K_\infty(n\mid x)\,dx=1\).
Since \(g_t\) is everywhere positive the sum is one almost everywhere. Translation of the test function is allowed in \(L^1\), so the endpoint bound implies exact translation equivariance in the weak-star limit. All equivariance relations and normalization hold simultaneously outside a countable union of null sets (which may be closed under integer translations).

Set \(k(w)=K_\infty(0\mid -w)\). Then \(K_\infty(n\mid x)=k(n-x)\). Conversely any nonnegative \(k\) with the following two properties gives an exact kernel:
\[
       \sum_{n\in\mathbb Z} k(x+n)=1\quad\text{a.e.},
       \qquad (g_t*k)(n)=D_s(n)\quad(n\in\mathbb Z).                     \tag{1}
\]
Thus \(k\) is a probability density (integrate its periodization) and satisfies \(\widehat k(j)=0\) for nonzero integer \(j\), with Fourier convention \(\widehat k(\xi)=\int e^{-2\pi i\xi w}k(w)\,dw\).

## 2. Exact samples force analytic growth

Put \(\Delta=s^2-t^2\) and define a probability law \(\nu(dw)=(Z_s/t)e^{-\pi w^2/t^2}k(w)\,dw\); normalization follows from (1) at \(n=0\). Completing the square in (1) gives its moment generating function on a mesh:
\[
 \mathbb E_\nu e^{u_n W}
       =e^{\gamma u_n^2/(4\pi)},\qquad
 u_n=2\pi n/t^2,\qquad \gamma=t^2\Delta/s^2 .                           \tag{2}
\]
If \(s<t\), this contradicts \(\mathbb E_\nu e^{uW}\,\mathbb E_\nu e^{-uW}\ge1\) at \(u=u_1\). If \(s=t\), equality in Cauchy–Schwarz forces \(\nu\) to be a point mass, and (2) places it at zero, impossible for a density.

Now \(\Delta>0\) and \(0<\gamma<t^2\). Log-convexity of the moment generating function and its values on adjacent mesh points imply for all real \(u\)
\[
     \mathbb E_\nu e^{u W}
        \le \exp(\gamma u^2/(4\pi)+\pi\gamma/(4t^4)).
\]
Indeed the secant of \(u^2\) above it at mesh spacing \(2\pi/t^2\) differs by at most \(\pi^2/t^4\). To undo the tilt, use \(e^{\pi w^2/t^2}=\mathbb E_Y e^{Yw}\) where \(Y\sim N(0,2\pi/t^2)\). Gaussian integration of the last upper bound gives
\[
    \int e^{uw}k(w)\,dw
        \le \frac{s}{Z_s}\exp(\pi\gamma/(4t^4)+\Delta u^2/(4\pi)).
                                                                        \tag{3}
\]
Here \((1-\gamma/t^2)^{-1/2}=s/t\) and \(\gamma/(1-\gamma/t^2)=\Delta\). By Poisson summation \(Z_s/s=\sum_{j\in\mathbb Z}e^{-\pi s^2 j^2}\ge1\). In particular \(\widehat k(z)\) is entire and
\[
           |\widehat k(z)|\le e^{\pi/(4t^2)}
                                 e^{\pi\Delta(\operatorname{Im}z)^2}.
                                                                        \tag{4}
\]
Entire analyticity follows by domination on each bounded complex region using two real exponential moments from (3).

## 3. An obstruction at small relative extra variance

The convolution \(f=g_t*k\) is Schwartz: its derivatives are Gaussian derivatives convolved with \(k\), and the finite moments from (3) give rapid decay bounds of every polynomial order. Poisson summation for the samples in (1) therefore gives
\[
 \sum_{j\in\mathbb Z} e^{-\pi t^2(\xi+j)^2}\widehat k(\xi+j)
   =\frac{s}{Z_s}\sum_{j\in\mathbb Z}e^{-\pi s^2(\xi+j)^2}
       \qquad(\xi\in\mathbb R).                                        \tag{5}
\]
For \(|\xi|\le1/10\), \(t\ge1\), separate \(j=0\), divide by \(e^{-\pi t^2\xi^2}\), and use \(|\widehat k|\le1\) on the real axis. The inequality
\((\xi+j)^2-\xi^2\ge j^2-|j|/5\ge4|j|/5\) for \(j\ne0\), together with \(1-s/Z_s=O(e^{-\pi s^2})\), gives
\[
 \big|\widehat k(\xi)-e^{-\pi\Delta\xi^2}\big|
                      \le C e^{-4\pi t^2/5}.                             \tag{6}
\]
All constants here are uniform for \(s\ge t\ge1\). However \(\widehat k(1)=0\) by the partition condition. The following elementary interpolation turns this mismatch into a constant-factor width obstruction.

For \(F(z)=\widehat k(z)-e^{-\pi\Delta z^2}\), interpolate at \(m\ge2\) evenly spaced real nodes in \([-1/10,1/10]\). The sum of absolute values of the Lagrange weights at \(z=1\) is at most \((11e)^{m-1}\): numerators are bounded by \((11/10)^{m-1}\), and for node \(j=0,\ldots,m-1\) the denominator is \((1/[5(m-1)])^{m-1} j!(m-1-j)!\). Sum using the binomial expansion and \((m-1)!\ge((m-1)/e)^{m-1}\). The contour formula for the interpolation remainder on \(|z|=5/2\) bounds its absolute value by a constant times
\(\sup_{|z|=5/2}|F(z)|(11/24)^m\): this is the ratio bound for the products of distances from 1 and from a contour point to the interpolation nodes. More explicitly the remainder integrand is \(F(z)/(z-1)\) times that product ratio, by Cauchy's formula and the residues at the nodes. From (4) and (6),
\[
 e^{-\pi\Delta}=|F(1)|
   \le C_1 e^{-4\pi t^2/5}(11e)^m
        + C_2 e^{(25/4)\pi\Delta}(11/24)^m.                            \tag{7}
\]
Take \(m=\lfloor 2t^2/3\rfloor\). If \(\Delta\le t^2/50\), multiplying (7) by \(e^{\pi\Delta}\) makes both right-hand terms tend to zero, since
\[
 4\pi/5-(2/3)\log(11e)>\pi/50,\qquad
 (2/3)\log(24/11)>(29/4)\pi/50 .
\]
The constants are fixed and the strict inequalities follow, for example, from \(3.14<\pi<22/7,\ \log 11<2.4,\ \log(24/11)>0.77\). This contradicts (7) for all sufficiently large \(t\). It is an obstruction for exact equality on the entire integer parameter set and not an error lower bound for approximate kernels on a finite range.

## 4. Positive exact kernels at wider ratios

Fix \(s^2/t^2>3/2\) and let \(t\to\infty\) with this ratio. Put
\[
 \beta=\Delta/s^2,\qquad L=1/\beta\in(1,3),\qquad
 v=t^2\beta,\qquad g_{\sqrt\Delta}(w)=\Delta^{-1/2}e^{-\pi w^2/\Delta}.
\]
Then \(\Delta=t^2/(L-1)\) and completing the square gives
\[
     g_t(n-w)g_{\sqrt\Delta}(w)=g_s(n)\,g_{\sqrt v}(w-\beta n).            \tag{8}
\]
We construct a bounded real perturbation \(u\) of the factor \(1\) in \(g_{\sqrt\Delta}(1+u)\), arranging two independent properties:
its nonzero periodization Fourier coefficients vanish, and \(\mathbb E\,u(\beta n+G_{\sqrt v})=0\) for every integer \(n\). The latter preserves the exact sample shape in (8).

If \(1<L<2\) put \(e_0=0\); if \(L=2+\ell\) with \(0\le\ell<1\), put \(e_0=(1+\ell)/4\). For each \(k\in\mathbb Z\setminus\{0\}\) let
\[
 \lambda_k=k+e_0\operatorname{sgn}(k),\qquad
 \mu_k=\lambda_k-L\operatorname{sgn}(k),\qquad
 b_k=e^{-\pi v(\lambda_k^2-\mu_k^2)},\qquad
 U_k(w)= e^{2\pi i\lambda_k w}-b_k e^{2\pi i\mu_k w}.
\]
Both frequency pairs have equal phases at \(\beta n\), because \(\beta L=1\), and by the choice of \(b_k\) the Gaussian damping matches. Thus each \(U_k\) has zero expectation at all those means. Also \(|U_k|\le2\), since
\(\lambda_k^2-\mu_k^2=L(2|k|+2e_0-L)>0\)
for both choices of \(e_0\).

For unknown \(c=(c_k)_{k\ne0}\in\ell^1\) take \(u=\sum_{k\ne0}c_k U_k\). The nonzero integer Fourier coefficients of \(g_{\sqrt\Delta}(1+u)\) are
\[
 h_j+\sum_{k\ne0}T_{jk}c_k,\quad h_j=e^{-\pi\Delta j^2},\quad
 T_{jk}=e^{-\pi\Delta(j-\lambda_k)^2}-b_k e^{-\pi\Delta(j-\mu_k)^2}
                   \quad(j\ne0).
\]
Let \(D=e^{-\pi\Delta e_0^2}\). We show \(\|T/D-I\|_{\ell^1\to\ell^1}\to0\) and \(\|h/D\|_1\to0\). The first terms of \(T/D\) have diagonal 1 and sum off the diagonal bounded columnwise by \(2\sum_{q\ge1}e^{-\pi\Delta(1-2e_0)q}\), which vanishes since \(e_0<1/2\). For the terms with \(b_k\):
* If \(1<L<2\), one has \(b_k\le e^{-\pi t^2(2-L)}\), \(D=1\), and the sum of the shifted Gaussian weights over \(j\) is uniformly bounded for \(\Delta\ge1\).
* If \(L=2+\ell\), each \(\mu_k\) has distance \(|e_0-\ell|<1/2\) to the closest integer. The Gaussian weights in a column sum to at most \(C_\ell e^{-\pi\Delta(e_0-\ell)^2}\) for \(\Delta\ge1\), by factoring the closest-point term. For all \(k\ne0\), \(b_k\le e^{-\pi t^2(2e_0-\ell)}\). Relative to \(D\), the column bound is
\[
 C_\ell\exp\!\left(-\pi(2e_0-\ell)
                       [t^2-\ell\Delta]\right)
        = C_\ell\exp\!\left(-\frac{\pi(2e_0-\ell)t^2}{1+\ell}\right)
        \longrightarrow0 .
\]
Here \(2e_0-\ell>0\), and \(e_0^2-(e_0-\ell)^2=\ell(2e_0-\ell)\).

The right-hand side converges to zero in \(\ell^1\) after division by \(D\), by \(j^2-e_0^2\ge (1-e_0^2)|j|\) for \(|j|\ge1\). Consequently \(Tc=-h\) has a solution with \(\|c\|_1=o(1)\) by the Neumann series. Uniqueness of this solution under the same inverse, reality of the coefficients, and symmetry under simultaneous \(j,k\) reflection imply \(c_k\) is real and \(c_{-k}=c_k\). Since \(U_{-k}=\overline{U_k}\), the resulting \(u\) is real and \(\|u\|_\infty\le2\|c\|_1=o(1)\).

It follows that \(f_0=g_{\sqrt\Delta}(1+u)\) is nonnegative and integrable. Its periodization is continuous by uniform convergence (Gaussian tail), and all nonzero Fourier coefficients vanish, so it equals the constant \(\int f_0\). Set \(k=f_0/\int f_0\) to get the first half of (1). By absolute convergence of the perturbation series, (8) and the zero-expectation property give \((g_t*f_0)(n)=g_s(n)\). The normalized density consequently gives samples proportional to \(D_s(n)\); their sum is one by the partition condition, so the second half of (1) holds exactly. This constructs an exact real Markov kernel without an efficiency assertion.

For a fixed \(\epsilon>0\), perform this construction at the fixed ratio \(s^2/\widetilde t^2=3/2+\epsilon\), where \(\widetilde t=s/\sqrt{3/2+\epsilon}\). If \(s^2\ge(3/2+\epsilon)t^2\), first add independent centered continuous Gaussian width \(\sqrt{\widetilde t^2-t^2}\) to the input (or nothing at equality). Its center remains the unknown integer and its new width is \(\widetilde t\ge t\), so the same construction works for all these target widths once \(t\) passes the fixed-ratio threshold. This proves the full sufficient statement.

**Replay.** Run `python3 verify-exact-integer-gaussian-discretization.py`. It checks the interpolation constants, exact algebra of paired frequencies, and checks finite operator norm bounds, perturbation positivity, and truncation residuals on synthetic examples. The analytic statements use the infinite operators and do not depend on numerical truncation.
