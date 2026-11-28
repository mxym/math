# Sharp quadratic approach to the uniform-lift curvature from finitely many Fourier zeros

For an \(\alpha\)-strongly log-concave probability density on the real line use the convention \(f(x)e^{\alpha x^2/2}\) is log-concave, allowing zeros. Write \(\widehat f(k)=\int f(x)e^{2\pi i kx}\,dx\), and \(A=8\log 2\). Let \(C_K\) be the supremum of \(\alpha\) under the constraints \(\widehat f(k)=0\) for \(1\leq k\leq K\), and \(C_K^{\mathrm{odd}}\) the same supremum requiring only the odd indices in that range.

**Theorem.** For an absolute \(B<\infty\) and every integer \(K\geq1\),
\[
 A+\frac{1}{1024\pi^2(K+2)^2}
 \ \leq\ C_K\ \leq\ C_K^{\mathrm{odd}}
 \ \leq\ A+\frac{B}{(K+1)^2}.
 \tag{1}
\]
The suprema do not change if one requires smooth strictly positive densities. The lower bound is constructed with exactly one nonconstant high-frequency cosine in the periodized density. Both real and imaginary parts vanish at every required index; no symmetry assumption is used for the upper bound.

Thus a finite Fourier certification of either type has a sharp order-\(K^{-2}\) excess over the exact Haar-wrap bound. The leading optimal constant is not determined. The exact value \(A\) for Haar wrap, and the prior distinct problem of one Fourier zero, are in [the fixed scalar Haar-lift note](https://github.com/mxym/math/blob/95e3da5084accbc96b71426a17db92a7fd86aacf/research/euclidean-tensor-geometry/theoretical-cryptography/strongly-logconcave-lattice-lift-sharp.md) and [the first-zero note](slc-fourier-zero-hex.md). The general lift setting is [Letwin–Reis–Rothvoss](https://arxiv.org/abs/2610.29238), which imposes exact uniform periodization, rather than the finite-mode relaxation treated here. The use of the Jackson kernel is classical; the proof below uses its positive second moment to absorb the unknown peak deficit of the log-concave residual. By projection and scaling the necessary upper bound also applies on any single dual ray of a multidimensional lift: if a density of Euclidean curvature \(\alpha\) has Fourier zeros at the odd frequencies \(kv\), \(1\le k\le K\), \(v\ne0\), then \(\alpha\le\|v\|^2(A+B/(K+1)^2)\). Here Prékopa gives curvature \(\alpha\) for the unit-direction marginal before scaling by \(\|v\|\). No sampler, implementation, or cryptographic conclusion is implied.

## 1. Centered modes and a compact lower bound of the central density

It is enough to prove the upper bound for smooth strictly positive densities with \(\alpha\geq A\). Convolution with a centered Gaussian of variance \(\sigma^2>0\) preserves each Fourier zero and gives a smooth positive density of curvature at least \(\alpha/(1+\alpha\sigma^2)\). This follows by factoring out \(e^{-\alpha x^2/[2(1+\alpha\sigma^2)]}\) after completing the square in the convolution and applying Prékopa to the jointly log-concave remainder. Thus any nonsmooth violation with \(\alpha>A\) would give a smooth violation by taking \(\sigma\) small enough. The same reasoning shows that the two suprema can be approached within the smooth class.

Translate a mode to zero; the zero conditions are unchanged. Gaussian tails and existence of a mode follow by taking an affine upper support to the log-concave residual at an interior point. Write \(h(x)=f(x)e^{\alpha x^2/2}\) and \(f_0=f(0)\). Since the convex function \(-\log f-\alpha x^2/2\) has derivative zero at the mode, \(h\leq f_0\) and \(h\) is nonincreasing on each ray. Gaussian domination and the countable sums in the periodization below are therefore valid. Also \(\mathbb E X^2\leq1/\alpha\): on each half-line \(h\) is a nonincreasing weight relative to the corresponding half-Gaussian, so its covariance with the increasing squared radius is nonpositive by the two-copy formula. Hence \(\Re\widehat f(1)=0\) and \(1-\cos(2\pi x)\leq2\pi^2 x^2\) give \(\alpha\leq2\pi^2\).

There is a uniform upper bound for \(f_0\) under the first zero, even using only ordinary log-concavity. Indeed with \(a=1/8\), the expectation of \(\cos(2\pi X)\) gives \(\Pr(|X|\ge a)\ge \cos(\pi/4)/(1+\cos(\pi/4))>0\). Set \(s=a/2\). On either ray \(f(\pm s)\leq1/s\) by monotonicity and normalization. If \(s f_0>1\), log-concavity by extrapolation of the chord from 0 to \(\pm s\) gives \(f(\pm t)\le f_0(s f_0)^{-t/s}\) for \(t\ge s\). Integrating for \(t\ge a=2s\) bounds the two tails by \(2/[(s f_0)\log(s f_0)]\). This tends to zero as \(f_0\to\infty\), proving the bound. A positive lower bound for \(f_0\) holds when \(\alpha\ge A/2\), by the second moment bound centered at the mode and the fact that \(f_0\) is the maximum.

We need the following qualitative compactness consequence: there is an absolute \(c_0>0\) so that for all sufficiently large \(K\), any smooth mode-centered density with \(\alpha\ge A\) and the indicated **odd** Fourier zeros has
\[
 f(1/4),f(-1/4)\ge c_0 . \tag{2}
\]
Here is a proof that does not assume uniqueness at a half-periodic limit. Take any sequence \(K\to\infty\) of these densities. Tightness follows from the centered second moment bound. Any weak limit \(\mu\) has every odd Fourier coefficient zero at integer frequencies, so its law modulo one is invariant under translation by \(1/2\), by uniqueness of Fourier coefficients on the circle. For \(0<\sigma\downarrow0\), the density \(g_\sigma\) of \(\mu\) convolved with a Gaussian of variance \(\sigma^2\) is \(a_\sigma\)-strongly log-concave, \(a_\sigma=A/(1+A\sigma^2)\). Indeed the same convolutions of the approximating laws satisfy these inequalities, their densities converge pointwise by weak convergence and bounded continuity of each Gaussian kernel, and the inequalities pass to positive density values. The periodization of \(g_\sigma\) is half-periodic by convolution, and the first zero persists.

Translate each \(g_\sigma\) temporarily to its own mode and call its periodization \(P_\sigma\), its peak \(g_0\). For \(j\geq0\) the same Gaussian envelope along rays gives
\[
 g_\sigma(\pm(j+1/2))\le e^{-a_\sigma/8} g_\sigma(\pm j).
\]
Half-periodicity \(P_\sigma(1/2)=P_\sigma(0)\) now implies
\(P_\sigma(0)\le e^{-a_\sigma/8}(P_\sigma(0)+g_0)\).
Since \(e^{A/8}=2\), we have \(0\le P_\sigma(0)-g_0=O(\sigma^2)P_\sigma(0)\); both \(g_0\) and \(P_\sigma(0)\) are bounded above and away from zero by the preceding peak bounds. Applying the same ray estimate to exclude \(j\ge1\) in the half-period fiber shows \(g_\sigma(1/2)+g_\sigma(-1/2)\ge P_\sigma(0)-O(\sigma^2)\), while each summand is at most \(g_0 e^{-a_\sigma/8}=P_\sigma(0)/2+O(\sigma^2)\). Thus at both endpoints the residual \(g_\sigma(\pm1/2)e^{a_\sigma/8}\) is \(g_0+O(\sigma^2)\). Its log-concavity and peak bound force the same \(O(\sigma^2)\) error across the central interval.

Undoing the translations, the mode positions of these \(g_\sigma\)'s stay bounded: each density gives fixed positive mass to a fixed-length interval around its mode, while \(\mu\) convolved with vanishing Gaussians is tight. Along a subsequence let the mode position tend to \(t_0\) and the peak to \(u_0>0\). The central estimate shows that \(\mu\) has density \(u_0 e^{-A(x-t_0)^2/2}\) in the open interval \((t_0-1/2,t_0+1/2)\), by uniform convergence on its compact subintervals and weak convergence \(\mu*G_\sigma\to\mu\). But the original approximating densities were nonincreasing on \((0,\infty)\) and nondecreasing on \((-\infty,0)\), so in the limit their masses of ordered equal-length intervals in either half-line obey the respective monotonicity, whenever the endpoints have zero mass. The displayed strictly increasing and decreasing central Gaussian then forces \(t_0=0\). In particular \(\mu\) has positive mass on \([1/4,3/8]\) and on its negative. The lower bound on the two density values in (2) follows along this subsequence from weak mass convergence and monotonicity. If no uniform \(c_0\) existed one could start from a sequence with one of these two values tending to zero, contradicting this argument. This completes (2).

## 2. A positive band-limited test with the right order of error

Let \(m=\lfloor K/2\rfloor+1\), and let \(J(t)\), \(|t|\le1/2\), be the normalized Jackson kernel
\[
 J(t)=c_m\left(\frac{\sin(\pi m t)}{\sin(\pi t)}\right)^4
     =c_m\left|\sum_{j=0}^{m-1}e^{2\pi i j t}\right|^4,\qquad \int J=1 .
\]
It is even, nonnegative, and has degree \(2(m-1)\le K\). Its second moment \(M_2=\int J(t)t^2\,dt\) is \(O((K+1)^{-2})\). For this elementary bound, the unnormalized integral is at least a fixed multiple of \(m^3\) from \(|t|\le1/(2m)\); the integrand is bounded by \(\min(m,C/|t|)^4\), so its unnormalized second moment is \(O(m)\). Cauchy–Schwarz gives \(\int J|t|=O((K+1)^{-1})\).

Put \(P(t)=\sum_{j\in\mathbb Z}f(t+j)\) and \(L=\int J(t)f(t)\,dt\), with every integral in this section over \([-1/2,1/2]\). Since \(J\) has no frequencies beyond \(K\), the odd-zero condition gives equality of two exact band-limited tests:
\[
 \int J(t)P(t)\,dt=\int J(t)P(1/2+t)\,dt=:C .
 \tag{3}
\]
One has \(0<L\le C\), and \(C\ge c>0\) for all sufficiently large \(K\) by (2) and the mass of \(J\) in \([-1/4,1/4]\). This does not require that \(C=1\).

In the half-shifted fiber, retain the two nearest terms \(f(1/2+t), f(-1/2+t)\). The further positive term \(f(j+1/2+t)\), \(j\ge1\), is at most \(e^{-3\alpha/8}f(j+t)\): the residual decreases along that ray, and the difference in the squared Gaussian exponents is \((j+t)/2+1/8\ge3/8\). The reflected comparison holds for the further negative terms. Define
\[
 \begin{split}
 H&=\int J(t)\big(e^{-\alpha(1/2+t)^2/2}
                       +e^{-\alpha(-1/2+t)^2/2}\big)\,dt,\\
 D_\pm&=\int J(t)e^{-\alpha(\pm1/2+t)^2/2}
                            \big(f_0-h(\pm1/2+t)\big)\,dt,\qquad D=D_++D_-,\\
 b_0&=e^{-3\alpha/8}.
 \end{split}
\]
Equation (3) and the ray comparison yield \(C\le f_0 H-D+b_0(C-L)\). The integrand of \(H\) before multiplication by \(J\) is even and is \(2e^{-\alpha/8}\) at zero. Its second derivatives are uniformly bounded for \(A\le\alpha\le2\pi^2\), so \(H=2e^{-\alpha/8}+O(M_2)\).

The important point is that an excess of the mode value over \(L\) consumes part of the *same* deficit \(D\). On \(|t|\le1/4\), each point \(\pm 1/2+t\) lies at least \(1/4\) along the corresponding ray, so monotonicity, a fixed lower bound on the Gaussian weights in that range, and \(J\)-mass \(1-O(M_2)\) show
\(f_0-h(\pm1/4)\le C_1 D_\pm\).
By (2) both \(h(\pm1/4)\) are bounded away from zero. For \(0\le u\le1/4\), concavity of \(\log h\) between \(0\) and \(\pm1/4\) gives
\[
 f_0-h(\pm u)\le 4u f_0\log(f_0/h(\pm1/4))\le C_2 uD_\pm .
\]
The final inequality uses the uniform peak bound and the positive lower bound on \(h(\pm1/4)\). Reinstating the Gaussian factor costs \(O(u^2)\). Outside this interval bound \(f_0-f(t)\) by the peak bound and \(\int_{|t|>1/4} J\le16M_2\). Thus
\[
 f_0-L\le C_3 D(K+1)^{-1}+O((K+1)^{-2}).
\]
Combining the last estimates, the cost \(H(f_0-L)\) is absorbed by \(D\) for large \(K\) apart from \(O((K+1)^{-2})\). Since \(L\le f_0\) is bounded, \(2e^{-\alpha/8}>b_0\), and \(L\le C\), this gives
\[
 C\le C\, 2e^{-\alpha/8}+O((K+1)^{-2}).
\]
As \(C\) stays bounded below, \(\alpha\le A+O((K+1)^{-2})\) follows. The absolute upper bound from the first zero absorbs all smaller \(K\) by enlarging the absolute constant. This shows why using a broad smoothing kernel and merely bounding its Fourier tail would lose the sharp scale: the peak deficit here is not paid twice.

## 3. A compact sharp-order lower construction

Let \(\ell\) be the least odd integer greater than \(K\), let \(\omega=2\pi\ell\), and put
\[
 \gamma=\frac{1}{4096\omega^2},\qquad
 \alpha=A+8\log\frac{1+\gamma}{1-\gamma},\qquad P(t)=1+\gamma\cos(\omega t).
\]
Set \(f(x)=(1+\gamma)e^{-\alpha x^2/2}\) on \(|x|\le1/2\), and on \(1/2<|x|<1\) set
\[
 f(x)=T(1-|x|),\qquad
 T(y)= (1+\gamma)(1-e^{-\alpha y^2/2})+\gamma(\cos(\omega y)-1).
 \tag{4}
\]
Set \(f=0\) outside \([-1,1]\). The pieces join continuously at \(|x|=1/2\) because \(2(1+\gamma)e^{-\alpha/8}=1-\gamma=P(1/2)\) for odd \(\ell\). Their first derivatives there also agree, since \(\sin(\pi\ell)=0\). At \(|x|=1\), \(T(0)=0\). Assuming the positivity proved below, the two overlapping terms in one period sum precisely to \(P(t)\), giving normalization and vanishing Fourier coefficients at every nonzero integer except \(\pm\ell\).

For the curvature check write \(B(y)=(1+\gamma)(1-e^{-\alpha y^2/2})\), \(R(y)=\gamma(\cos(\omega y)-1)\) and \(E_0=\gamma\omega^2=1/4096\). Elementary bounds give \(5<\alpha<6\) (e.g. \(2/3<\log2<7/10\) and \(\gamma<1/10000\)). For \(0<y\le1/2\), \(B(y)\ge y^2,\ |B'(y)|\le12y,\ |B''(y)|\le30\), by \(u=\alpha y^2/2\le3/4\) and \(1-e^{-u}\ge ue^{-u}\). Also \(|R(y)|\le E_0y^2/2,\ |R'(y)|\le E_0 y,\ |R''(y)|\le E_0\). Thus \(r=R/B\) satisfies \(|r|\le E_0/2,\ |r'|\le7E_0/y,\ |r''|\le184E_0/y^2\) by the quotient rule. This ensures \(T>0\) and
\[
 |(\log(1+r))''|\le564E_0/y^2 .
\]
On the other hand,
\[
 y^2\big(-(\log B)''-\alpha\big)
   =2u\,\frac{e^u(1+2u-e^u)}{(e^u-1)^2}\ge4/9.
\]
Indeed \((e^u-1)/u\) is increasing, and \(e^{3/4}<17/8\) implies \(e^u-1\le(3/2)u\) and \(1+2u-e^u\ge u/2\) on this interval. Hence the tail curvature exceeds \(\alpha\), since \(564/4096<4/9\). The central curvature is exactly \(\alpha\), and the matching first derivatives across the seams give global strong log-concavity on the open support and, by continuation with zero, on the line. Finally \(\alpha-A\ge16\gamma\ge[1024\pi^2(K+2)^2]^{-1}\), yielding the lower bound in (1). Gaussian convolution supplies the same supremum in the smooth positive class.

## Reproduction

Run `python3 verify-finite-fourier-lift-gap.py` (standard library only). The checker reproduces exact Jackson coefficient identities, rational exponential and quotient-derivative margins in the construction, and sample integer mode arithmetic. The compactness and all-mode comparison are analytic arguments, not inferred from numerical Fourier fits.
