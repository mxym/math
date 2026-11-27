# How much local unbiased rounding costs to match many Gaussian moments

**Scope:** one-dimensional probability and its independent-coordinate product. This compares idealized continuous-to-discrete laws and does not implement or assess a cryptosystem.

## 1. Model and results

A continuous, compactly supported, even function \(K:\mathbb R\to[0,\infty)\) is an unbiased lattice rounding kernel if for every \(x\in\mathbb R\),
\[
   \sum_{k\in\mathbb Z}K(x-k)=1,\qquad
   \sum_{k\in\mathbb Z}(x-k)K(x-k)=0.                     \tag{1}
\]
Thus \(K(x-k)\) is the probability of outputting \(k\) at input \(x\), and that output has mean \(x\). Also \(\int K=1\), by integrating the first equation over one period. Under uniform input modulo \(\mathbb Z\) the unconditional error has density \(K\). In this note “matching moments” is about that integrated error law, not about reproducing all higher powers of a fixed input point.

The cost of matching the moments of \(G_v=N(0,v)\) through degree \(2r\) is **linear in \(r\)**, both for its variance \(v\) and for its required support radius \(R\). Specifically, \(r\ge1\) implies
\[
 v\ \ge\ \frac{W(e^{-1})}{2\pi^2}\,r,\qquad
 R^2\ \ge\ (2r-1)v,                                    \tag{2}
\]
where \(W\) is the positive real Lambert \(W\) function. Conversely there is such a kernel with \(v=r+1\) and \(R<4(r+1)\), matching all moments through degree \(2r+1\). The upper kernel is a finite positive mixture of translates of the ordinary triangular density.

Write \(g_\sigma\) for the normalized real Gaussian density of standard deviation \(\sigma\), and \(D_{\sigma,c}\) for the law on \(\mathbb Z\) proportional to \(g_\sigma(k-c)\). Rounding \(N(c,\sigma^2)\) by the constructed kernel gives, uniformly over real \(c\),
\[
 \operatorname{TV}\!\left(\text{rounded }N(c,\sigma^2),D_{\sqrt{\sigma^2+r+1},c}\right)
 \le
 \left(1+\frac{\sqrt{2r+3}}{\sigma}\right)
       \left(\frac{8e(r+1)}{\sigma^2}\right)^{r+1}
 +\frac{e^{-2\pi^2(\sigma^2+r+1)}}{1-e^{-2\pi^2(\sigma^2+r+1)}}.     \tag{3}
\]
This is useful for \(\sigma^2>8e(r+1)\), and allows exponential accuracy in \(\sigma^2\) by choosing a new kernel of order proportional to \(\sigma^2\). At any fixed kernel, there is an algebraic obstruction (§5). The constants in (2) and the upper bound are not asserted optimal; the linear orders are.

## 2. Lower bounds from a lattice Fourier zero

Integrate the first part of (1) against \(e^{2\pi i x}\) over one period. This gives \(\mathbb E\cos(2\pi U)=0\) for \(U\) of density \(K\). Only the mass partition property, not the unbiasedness identity, is needed here.

For every real \(y\), \(\cos y\) lies between its Taylor polynomials \(\sum_{j=0}^{r-1}(-1)^j y^{2j}/(2j)!\) and \(\sum_{j=0}^{r}(-1)^j y^{2j}/(2j)!\), in the order dictated by parity. A direct proof starts with \(1-\cos y\ge0\); each successive signed remainder has second derivative equal to the previous signed remainder and has zero value and first derivative at zero. The width of this interval is \(|y|^{2r}/(2r)!\). Since the moments match, averaging those endpoints at \(y=2\pi U\) and at \(y=2\pi G_v\) gives the same interval for both expected cosines. With \(t=2\pi^2 v\), their difference therefore satisfies
\[
          e^{-t}\le \frac{t^r}{r!}.
\]
As \(r!\ge(r/e)^r\), writing \(t=rx\) yields \(x e^x\ge e^{-1}\). This is the first part of (2). The second is immediate from
\(\mathbb E U^{2r}\le R^2\mathbb E U^{2r-2}\) and the ratio \((2r-1)v\) of two successive Gaussian even moments. In particular \(R\) also grows linearly. For comparison \(v\ge1/6\) for any kernel satisfying (1), even without higher matching: the conditional minimum rounding variance at fractional part \(f\) is \(f(1-f)\), which averages to \(1/6\).

## 3. A positive finite measure for the inverse moment problem

Let \(B(u)=(1-|u|)_+\), the density of the sum of two independent uniform \([-1/2,1/2]\) variables. It satisfies (1) by the two adjacent-integer weights. Its moment generating function is
\[
    M_B(t)=\left(\frac{\sinh(t/2)}{t/2}\right)^2.
\]
We build a symmetric probability law \(\nu\) so the first moments of \(B*\nu\) are the Gaussian ones. Its required formal moments have series \(e^{vt^2/2}\psi(t)\), with \(\psi(t)=M_B(t)^{-1}=\sum_{j\ge0}a_j t^j\). The even coefficients of \(\psi\) alternate signs, since the [Euler product for \(\sinh\)](https://dlmf.nist.gov/4.36) gives
\(\psi(it)=\prod_{k\ge1}(1-(t/(2\pi k))^2)^{-2}\) with nonnegative Taylor coefficients on \(|t|<2\pi\). Consequently
\[
       \sum_{j\ge1}|a_j|\,2^j=(\sin 1)^{-2}-1<1/2,
                                                        \tag{4}
\]
where \(\sin 1\ge 5/6\) suffices.

For a polynomial \(P\), put
\[
    L_v(P)=\sum_{j\ge0}a_j\,\mathbb E\,P^{(j)}(G_v);
\]
the sum is finite. Its formal exponential series is exactly \(e^{vt^2/2}\psi(t)\). The main step is positivity through growing order. For polynomials of degree at most \(d\), the Gaussian \(L^2\) norm satisfies
\[
 \|P^{(j)}\|_{G_v}\le(d/v)^{j/2}\|P\|_{G_v}.
\]
Indeed in the orthonormal probabilists' Hermite basis \(x\mapsto \mathrm{He}_k(x/\sqrt v)/\sqrt{k!}\), differentiation lowers index by one with coefficient \(\sqrt{k/v}\). The product rule and Cauchy–Schwarz then give
\[
    |\mathbb E(P^2)^{(j)}(G_v)|
          \le (2\sqrt{d/v})^j\|P\|_{G_v}^2 .
\]
With \(v=d=r+1\), (4) shows for every \(P\) of degree at most \(r+1\)
\[
        \tfrac12\|P\|_{G_v}^2\le L_v(P^2)
                        \le\tfrac32\|P\|_{G_v}^2 .       \tag{5}
\]
Thus the finite moment functional is positive even though the formal series alone need not represent a probability measure at all orders.

To realize the required finite moments, give the polynomials of degree at most \(r+1\) the inner product \(L_v(PQ)\), and let \(J\) be multiplication by \(x\) compressed to the subspace of degrees at most \(r\). It is selfadjoint. Let \(\nu\) be its spectral measure at the constant vector \(1\), which has norm one. It is supported on at most \(r+1\) points; it is symmetric since parity preserves the inner product, fixes \(1\), and conjugates \(J\) to \(-J\). For \(j\le r\), \(J^j1=x^j\), and splitting an exponent into two powers of at most \(r\) shows \(L_v(x^k)=\langle1,J^k1\rangle\) through \(k=2r\). For \(k=2r+1\), use \(\langle x^r,Jx^r\rangle=L_v(x^{2r+1})\). This is finite Gaussian quadrature in spectral form.

The Hermite recurrence gives \(\|xP\|_{G_v}\le\sqrt v(\sqrt{r+1}+\sqrt r)\|P\|_{G_v}\) for degree at most \(r\). By (5) and contraction of the compression in the \(L_v\) norm,
\[
          \|J\|\le 2\sqrt{3v(r+1)}=2\sqrt 3(r+1).
\]
Finally set \(K=B*\nu\). Its moment series matches \(M_B(t)e^{vt^2/2}\psi(t)\) through degree \(2r+1\), as desired. Its density is nonnegative, symmetric and continuous; its support radius is at most \(1+2\sqrt 3(r+1)<4(r+1)\). The first part of (1) is preserved by averaging the translates of \(B\) under \(\nu\). The second part holds since inside the integral \(x-k=(x-k-y)+y\): the first term sums to zero and the second integrates to \(\int y\,d\nu(y)=0\).

The construction also tolerates different base kernels. If \(B\) is any symmetric compactly supported kernel satisfying (1), with support radius \(L>0\), it suffices to use \(v=9L^2(r+1)\) and the same argument. At \(s=2\sqrt{(r+1)/v}=2/(3L)\), the nonconstant coefficients of \(M_B\) have absolute sum \(C(s)=M_B(s)-1\le\cosh(2/3)-1<1/3\). The geometric series for the formal reciprocal bounds its nonconstant absolute sum by \(C(s)/(1-C(s))<1/2\). Thus (5) again holds and the combined support is \(O(L(r+1))\). For example a smooth symmetric compact convolution of the triangle can be used as a base when smoothness is needed. This does not require a signed kernel at either rounding stage.

## 4. From moment matching to the lattice law

Let \(X=N(c,\sigma^2)\) and round using \(K\), and let \(U\) denote its density. The unnormalized Gaussian-comparison identities are
\[
   \Pr[Y=k]=\mathbb E g_\sigma(k-c+U),\qquad
   g_{\sqrt{\sigma^2+v}}(k-c)=\mathbb E g_\sigma(k-c+G_v).
\]
The first is integration of the conditional weight and the second is continuous Gaussian convolution. Their Taylor terms in \(U,G_v\) cancel through degree \(2r+1\).

There is a uniform sampling estimate \(\sum_k|f(k+a)|\le \|f\|_1+\|f'\|_1\) for smooth integrable \(f,f'\), by averaging the fundamental theorem of calculus on every interval \([k+a,k+a+1]\). Also \(\|g_\sigma^{(j)}\|_1\le \sigma^{-j}\sqrt{j!}\) by Hermite orthogonality and Cauchy–Schwarz. Summing the integral Taylor remainder at order \(q=2r+2\), this gives an absolute \(\ell^1\) error at most
\[
  \frac{\mathbb E|U|^q+\mathbb E|G_v|^q}{\sqrt{q!}\,\sigma^q}
               \left(1+\frac{\sqrt{q+1}}{\sigma}\right).
\]
For the constructed kernel, \(R<4(r+1)\), so \(R^q/\sqrt{q!}\le (8e(r+1))^{r+1}\), using \(q!\ge(q/e)^q\). And \(\mathbb E|G_v|^q/\sqrt{q!}\le v^{r+1}\) by \(\binom{2r+2}{r+1}\le 4^{r+1}\). The normalization of the sampled Gaussian changes its \(\ell^1\) mass by \(|Z-1|\), where Poisson summation gives
\(|Z-1|\le 2e^{-2\pi^2(\sigma^2+v)}/(1-e^{-2\pi^2(\sigma^2+v)})\). Dividing by two proves (3).

Applying independent copies in orthogonal coefficient coordinates gives a total variation bound at most the sum of the coordinate bounds; in particular this includes the orthogonal power coordinates of a power-of-two cyclotomic lattice after accounting for the common scale. It says nothing about arbitrary correlated coefficient coordinates or implementation precision.

## 5. The first mismatching moment gives the exact leading error

Fix any compact, symmetric \(K\) satisfying (1) and let \(v\) be its variance. There is a finite first mismatching Gaussian moment of even degree \(2s\ge4\): otherwise (2) would force \(v\) arbitrarily large. Put \(\Delta=\mathbb E U^{2s}-\mathbb E G_v^{2s}\ne0\). Taylor expansion through degree \(2s+1\) gives, in \(\ell^1(\mathbb Z)\) and uniformly in \(c\),
\[
  \Pr[Y=k]-g_{\sqrt{\sigma^2+v}}(k-c)
       =\frac{\Delta}{(2s)!} g_\sigma^{(2s)}(k-c)
                          +O_{\ell^1,K,s}(\sigma^{-2s-2}).
\]
Indeed all preceding terms cancel, including the odd term at degree \(2s+1\); the same sampled derivative bound handles the remainder. The \(\ell^1\) norm of the displayed derivative, times \(\sigma^{2s}\), tends uniformly over \(c\) to its rescaled integral \(\mathbb E|\mathrm{He}_{2s}(Z)|\), \(Z=N(0,1)\), by Riemann sums with a uniformly shifted grid. Poisson normalization is exponentially smaller. Therefore at the variance-matched target width,
\[
 \operatorname{TV}\!\left(\text{rounded }N(c,\sigma^2),
                     D_{\sqrt{\sigma^2+v},c}\right)
   =\frac{|\Delta|\,\mathbb E|\mathrm{He}_{2s}(Z)|}{2(2s)!}
                        \sigma^{-2s}+o_{K,s}(\sigma^{-2s}).
\]
So no single bounded-support kernel gives superpolynomial accuracy in \(\sigma\) in this model. The construction instead uses a choice of kernel that varies with the desired order. The asymptotic here is for the stated variance-matched target, not an optimization over all possible target retunings.

## 6. Prior work and verification

[Peikert's convolution-like randomized rounding](https://eprint.iacr.org/2010/088.pdf) uses shifted discrete Gaussian rounding and a smoothing hypothesis, a different model from a single finite nonnegative unbiased kernel. [de Boor's B-spline convolutions](https://pages.cs.wisc.edu/~deboor/toast/b-convol.pdf) give the standard triangular-spline and convolution setting; [Golub–Welsch](https://www.ams.org/journals/mcom/1969-23-106/S0025-5718-69-99647-1/S0025-5718-69-99647-1.pdf) is the classical spectral quadrature reference. The distributional comparison uses ordinary Gaussian differentiation and Poisson summation. What is proved here is the positivity of the inverse moment functional at variance linear in order, the matching lattice Fourier obstruction, and the uniform continuous-to-discrete error in this constrained problem. The preceding repository note on deterministic nearest rounding considers one fixed kernel, not the existence and necessary size of freely designed positive unbiased kernels.

The adjacent verification checks rational finite moment identities and fixed numeric examples. It reports 5,648 exact and 46 numerical checks. The all-orders positivity, lower bound and statistical estimates are analytic.
