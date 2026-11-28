# An exact integer-center Gaussian conversion at the four-thirds width scale

Let \(g_t(x)=t^{-1}e^{-\pi x^2/t^2}\) and give \(D_s\) on \(\mathbb Z\) mass proportional to \(e^{-\pi j^2/s^2}\). A single observation is \(X=\theta+G_t\) for an unknown integer \(\theta\); \(G_t\) has density \(g_t\). The output should have exactly the law \(\theta+D_s\) for every \(\theta\in\mathbb Z\).

**Theorem.** For every \(t\ge4\), an exact Markov kernel exists whenever
\[
                             s^2\ \ge\ \tfrac43 t^2+2 .               \tag{1}
\]
The same statement holds on \(\mathbb Z^d\) with spherical input and the corresponding centered product discrete Gaussian. For a fixed rectangular lattice with largest orthogonal step \(b\), it holds with \(t\ge4b\), \(s^2\ge(4/3)t^2+2b^2\). The parameters refer to the displayed width convention, not standard deviation.

This improves the sufficient ratio from every fixed ratio \(>3/2\) in the [previous integer theorem](exact-integer-gaussian-discretization.md) to \(4/3+O(t^{-2})\), and includes the old unresolved \(3/2\) endpoint for large \(t\). The earlier [general lattice result](exact-lattice-gaussian-gap.md) gives the necessary asymptotic ratio \(5/4-O(t^{-2})\), also on the line. We do not close the gap between these constants or claim the exact \(4/3\) endpoint without the additive constant. Nor do we extend the improved upper bound to skew lattices. [Peikert, §3](https://web.eecs.umich.edu/~cpeikert/pubs/pargauss.pdf) and [LPR Toolkit, §2.4.2](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf) address the different, statistically approximate randomized Gaussian rounding problem. This is solely an exact abstract comparison on the lattice parameter set; it does not give an efficient sampler or a security consequence.

## 1. A bounded perturbation with exact sample identities

It suffices to construct the kernel for \(s^2=\frac43 t^2+2\). Write
\[
 \Delta=s^2-t^2=t^2/3+2,\qquad
 L=s^2/\Delta,\qquad \beta=1/L,\qquad \omega=t^2/L .
\]
Then \(d_0=4-L=6/\Delta\) satisfies \(0<d_0<1\) for \(t\ge4\), \(t^2=(L-1)\Delta\), and \(\beta L=1\). For every real \(x,w\), completion of squares gives
\[
         g_t(x-w)g_{\sqrt\Delta}(w)
               =g_s(x)g_{\sqrt\omega}(w-\beta x).                    \tag{2}
\]
We seek a real bounded \(u\) with
\(\mathbb E u(\beta j+G_{\sqrt\omega})=0\) for every \(j\in\mathbb Z\) and such that \(g_{\sqrt\Delta}(1+u)\) has no nonzero integer Fourier coefficients. We will obtain \(\|u\|_\infty<1\).

The frequency functions used for \(k\ge1\) are
\[
 \lambda_1=\lambda=2-d_0/4,\qquad \lambda_k=k\ (k\ge2),\qquad
 \mu_k=\lambda_k-L,\qquad
 b_k=\exp[-\pi t^2(2\lambda_k-L)],
\]
\[
 U_k(w)=\cos(2\pi\lambda_k w)- b_k\cos(2\pi\mu_k w).
\]
These satisfy \(0<b_k\le1\), \(\|U_k\|_\infty\le2\). Their mean in each matched Gaussian in (2) is zero: the two phases at \(\beta j\) agree because \(\lambda_k-\mu_k=L\), and
\(\omega(\lambda_k^2-\mu_k^2)=t^2(2\lambda_k-L)\) makes their damping agree.

For \(c=(c_k)_{k\ge1}\in\ell^1\), put \(u=\sum_k c_k U_k\). Twice the Fourier coefficient of \(g_{\sqrt\Delta}U_k\) at integer \(j\ge1\) is
\[
 T_{jk}=e^{-\pi\Delta (j-\lambda_k)^2}
       +e^{-\pi\Delta (j+\lambda_k)^2}
       -b_k\big[e^{-\pi\Delta(j-\mu_k)^2}
                    +e^{-\pi\Delta(j+\mu_k)^2}\big].
 \tag{3}
\]
Thus we must solve \(T c=f\) with \(f_j=-2e^{-\pi\Delta j^2}\). The previously used diagonal-column argument breaks below the \(3/2\) ratio because the primary frequency for the first constraint is closer to 2 than to 1. Here we eliminate that spillover into the coordinates \(j\ge2\) first and prove that its feedback into coordinate 1 is small.

## 2. Uniform estimates for the Schur complement

Use the abbreviations
\[
 D=e^{-\pi\Delta},\quad
 P=e^{-\pi\Delta(\lambda-1)^2},\quad
 V=e^{-\pi\Delta(2-\lambda)^2},\quad
 z=e^{-\pi\Delta d_0/2}=e^{-3\pi}.
\]
Write \(T=\begin{pmatrix}T_{11}&r\\ v&B\end{pmatrix}\), with \(B\) on indices \(j,k\ge2\). On \(\ell^1\) the high block satisfies
\[
       \|B-I\|_{1\to1}\le \frac{3D}{1-D}+4e^{-12\pi}<\tfrac12 .       \tag{4}
\]
Indeed the positive primary columns have integer centers \(k\) and \(-k\); their total nondiagonal contribution is bounded by \(3\sum_{\ell\ge1}e^{-\pi\Delta \ell^2}\). For the negative terms, each shifted Gaussian column sum, even over the whole integer line, is at most \(2\) for \(\Delta\ge1\), by Poisson positivity and the centered sum bound. Also for \(k\ge2\)
\[
 b_k\le e^{-\pi t^2(4-L)}=e^{-\pi (L-1)\Delta d_0}\le e^{-12\pi},
\]
since \(L\ge3\). This proves (4) and gives \(\|B^{-1}\|_{1\to1}\le2\).

For the high-to-first row, \(\|r\|_{\infty}\le4 D\). The primary terms have distances at least 1. When \(k=2\), the lower of the two companion exponents divided by \(\pi\Delta\) is
\[
       (L-1)(4-L)+(L-3)^2=5-L\ge1 .
\]
When \(k\ge3\), the damping alone gives \((L-1)(2k-L)\ge4\). Consequently each companion term has magnitude at most \(D\).

In the first column, \(1<|\mu_1|=L-\lambda<\lambda<2\). Thus each of its four Gaussian sums at \(j\ge2\) is at most \(V/(1-D)\): the nearest positive integer \(j\ge2\) to the larger absolute frequency is 2, and moving \(q\) more steps adds at least \(q\) to the squared distance. (The reflected side is no closer.) Damping does not increase these bounds, so \(\|v\|_1\le8 V\). At \(j=1\) the nearest primary term is \(P\). The nearer companion contributes at most \(zP\), because its exponent difference divided by \(\pi\Delta\) is exactly
\[
     (L-1)(2\lambda-L)+(L-\lambda-1)^2-(\lambda-1)^2
                =2\lambda-L=d_0/2.
\]
The farther companion is no larger. Therefore \(T_{11}\ge P(1-2z)\).

Now
\[
 \frac{D V}{P}
 =\exp[-\pi\Delta\{1+(2-\lambda)^2-(\lambda-1)^2\}]
 =e^{-\pi\Delta(4-2\lambda)}=z .
\]
Equations (4) and the row/column estimates bound the Schur complement
\(S=T_{11}-r B^{-1}v\) below by \(P(1-66z)\ge P/2\). All these inequalities are uniform in \(t\ge4\); the matrix is not being treated as diagonally dominant in the first column.

The high part of \(f\) has \(\ell^1\) norm at most \(3D^4\). The absolute value of the first Schur right side \(f_1-rB^{-1}f_{\ge2}\) is at most \(2D+24D^5\le3D\). It follows that the real solution satisfies
\[
 |c_1|\le6D/P
       =6e^{-\pi\Delta[\,d_0/2-d_0^2/16\,]}
       \le6e^{-21\pi/8}
\]
because \(\Delta d_0=6\) and \(d_0<1\). The high coefficients satisfy \(\|c_{\ge2}\|_1\le6D^4+16|c_1|\). Since \(\Delta\ge 22/3\), these estimates in particular give \(2\|c\|_1<1\). Thus (3) solves all nonzero integer Fourier constraints with \(\|u\|_\infty<1\).

## 3. Exact normalization, larger widths, and products

The real function \(p_0=g_{\sqrt\Delta}(1+u)\) is nonnegative and integrable. Its periodization is continuous and constant: the Gaussian tail permits uniform summation over integer translates, and all its nonzero Fourier coefficients vanish by construction and even symmetry. Normalize \(p=p_0/\int p_0\), so \(\sum_{j\in\mathbb Z}p(j-x)=1\) for every \(x\). This defines the kernel \(K(j\mid x)=p(j-x)\).

Equation (2) and the zero expectations of each \(U_k\), summed absolutely, give \((g_t*p_0)(j)=g_s(j)\) for every integer \(j\). Normalization therefore gives \((g_t*p)(j)=D_s(j)\): the masses are proportional to \(g_s(j)\) and sum to one by the kernel normalization. For arbitrary integer \(\theta\), translation invariance gives \((g_t*p)(j-\theta)\) as the output mass. This proves the exact statement at equality in (1).

If \(s^2\ge(4/3)t^2+2\), put \(\widetilde t^2=\tfrac34(s^2-2)\ge t^2\). First add an independent centered continuous Gaussian of width \(\sqrt{\widetilde t^2-t^2}\) (or do nothing at equality). The unknown center is unchanged, and the constructive case with width \(\widetilde t\ge4\) applies exactly. In orthogonal coordinates of a rectangular lattice, each coordinate of the input belongs to an independent scalar Gaussian location experiment, with unknown integer center after dividing by its step \(b_i\). The stated conditions imply \(t/b_i\ge4\), \((s/b_i)^2\ge\tfrac43(t/b_i)^2+2\) for every \(i\). Use a product of the scalar kernels and scale the outputs back. This proves the remaining claims.

## Reproduction

Run \(\texttt{python3 verify-four-thirds-discretization.py}\). This only checks the exact exponent identities, conservative Schur bounds, and finite illustrative entries; the proof concerns the infinite \(\ell^1\) block and no numerical truncation is needed.
