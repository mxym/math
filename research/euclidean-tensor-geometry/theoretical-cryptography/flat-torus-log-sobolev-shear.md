# Sharp log-Sobolev equality and fourth-order symmetry breaking on sheared flat tori

Use normalized Haar measure on \(\mathbb R^2/(2\pi\mathbb Z)^2\), inverse metric
\[
G_c=\begin{pmatrix}1&c\\c&1\end{pmatrix},\qquad 0\le c<1.
\]
Changing the sign of \(c\) is isometric. Write \(E_c(f)=\int \nabla f^\top G_c\nabla f\), \(A_c=-\Delta_{G_c}\), and let \(\alpha_c\) be the infimum of \(E_c(f)/\operatorname{Ent}(f^2)\) for positive entropy. The spectral gap is \(\lambda_c=\min\{1,2(1-c)\}\). Indeed, for any pair of nonzero integer coordinates the smaller choice of their relative sign gives \(q=(|m|-|n|)^2+2(1-c)|mn|\). The two candidate values are realized by an axis and a diagonal frequency.

**Theorem.** Define \(\tau\in(1/18,3/50)\) by
\[
4-72\tau+89\tau^2-12\tau^3-12\tau^4=0 .
\]
Then:
1. \(\alpha_c=\lambda_c/2\) for \(0\le c\le\tau\) and also for \(3/5\le c<1\).
2. For \(0\le c<1/2\), the inequality \(\operatorname{Ent}(f^2)\le 2E_c(f)\) holds for all \(f\) in an \(L^\infty\) neighborhood of the constant 1 (in \(H^1\)) exactly when \(c\le1/\sqrt{10}\). In that neighborhood it is strict off constants. In particular, \(\alpha_c<\lambda_c/2\) throughout \(1/\sqrt{10}<c<1/2\), although the first eigenspace has no resonant triple of frequencies and every first eigenfunction has zero third moment.

Item 1 gives an open family of sharp nonrectangular metrics even without tying the two axis lengths: after normalizing the smaller diagonal entry to 1, any inverse metric \(\bigl(\begin{smallmatrix}1&c\\c&b\end{smallmatrix}\bigr)\) with \(b\ge1,\,|c|\le\tau\) has gap 1 and sharp log-Sobolev constant \(1/2\). Just add the nonnegative form \((b-1)\int f_y^2\) to the rhombic case; the first horizontal mode still has eigenvalue 1. The genuinely rhombic examples \(0<c\le\tau\) are not rectangular: their four shortest dual frequencies are two nonorthogonal opposite pairs, whereas any rectangular torus with four shortest vectors has orthogonal pairs. Nonrectangularity persists in a neighborhood of each such positive-definite metric: in any convergent sequence of rectangular metrics with bounded determinant and smallest eigenvalue bounded away from zero, the corresponding orthogonal unimodular bases have uniformly bounded length (use their product of squared lengths and the lower length bound), hence there are only finitely many bases to consider.

## 1. Global equality by heat dissipation

Set \(D_c(f)=2E_c(f)-\operatorname{Ent}(f^2)\); the usual first-eigenfunction expansion always gives \(\alpha_c\le\lambda_c/2\). For a smooth positive density \(\rho=f^2\), its Fisher information \(I_c=\int \rho |\nabla\log\rho|_{G_c}^2\) satisfies
\[
(\operatorname{Ent}\rho)'=-I_c,\qquad I_c'=-2J_c,\qquad
J_c=\int \rho\,\operatorname{tr}(G_c H\log\rho\,G_c H\log\rho)
\]
along the heat flow \(\partial_t\rho=\Delta_{G_c}\rho\). These follow by integration by parts and the flat Bochner identity. Since \(I_c=4E_c(f)\), it suffices to show \(J_c\ge I_c\): integrate the resulting decay \(I_c(t)\le e^{-2t}I_c(0)\), using convergence of heat to the constant density. Smooth positive approximations of \(|f|\) give the inequality for every real \(H^1\) function by \(H^1\) convergence and the compact two-dimensional Sobolev embedding into \(L^p\) for finite \(p\).

For the next calculation all angles have period \(2\pi\), integrals have normalized measure, and \(f>0\). Write \(X=f_x\), \(Y=f_y\), \(Z=f_{xy}\), \(T=XY/f\), \(U=(X^2+Y^2)/f\), and
\[
P=\int(f_{xx}^2-X^2+f_{yy}^2-Y^2)\ge0 .
\]
Expanding \(H\log(f^2)\) and integrating the mixed term by parts gives
\[
J_c/4=\int[(\Delta_{G_c} f)^2+\Delta_{G_c} f\,|\nabla f|^2_{G_c}/f].
\]
For clarity, \(\int\operatorname{tr}(G_cHfG_cHf)=\int(\Delta_{G_c}f)^2\). If \(V=|\nabla f|^2_{G_c}\), then \(\int \nabla (\!V/f)\cdot G_c\nabla f=-\int \Delta_{G_c} f\,V/f\) produces exactly the cross and quartic terms of the expansion. At \(c=0\) the one-coordinate identity
\(\int(f_{ii}-f_i^2/f)^2=\int f_{ii}^2+(1/3)\int f_i^4/f^2\) yields
\[
(J_0-I_0)/4=P+\int[2(Z-T)^2+(U^2-2T^2)/3].
\]

The difference of the linear Fourier part \(\int[(\Delta_{G_c}f)^2-|\nabla f|^2_{G_c}]\) from its \(c=0\) value is bounded below by \(-2cP+(-6c+4c^2)\int Z^2\). For one mode write \(q=m^2+n^2\), \(p=|mn|\). The linear term is at least \(-2cp(2q-1)\) and the square term is \(4c^2p^2\). The bound follows from the exact identity
\[
2(m^4+n^4-q)+6p^2-2p(2q-1)=2(q-p)(q-p-1)\ge0 .
\]
In the nonlinear part, use
\(\int f_{xx}XY/f=\int(-X^2 Z/(2f)+X^3Y/(2f^2))\), and its \(y\) counterpart, to see that its change is
\(\int[c ZU+c TU+4c^2 ZT]\).
Consequently
\[
(J_c-I_c)/4\ge(1-2c)P+
\int\left[a Z^2+\{cU-4(1-c^2)T\}Z+\tfrac13 U^2+\tfrac43 T^2+cTU\right],
\quad a=2(1-c)(1-2c).
\]
For \(0\le c\le3/50\), \(a>0\); where \(U=0\) the integrand is \(a Z^2\). Where \(U>0\), minimize the square in \(Z\), then put \(s=T/U\in[-1/2,1/2]\). The resulting factor of \(U^2\) is
\[
\frac13+\frac43s^2+cs-\frac{(c-4(1-c^2)s)^2}{4a}.
\]
It is concave in \(s\) because \(4/3<4(1-c^2)^2/a\) on this range. Its smaller endpoint is \(s=-1/2\), so the factor is at least
\[
\frac23-\frac c2-\frac{(2+c-2c^2)^2}{4a}.
\]
This is strictly decreasing on \([0,3/50]\) (the squared positive numerator increases and \(a\) decreases). Its sign is the sign of \(4-72c+89c^2-12c^3-12c^4\). The value at \(1/18\) is \(149/11016\); at \(3/50\) the sign is negative. This proves the root assertion, \(J_c\ge I_c\) through \(\tau\), and the first equality range.

## 2. Global equality at large shear: a fiber criterion

On an arbitrary Euclidean flat torus, choose a primitive dual frequency \(u\), in angular normalization (characters \(e^{i\langle u,x\rangle}\)). Projection onto the \(u\) circle is a Riemannian submersion to a circle of spectral gap \(|u|^2\), with isometric connected fibers and orthogonal horizontal direction. For a smooth \(f\), let \(b\) be the square-root of the conditional mean of \(f^2\) along each fiber. The entropy decomposition into the integral of the fiber entropies and \(\operatorname{Ent}(b^2)\) is exact. The base energy of \(b\) is at most the horizontal energy of \(f\) by Cauchy–Schwarz, differentiating using the local parallel transport between fibers. Global monodromy does not affect \(b\). The tensorization argument therefore gives the lower bound \(\alpha_{\rm torus}\ge\min\{|u|^2/2,\alpha_{\rm fiber}\}\), using the sharp circle inequality for the base. If \(u\) is shortest and \(\alpha_{\rm fiber}\ge |u|^2/2\), this proves equality.

In rank two, the fiber is a circle whose gap is the squared norm of the orthogonal projection of a completing dual basis vector onto \(u^\perp\). One may see this by restricting its character to the kernel of the primitive first character: it generates the character group of the fiber. For \(c>1/2\) take \(u=(1,-1)\) and a completing dual basis vector \(v=(0,1)\), in Fourier coordinates. The projection's squared length is \((1-c^2)/(2(1-c))=(1+c)/2\), which is at least \(2(1-c)\) exactly when \(c\ge 3/5\).

## 3. Local equality threshold: optimize the non-first modes

For \(c<1/2\) the first eigenspace \(K\) consists precisely of the horizontal and vertical first modes. Its real elements have zero cubic average, and translations allow \(g\in K\) to be written \(g=A\cos x+B\cos y\), with no restriction needed on the signs. On the orthogonal complement of constants and \(K\), denote by \(L=A_c-1\) the positive operator and by \(\Pi\) the projection. Below \(\langle\,\cdot\,\rangle\) denotes Haar average.

Normalize a perturbation by \(\langle f\rangle=1\), permissible by homogeneity. For mean zero \(u=f-1\) near zero the expansion is
\[
D_c(1+u)=2\langle u,(A_c-1)u\rangle
-\tfrac23\langle u^3\rangle+\tfrac16\langle u^4\rangle-\tfrac1{15}\langle u^5\rangle
+\tfrac1{30}\langle u^6\rangle
+\tfrac12\langle u^2\rangle^2-\tfrac16\langle u^2\rangle^3+O(\|u\|_\infty^7).
\]
This is the Taylor series of \(2(1+u)^2\log(1+u)\) with the normalizing term \((1+\langle u^2\rangle)\log(1+\langle u^2\rangle)\) subtracted from the entropy.

At each small fixed \(g\in K\), the complement can be optimized locally. On \(H^s\) for \(s>1\) the projected critical equation maps analytically to \(H^{s-2}\); at zero its complement derivative is the isomorphism \(4L\). The analytic implicit function theorem gives \(w(g)\) in the complement with \(w(0)=0,Dw(0)=0\). The complement Hessian is the positive quadratic form \(4L\) plus a bounded \(L^2\) perturbation of size \(O(\|u\|_\infty)\). Indeed the scalar entropy terms have uniformly bounded derivatives near \(1\), and the derivatives of the normalizing integral are bounded multiplication and rank-one terms. Shrink the neighborhood using the positive spectral gap of \(L\). Along the line segment from any nearby complement perturbation \(h\in H^1\cap L^\infty\) to \(w(g)\), the second derivative is then positive unless \(h=w(g)\). Thus \(w(g)\) minimizes the deficit there, also for \(H^1\cap L^\infty\), and it suffices to study \(d(g)=D_c(1+g+w(g))\). Translation invariance and uniqueness imply that \(d(g)\) is phase independent and even under \(g\mapsto-g\) (translate both coordinates by \(\pi\)).

The second-order correction in \(w(tg)\) is \(t^2h\) with \(h=L^{-1}\Pi(g^2)/2\): it minimizes \(2\langle h,Lh\rangle-2\langle h,g^2\rangle\). Accordingly, \(d(tg)\) has quartic coefficient
\[
Q_c(g)=\tfrac16\langle g^4\rangle+\tfrac12\langle g^2\rangle^2
-\tfrac12\langle\Pi g^2,L^{-1}\Pi g^2\rangle
=\frac{A^4+B^4}{6}-\frac{2c^2}{1-4c^2}A^2B^2.
\]
To check the last expression, the zero mode of \(g^2\) is \((A^2+B^2)/2\). Its doubled-axis modes have eigenvalue 4, and the two diagonal cosine terms \(AB\cos(x+y)\), \(AB\cos(x-y)\) have eigenvalues \(2\pm2c\). Parseval gives the stated expression without Fourier truncation. If \(c<1/\sqrt{10}\), it is strictly positive for \(g\ne0\), uniformly on the finite-dimensional unit sphere. If \(c>1/\sqrt{10}\), take \(A=B=1\). Then \(Q_c<0\) and the explicit polynomial trial function \(1+t g+t^2h\) is positive and has negative \(D_c\) for all sufficiently small nonzero \(t\). The strict failure holds on nearby general inverse metrics, including ones with just a single opposite shortest pair: the fixed witness and the spectral gap depend continuously on the matrix. No first-shell cubic resonance is used.

### The borderline is locally stable

At \(c=1/\sqrt{10}\) the quartic is \((A^2-B^2)^2/6\). On the vanishing cone it suffices by translation and homogeneity to use \(g=\cos x+\cos y\). Write \(w(tg)=t^2h+t^3k+t^4\ell+\cdots\). The sixth-order terms involving \(\ell\) cancel by the critical equation for \(h\). The \(k\)-terms are \(2\langle k,Lk\rangle+\langle k,p\rangle\) with \(p=-4gh+(2/3)g^3\); at their minimum they contribute \(-\langle\Pi p,L^{-1}\Pi p\rangle/8\). The full sixth-order coefficient is
\[
-\tfrac23\langle h^3\rangle+\langle g^2h^2\rangle-\tfrac13\langle g^4h\rangle+
\tfrac1{30}\langle g^6\rangle+\langle g^2\rangle\langle h^2\rangle
-\tfrac16\langle g^2\rangle^3-\tfrac18\langle\Pi p,L^{-1}\Pi p\rangle
=\frac{365}{324}>0 .
\]
The seven summands in order are \(-5/72,191/144,-8/9,5/24,47/48,-1/6,-85/324\). Products are finite Fourier convolutions: start with coefficients \(1/2\) at \(\pm(1,0),\pm(0,1)\), invert \(L\) on a mode by division by \(m^2+n^2+2cmn-1\), and discard the four first modes and zero in each projected inverse. This gives the rational table with arithmetic in \(\mathbb Q(c)\), \(c^2=1/10\). The [standalone replay](verify-flat-torus-log-sobolev-shear.js) computes the table exactly. The degree-six part of the even analytic \(d\) is positive on a neighborhood of the normalized vanishing cone by continuity. On the rest of the unit sphere the quartic is uniformly positive. The uniform higher-order remainder proves local strictness at the borderline; it makes no claim of global equality there.

## Scope and prior work

[Chen, Liu and Saloff-Coste (2008), Theorem 1.1 and Question Q1](https://doi.org/10.5802/afst.1183) give the third-moment obstruction and ask for the flat-torus constant; their Q1 also records the known sharp circle and rectangular cases. [AIM problem 1019](https://github.com/MColbrook/AIM/blob/b2ec0fac559f532fc0ed04fce81deea0ce07c68b/problems/1019-the-sharp-logarithmic-sobolev-constant-of-a-flat-torus.md) includes this question. [Colbrook's primary note](https://github.com/MColbrook/AIM/blob/b2ec0fac559f532fc0ed04fce81deea0ce07c68b/research/solutions/1019-flat-torus-log-sobolev/aim1019.tex), §§2–4, already gives strict failure at \(c=1/2\) by a cubic resonance and then on the explicit surrounding interval \((787/1728,941/1805)\) by a fixed trial function. The present computation extends that interval downward to \(1/\sqrt{10}\) by a fourth-order mechanism and gives positive nonproduct ranges. The exact sharp constant in the strict-failure range, and the global equality transition between \(\tau\) and \(1/\sqrt{10}\), are not determined. For \(c<1/2\), the equality set is an interval starting at zero since each \(D_c(f)\) is affine in \(c\); positivity is an intersection of closed half-spaces. At the endpoint \(1/\sqrt{10}\) the result is **local only**. This is a continuum variational result, not a claim about discrete cryptographic assumptions.

Replay: Node.js 18+, no dependencies or data files.
