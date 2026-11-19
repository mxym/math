# The leading constant for empty tetrahedra in a tetrahedron

**Theorem.** If \(T\) is any tetrahedron of positive volume and \(H\) counts the empty tetrahedra spanned by \(n\) independent uniform points in \(T\), then
\[
 \lim_{n\to\infty}n^{-3} EH=\frac94+\frac{3\pi^2}{35}.
\]
The existence of this limit and its hyperplane-section formula are due to Reitzner and Temesvari. Here only its evaluation for a tetrahedron is at issue. This answers Problem 1 of Balko–Scheucher–Valtr, [*Tight bounds on the expected number of holes in random point sets*](https://arxiv.org/pdf/2111.12533), whose numerical experiment estimated the constant between 3.095 and 3.097.

## From sections to one chamber

Use affine invariance to take \(T=\operatorname{conv}(0,e_1,e_2,e_3)\), \(V=|T|=1/6\). For \(w\ne0\) let \(f_w\) be the density of \(w\cdot X\) for \(X\) uniform in \(T\); put \(D(w)=\int_{\mathbb R} f_w(t)^4dt\). For unit \(u\), the area of the section at height \(t\) is \(V f_u(t)\). [Reitzner–Temesvari, §3.2, proof of Theorem 1.4](https://arxiv.org/pdf/1808.08734) give the limiting constant as \(3\kappa_3/(4V^3)\) times the integral of section area to the fourth power with respect to hyperplane measure. Their normalization gives mass 2 to the hyperplanes meeting the unit ball: this is the pushforward of \((4\pi)^{-1}d\sigma(u)dt\), for ordinary surface area \(d\sigma\) on the full unit sphere and signed height \(t\). Since \(3\kappa_3=4\pi\), the constant becomes
\[
 \frac{V}{4}\int_{S^2} D(u)\,d\sigma(u).
 \tag{1}
\]

Order the four heights \(0,w_1,w_2,w_3\); ties are negligible. The 24 chambers contribute equally although the reference tetrahedron is not regular. Indeed let \(H(w)\) be the maximum minus minimum of the four heights. The contribution of a conical chamber \(C\) to the sphere integral equals
\[
 \int_C {\bf1}_{1\le H(w)\le e}D(w)\,dw
\]
by radial integration, since \(D(ru)=r^{-3}D(u)\) and \(H(ru)=rH(u)\) for \(r>0\). Every permutation of the four vertices is implemented by an affine map \(x\mapsto Mx+c\) preserving \(T\), hence \(|\det M|=1\). Under \(w\mapsto M^\top w\), the heights are permuted up to a common translation, and the scalar projection law is translated; therefore both \(D\) and \(H\) are invariant. These maps preserve volume and permute the chambers transitively.

In the chamber \(0<w_1<w_2<w_3\), put \(w=(ra,rb,r)\) with \(0<a<b<1\) and \(r=H(w)\). The Jacobian is \(r^2\); integrating \(dr/r\) from 1 to \(e\) and noting \(24V/4=1\) reduce (1) to
\[
 \int_{0<a<b<1}\int_0^1 f_{(a,b,1)}(t)^4\,dt\,da\,db.
 \tag{2}
\]

## Integrating the three spline pieces

For \(w=(a,b,1)\) with vertex heights \(c=(0,a,b,1)\), the classical simplex-section/B-spline formula (e.g. [Lasserre, Theorem 2.2](https://arxiv.org/pdf/1412.4617), differentiated volume divided by \(V\), and rescaled for nonunit \(w\)) gives the density
\[
 f_w(t)=3\sum_{i=0}^3\frac{(t-c_i)_+^2}{\prod_{j\ne i}(c_j-c_i)}.
\]
On the first segment it is \(3t^2/(ab)\) for \(0<t<a\). This segment contributes
\[
 \int_0^1 db\int_0^b da\; 9 a^5/b^4=1/2.
\]
The interval \(b<t<1\) contributes the same by reflecting all heights. For the middle segment put \(t=a+(b-a)u\), \(x=a/b\), \(y=(1-b)/(1-a)\). The quadratic there is
\[
 f_w(t)=3[x(1-u)^2+2u(1-u)+yu^2].
\]
Indeed its two endpoint values are \(3x,3y\), and the derivative with respect to \(t\) at the left endpoint is \(6/b\) by the first segment and spline differentiability. Also \(b=(1-y)/(1-xy),a=xb\): the map takes \(0<a<b<1\) onto \(0<x,y<1\) and
\[
 (b-a)\,da\,db=\frac{(1-x)^2(1-y)^2}{(1-xy)^4}\,dx\,dy .
\]

To evaluate the resulting integral, expand the fourth power multinomially and \((1-xy)^{-4}\) by its nonnegative series; Tonelli applies. For \(i,j\ge0\), \(i+j\le4\), write \(m=4-i-j\). Integrating in \(u\) first gives for the middle segment the series \(\sum_{r=0}^\infty R(r)\), where
\[
 R(r)=\sum_{i+j\le4}
 81\frac{4!\,2^m(2j+m)!(2i+m)!}{i!j!m!9!}
 \frac{2(r+1)(r+2)(r+3)}
      {3\prod_{l=1}^3(r+i+l)(r+j+l)} .
\]
Here \(\int_0^1x^{r+i}(1-x)^2dx=2/\prod_{l=1}^3(r+i+l)\), and similarly for \(y\). Partial fractions give \(35R(r)=\sum_{q=1}^7(A_q/(r+q)+B_q/(r+q)^2)\), with the rows in increasing \(q\) equal to
\[
 A=(24,36,81,-99,-117,-135,210),\qquad
 B=(0,0,0,126,-108,0,0).
\]
These are rational identities, checkable simply by clearing the denominators. For \(H_0^{(s)}=0,\ H_l^{(s)}=\sum_{j=1}^l j^{-s}\), the zero sum of the entries of \(A\) cancels the divergent first harmonic terms. Summation gives
\[
 \sum_{r\ge0}R(r)=\frac1{35}\sum_{q=1}^7
 [-A_qH_{q-1}^{(1)}+B_q(\zeta(2)-H_{q-1}^{(2)})]
 =\frac54+\frac{18}{35}\zeta(2).
\]
The two outer contributions add 1. With \(\zeta(2)=\pi^2/6\) this yields the asserted exact value. No numerical integration or fit to the previously published estimate is needed.
