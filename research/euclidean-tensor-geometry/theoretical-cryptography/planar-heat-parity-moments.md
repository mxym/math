# The hexagonal torus minimizes the cubic and quartic heat-kernel moments at every time

## Results

Let \(L\subset\mathbb R^2\) be a lattice of area one, \(p_{L,t}\) the heat kernel of the flat torus \(\mathbb R^2/L\) at time \(t>0\) based at the origin, and \(dx\) its Haar probability measure. Let \(H\) be the area-one hexagonal lattice, also called the triangular lattice.

For every \(t,s>0\), \(H\) uniquely minimizes, up to isometry,
\[
\int p_{L,t}^{\,2}p_{L,s}\,dx,\qquad
\int p_{L,t}^{\,2}p_{L,s}^{\,2}\,dx .
\]
In particular it uniquely minimizes \(\|p_{L,t}\|_3\) and \(\|p_{L,t}\|_4\) at **each** time, and equivalently maximizes the order-three and order-four Rényi entropies. No conclusion is asserted here at order one or at other real orders.

The proof is a parity-gluing principle: for every \(m\ge1\) and all \(u_1,\ldots,u_m>0\),
\[
Z_m(L;u_1,\ldots,u_m)
=\sum_{\delta\in L/2L}\prod_{j=1}^m\Theta_\delta(u_j),
\qquad
\Theta_\delta(u)=\sum_{v\in2L+\delta}e^{-u\|v\|^2},
\tag{1}
\]
is uniquely minimized by \(H\). In particular the principle treats mixed Gaussian widths, not only the two heat-kernel consequences. The key separate fact is that the three nonzero parity classes of **any** fixed planar lattice have the same ordering at every width. We give the strict order and all ties in a reduced basis.

## 1. The fixed ordering of three parity classes

After an isometry choose an oriented area-one reduced basis
\[
v=(y^{-1/2},0),\quad w=(x y^{-1/2},y^{1/2}),
\qquad 0\le x\le 1/2,\quad x^2+y^2\ge1,
\]
so \(y\ge\sqrt3/2\). These inequalities follow, for example, by choosing a shortest primitive \(v\), completing to a lattice basis, reducing the parallel component of \(w\) modulo \(v\), and choosing the reflection/orientation so its coefficient \(x\) is nonnegative. Write \(10,01,11\) for the classes of \(v,w,v+w\). The claim is
\[
\Theta_{10}(u)\ge\Theta_{01}(u)\ge\Theta_{11}(u)\qquad(u>0),
\tag{2}
\]
with equality in the first comparison precisely when \(x^2+y^2=1\), and in the second precisely when \(x=1/2\). These correspond to equality of the successive squared lengths \(1/y\), \((x^2+y^2)/y\), \(((1-x)^2+y^2)/y\) of \(v,w,w-v\).

### Reciprocal widths preserve nonzero-class differences

For an area-one lattice, a right-angle rotation \(J\) sends \(L\) onto its dual \(L^*\): its pairings are signed integer determinants, and its covolume equals that of the dual. Poisson summation on \(2L\) gives
\[
\Theta_\delta(u)
=\frac{\pi}{4u}\sum_{\epsilon\in L/2L}
(-1)^{\det(\delta,\epsilon)}\Theta_\epsilon\bigl(\pi^2/(4u)\bigr).
\tag{3}
\]
Here the determinant sign under a different compatible orientation is immaterial modulo two. For a nonzero \(\delta\), the sign is positive for \(\epsilon=0,\delta\) and negative for the other two classes. Subtracting the equations for two distinct nonzero classes gives a positive scalar times the same difference at the reciprocal width. It is therefore enough to prove (2) for \(u\ge\pi/2\). Separately, the same Poisson sum at any width shows \(\Theta_0(u)>\Theta_\delta(u)>0\) for \(\delta\ne0\): all summands in the difference from the zero class are nonnegative, and a character odd on \(\delta\) gives strictness.

### A Jacobi strip comparison

Use any area-one basis of the coordinate form above with \(0\le x\le1/2\) and \(y\ge9/20\), even if it is not a reduced basis. For \(a>0\) write
\[
M_a(t)=\sum_{m\in\mathbb Z}(-1)^m e^{-a(m+t)^2}.
\]
Poisson summation with the alternating character and the [Jacobi product for \(\vartheta_2\)](https://dlmf.nist.gov/20.5.E2) give
\[
M_a(t)=C_a\cos(\pi t)\prod_{k\ge1}
\bigl(1+2q^{2k}\cos(2\pi t)+q^{4k}\bigr),
\qquad q=e^{-\pi^2/a},\quad C_a>0.
\tag{4}
\]
In particular \(M_a(x)>0\) for \(0\le x<1/2\). For odd positive \(j\), the sine multiple-angle bound \(|\sin(jz)|\le j|\sin z|\) gives \(|\cos(\pi jx)|\le j\cos(\pi x)\) on this interval. The ratio of the largest to smallest possible product in (4) is bounded by \(e^{a/4}\): its logarithm is
\[
2\sum_{k\ge1}\log\coth(\pi^2 k/a)
\le\frac{2a}{\pi^2}\int_0^\infty\log\coth r\,dr=\frac a4 .
\]
The inequality uses the positive decreasing integrand; the integral is \(\pi^2/8\), by expanding the two logarithms in \(\log(1+e^{-2r})-\log(1-e^{-2r})\) and integrating the odd powers. Thus
\[
|M_a(jx)|\le j e^{a/4}M_a(x).
\tag{5}
\]
At \(x=1/2\) both sides vanish for odd \(j\), directly from (4).

Group the \(01\) and \(11\) cosets along odd second coordinates:
\[
\Theta_{01}(u)-\Theta_{11}(u)
=2\sum_{\substack{j\ge1\\j\ \mathrm{odd}}}e^{-u y j^2}M_{u/y}(j x).
\tag{6}
\]
For \(x<1/2\), compare the tail to the positive \(j=1\) term with (5). Its absolute ratio is at most
\[
\sum_{\substack{j\ge3\\j\ \mathrm{odd}}}
j\exp\left[-u\left(y(j^2-1)-\frac{1}{4y}\right)\right]<1 .
\tag{7}
\]
For an explicit uniform check, the bracket increases with \(y\). At \(y=9/20\), \(u\ge\pi/2>3/2\), and \(j=3+2k\), the exponent's positive magnitude exceeds \(4+10k\): \( (3/2)(8\cdot 9/20-5/9)>4\), and \(j^2-9=4k(k+3)\ge16k\) for \(k\ge1\). Hence the sum in (7) is below \(e^{-4}\sum_{k\ge0}(3+2k)e^{-10k}<1\), even using just \(e>2\). Formula (6) proves the strip comparison, strict unless \(x=1/2\). This settles the second inequality of (2) in the original reduced basis.

### The other comparison, including the cusp

If \(y\le3/2\), use the basis \(v'=v-w,w'=v\). It is oriented with area one and has parameters
\[
x'=\frac{1-x}{(1-x)^2+y^2}\in[0,1/2],\qquad
y'=\frac{y}{(1-x)^2+y^2}\ge\frac6{13}>\frac9{20}.
\]
The upper bound on \(x'\) is equivalent to \(x^2+y^2\ge1\); equality is equivalent to equality there. For the bound on \(y'\), its reciprocal is at most \(y+1/y\) for \(y\in[\sqrt3/2,3/2]\); the maximum of this convex function on the interval is \(13/6\). In the new basis the second coordinate odd and the first even gives the original class \(10\); both odd gives the original class \(01\). Apply the strip comparison, proving the first inequality of (2) with its stated equality in this region.

If \(y>3/2\), the lower bound \(\Theta_{10}(u)\ge 2e^{-u/y}\) comes from \(\pm v\). For \(\Theta_{01}\) sum on each odd \(j\) over the even first-coordinate integers. The one-dimensional sum at any shift is at most its zero-shift value by the positive Fourier expansion, and
\[
\sum_{k\in\mathbb Z}e^{-(4u/y)k^2}\ \le\ 1+\frac12\sqrt{\pi y/u}
\]
by integral comparison. Thus
\[
\frac{\Theta_{01}(u)}{2e^{-u/y}}
\le \left(1+\tfrac12\sqrt{\pi y/u}\right)
\frac{e^{-u(y-1/y)}}{1-e^{-8uy}}
\le \frac{(1+\sqrt{y/2})e^{-(\pi/2)(y-1/y)}}{1-e^{-6\pi}} <1 .
\tag{8}
\]
For the last strict inequality, the numerator decreases for \(y\ge3/2\) since the logarithmic derivative of \(1+\sqrt{y/2}\) is at most \(1/(2y)\). Its value at \(3/2\) is \((1+\sqrt3/2)e^{-5\pi/12}<2/3\) (use \(5\pi/12>5/4\) and \(e^{5/4}>3\)); the reciprocal denominator is less than \(3/2\). There is no tie in this region. This proves (2) for the required widths, and (3) completes the all-width claim.

## 2. The parity-gluing minimum

For any \(u_j\) let \(A_j=\Theta_0(u_j)=\Theta_L(4u_j)\), \(P_j=\Theta_L(u_j)=\sum_\delta\Theta_\delta(u_j)\). The three nonzero terms, as a vector, are sorted in the same direction at every \(u_j\) by (2). Chebyshev's sum inequality, iterated on the product of positive sorted vectors, gives
\[
Z_m(L;u_1,\ldots,u_m)
\ \ge\ \prod_j A_j+3^{1-m}\prod_j(P_j-A_j).
\tag{9}
\]
For two vectors the inequality follows from summing \((a_i-a_k)(b_i-b_k)\ge0\) over pairs; for several, the product of the already combined positive sorted vectors is still sorted. At \(H\), rotation acts transitively on the three classes, so all are equal and (9) is attained.

Treat the right side of (9) as a function \(B(A,P)\) on the convex domain \(A_j>0\), \(A_j<P_j\le4A_j\), which includes all the lattice inputs by the positivity and the zero-class maximum. Its partial derivatives satisfy
\[
\frac{\partial B}{\partial P_i}=3^{1-m}\prod_{j\ne i}(P_j-A_j)>0,\quad
\frac{\partial B}{\partial A_i}
=\prod_{j\ne i}A_j-3^{1-m}\prod_{j\ne i}(P_j-A_j)\ge0.
\tag{10}
\]
By [Montgomery's minimum-theta theorem](https://doi.org/10.1017/S0017089500007047), every \(A_j\) and \(P_j\) is at least its value at \(H\), and every \(P_j\) is strictly larger unless \(L\) is hexagonal. The line segment between the two evaluation vectors stays in the displayed domain, so (10) gives the comparison strictly unless \(L\cong H\). Together with equality at \(H\) in (9), this proves the claim for (1). The argument also handles \(m=1\), when it reduces to Montgomery's result.

Equivalently this proves minimization of the Gaussian sum on the lattice of tuples \((z_1,\ldots,z_m)\in L^m\) with all \(z_j\) congruent modulo \(2L\), using the arbitrary positive diagonal weights \(u_j\) on their squared norms. This interpretation does not assert minimization among all lattices of dimension \(2m\), only within that parity-glued family with common planar shape.

## 3. Heat-kernel moments and mixed times

The Fourier series of the heat kernel is
\[
p_{L,t}(x)=\sum_{v\in L^*}e^{-4\pi^2 t\|v\|^2}e^{2\pi i\langle v,x\rangle}.
\]
It is absolutely convergent at each positive time. Integrating a product retains only tuples whose frequencies sum to zero. Write \(K=L^*\), \(a=4\pi^2t\), \(b=4\pi^2s\); \(K\) also has area one and is hexagonal exactly when \(L\) is.

For the product \(p_t^2p_s\), name the first two frequencies \(v,w\), so the last is \(-v-w\). The change of variables \(r=v+w,d=v-w\) gives a bijection onto pairs in \(K^2\) of the same parity class, and
\[
a(\|v\|^2+\|w\|^2)+b\|v+w\|^2
=(a/2+b)\|r\|^2+(a/2)\|d\|^2.
\]
Thus the integral is \(Z_2(K;a/2+b,a/2)\) and our result applies. For the product \(p_t^2p_s^2\), let \(r\) be the sum of the first two frequencies and \(-r\) the sum of the last two. The differences \(d,e\) of these two ordered pairs both lie in the parity class of \(r\). This is again a bijection and the exponent becomes
\[
((a+b)/2)\|r\|^2+(a/2)\|d\|^2+(b/2)\|e\|^2 .
\]
This gives \(Z_3(K;(a+b)/2,a/2,b/2)\), proving the second comparison.

At equal times these are the cubic and quartic power moments. For a density \(p\) on a probability space, the order-\(k\) Rényi entropy is \((1-k)^{-1}\log\int p^k\) for \(k>1\), and \(\|p\|_k\) is the positive \(k\)-th root of the same integral. This proves the asserted equivalences. The weak lower envelope (9) yields an attained explicit minimum in terms of the ordinary hexagonal theta values at the indicated widths and their quadruples; no asymptotics in \(t\) are needed.

### Independent equal-time fourth-moment proof

For \(p_t^4\), an alternative elementary transformation of a zero-sum quadruple \((v_1,v_2,v_3,v_4)\) takes \(z_1=v_1+v_2,z_2=v_1+v_3,z_3=v_1+v_4\), whose sum is \(2v_1\in2K\). The inverse is division by two of the corresponding signed sums. It preserves the sum of squared norms and all integrality restrictions. If \(A=\Theta_0(a)\) and \(B,C,D\) are the other three parity values at the common width, the integral is
\[
A^3+3A(B^2+C^2+D^2)+6BCD .
\]
For fixed \(S=B+C+D\), averaging a pair, say \(B,C\), cannot increase this expression since the part depending on \(BC\) is \(-6(A-D)BC\) and \(D\le A\). Repeated averaging gives the lower bound \(A^3+AS^2+(2/9)S^3\) with equality at \(H\). For \(P=\Theta_K(a)=A+S\), its derivative in \(A\) at fixed \(P\) is \((3A-S)^2/3\ge0\), and its derivative in \(P\) is strictly positive. Montgomery then proves the same unique shape conclusion without using (2).

## Comparisons and replay

The classical quadratic moment is \(p_{L,2t}(0)\) by the heat semigroup and symmetry, so Montgomery handles it directly. Bétermin, Faulhuber, and Steinerberger's [heat-kernel polarization theorem](https://doi.org/10.1017/fmp.2026.10040) concerns the *spatial minimum* of the kernel, not the third or fourth integrated moments here. [Cho–Jang](https://arxiv.org/abs/2610.37520) analyze Fisher geometry and compare quadratic distance to equilibrium; that does not imply this parity-gluing argument or an all-time Shannon claim. These are distinctions of statements, not claims of exhaustive literature priority.

Run **node verify-planar-heat-parity-moments.js** for exact integer shell tests of the parity transformations, rational checks of the uniform bounds and the comparison polynomial, and numerical checks of parity order, Poisson reciprocity, and the moment comparisons on generated planar fixtures. The all-width and all-shape statements are analytic given Montgomery's theorem and the standard Jacobi product.
