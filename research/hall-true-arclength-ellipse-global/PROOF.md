# Global acute-triangle comparison for true perimeter samples on ellipses

**Theorem (exact computer-assisted proof).** For every noncircular Euclidean ellipse, the probability that three independent points sampled uniformly in arc length form an acute triangle is strictly less than \(1/4\). For a circle the probability is \(1/4\). This is a global extremal comparison, not a claim of strict monotonicity with aspect ratio or a result for general convex curves or higher-dimensional ellipsoids.

Take semiaxes \(a\ge b>0\). Use
\[
 q=(a-b)/(a+b),\quad \rho=2q/(1+q^2)=(a^2-b^2)/(a^2+b^2),\quad
 g(x)=|1-q e^{2ix}|,\quad \mu=E g .
\]
Here and throughout \(E\) of a single angle is its uniform circle average. The pullback of arc length under \(x\mapsto(a\cos x,b\sin x)\) has density \(g(x)/\mu\) relative to uniform angle: its speed is \((a+b)g(x)/2\).

## 1. Exact triangle integral

Anchor the first point at parameter \(\alpha\). Write the other two as \(\alpha+2u,\alpha+2v\) modulo \(2\pi\), ordered \(0<u<v<\pi\). The chord to the point at \(\alpha+2u\) is \(2\sin u\,(-a\sin m,b\cos m)\), \(m=\alpha+u\). The direction of \((-a\sin m,b\cos m)\) advances strictly with \(m\) and makes a half-turn in parameter length \(\pi\). The next orthogonal tangent occurs at \(m+h\), with \(0<h<\pi\). Their dot product gives
\[
 h=\pi/2+\beta(m),\qquad \beta(m)=-\arg(1-\rho e^{2im})
      =\sum_{n\ge1}\frac{\rho^n}{n}\sin(2nm).
\]
Indeed \(\cos h-\rho\cos(2m+h)=0\), and \(1-\rho\cos 2m>0\). Thus the anchored angle is obtuse precisely for \(v>u+h\). Put \(L=\pi-h=\pi/2-\beta\), \(r=v-u-h\). Ordering and both doubled parameters give the anchored obtuse probability \(2J/(\pi^2\mu^3)\), with
\[
 J=E_m\int_{u,r\ge0,\ u+r\le L} g(m-u)g(m+u)g(m+u+2\beta+2r)\,du\,dr .
 \tag{1}
\]
This uses the \(\pi\)-periodicity of \(g\). The right-angle equalities and coincident draws have probability zero (a specified tangent direction fixes the third parameter). At most one angle is obtuse, so the acute probability is \(p=1-6J/(\pi^2\mu^3)\). Our target is
\[
 D=J-\pi^2\mu^3/8>0\qquad(q>0).
 \tag{2}
\]
For \(q=0\), \(\beta=0\) and \(g=1\), so \(D=0\).

## 2. Thin ellipses: an elementary tail bound

First take the *same* ellipse geometry but use uniform parameter instead of true arc length (the homeoid law). Then (1) has all three weights equal to one, and \(E L^2/2=\pi^2/8+\tfrac14\sum_{n\ge1}\rho^{2n}/n^2\) by sine orthogonality. Each true arc-length density divided by uniform parameter density is at most \(\pi/2\): actual speed is at most \(a\), and its average is at least \(E[a|\sin x|]=2a/\pi\). Hence
\[
 p\ \le\ \frac{\pi^3}{32}-\frac{3\pi}{16}\sum_{n\ge1}\frac{\rho^{2n}}{n^2}.
\]
If \(q\ge7/10\) then \(\rho\ge140/149\). Already the first ten sum terms, together with \(157/50<\pi<22/7\), give the rational upper bound
\[
 (22/7)^3/32-\frac{3(157/50)}{16}\sum_{n=1}^{10}(140/149)^{2n}/n^2<1/4 .
\]

## 3. Finite majorization of the error for \(0\le q\le7/10\)

Let \(b_n=(-1)^n{1/2\choose n}\); \(b_0=1\) and \(b_n<0\) with decreasing absolute values for \(n\ge1\). Write
\[
 G(x)=\left|\sum_{j=0}^8 b_j q^j e^{2ijx}\right|^2
     =\sum_{|j|\le8}g_j(q)e^{2ijx},\qquad
 g_j(q)=\sum_{a-b=j,\ 0\le a,b\le8} b_a b_b q^{a+b}.
\]
The square-root binomial series before taking the modulus squared has error \(\delta\le (10/3)|b_9|q^9\). Its exact modulus is at most \(\sqrt{1+q}\le\sqrt{17/10}\). In particular the truncated modulus is \(<\sqrt2\) (use \(|b_9|<1/64\)), both \(g,G\) are at most 2, and \(|g-G|\le(2\sqrt{17/10}+\delta)\delta\le3\delta\). The error of a trilinear product of three such factors is at most \(12\|g-G\|_\infty\), and the same bound applies to the difference of the cubed means. By \(E\beta=0, |\beta|\le\pi/2\), \(E L^2/2\le\pi^2/4\). Thus replacing \(g\) by \(G\) in (2) costs at most
\[
 12(\pi^2/4+\pi^2/8)\,3\delta\ \le\ 450 |b_9| q^9 .
 \tag{3}
\]

## 4. Integrating each finite Fourier frequency

Use \(z=e^{2im}\), \(\gamma=e^{2i\beta}=(1-\rho/z)/(1-\rho z)\). Define real functions
\[
 U_{k,M}=E[z^M\gamma^k],\quad V_{k,M}=E[\beta\sin(2Mm+2k\beta)],\quad
 W_M=E[\beta^2\cos(2Mm)] .
\]
The first expectation is real by reflection; \(E[\beta z^M\gamma^k]=i V_{k,M}\). For a triple \((j,k,l)\) of weight indices let
\[
 M=j+k+l,\qquad A=-j+k+l,\qquad B=2l,qquad e_A=(-1)^A,quad e_B=(-1)^B,quad d_M=\mathbf1_{M=0}.
\]
After removing the circle constant in (2), its contribution is \(g_jg_kg_l\) times the row \(T_{M,A,B}\) below:
\[
\begin{array}{c|l}
 (A,B) & T_{M,A,B}\\\hline
 (0,0) & W_M/2\\
 A\ne0, B=0 & (d_M-e_AU_{-A,M})/(4A^2)+V_{0,M}/(2A)\\
 A=0, B\ne0 & (U_{B,M}-e_Bd_M)/(4B^2)+V_{B,M}/(2B)\\
 A=B\ne0 & (e_Bd_M-U_{B,M})/(4B^2)-e_B V_{0,M}/(2B)\\
 AB(A-B)\ne0 & -e_A U_{B-A,M}/[4A(A-B)] +e_Bd_M/[4B(A-B)]-U_{B,M}/(4AB).
\end{array}
\tag{4}
\]
For a direct derivation, let
\[
 I(A,B;L)=\int_{u,r\ge0,\ u+r\le L}e^{2iAu+2iBr}\,du\,dr,\qquad
 P(s)=(e^{2isL}-1)/(2is),\quad P(0)=L .
\]
For \(B\ne0\), direct integration in \(r\) gives \(I=(e^{2iBL}P(A-B)-P(A))/(2iB)\). For \(B=0,A\ne0\), one instead has \(I=(e^{2iAL}-1)/(2iA)^2-L/(2iA)\), and \(I(0,0)=L^2/2\). Multiply by \(z^M\gamma^B\), use \(e^{2iAL}=e_A\gamma^{-A}\), average real parts and substitute \(L=\pi/2-\beta\). The only omitted real constant is \(\pi^2 d_M/8\) in the first row: \(M=A=B=0\) forces \(j=k=l=0\), exactly canceling \(\pi^2 (EG)^3/8\). This also explains why the finite test needs no irrational coefficients.

For \(k>0\), coefficient extraction in \(U_{k,M}\) gives the polynomial
\[
 \sum_{a=\max(0,M)}^k(-1)^a{k\choose a}{k+a-M-1\choose a-M}\rho^{2a-M}.
\]
For \(k<0\) use \(U_{k,M}=U_{-k,-M}\); \(U_{0,M}=d_M\). Also \(V_{0,M}=\operatorname{sgn}(M)\rho^{|M|}/(2|M|)\) for \(M\ne0\), zero otherwise.

Only two quantities in (4) remain nonpolynomial. Set \(N=40\):
1. For \(B\ne0\) use the first \(N\) harmonics of \(\beta\), giving
\[
 \widetilde V_{B,M}=\sum_{n=1}^{N}\frac{\rho^n}{2n}(U_{B,M-n}-U_{B,M+n}).
\]
The error is at most \(\rho^{N+1}/[(N+1)(1-\rho)]\). This appears only with factor \(1/(2B)\), \(|B|\ge2\). The sum of all absolute triple coefficients is at most \((\sum_{j=0}^8|b_j|q^j)^6\le(2-\sqrt{1-q})^6<12\). Since \(\rho\le140/149<16/17\), the total error is at most \(51\rho^{41}/41\).
2. For \(m_0=|M|\), sine product orthogonality gives
\[
 W_M=\sum_{n=1}^\infty\frac{\rho^{2n+m_0}}{2n(n+m_0)}
    -\sum_{n=1}^{m_0-1}\frac{\rho^{m_0}}{4n(m_0-n)}.
\]
In the first sum keep only \(n\le N\). This is a **lower** bound, not an absolute error estimate. It is safe to substitute because \(A=B=0\) forces \(l=0, j=k\), hence the associated multiplier \(g_j^2 g_0\) is nonnegative for real \(q\).

Let \(P(q,\rho)\) be the sum of (4) with these finite substitutions and with both error bounds \(450|b_9|q^9\) and \(51\rho^{41}/41\) subtracted. It follows from (3) and the preceding estimates that \(D\ge P(q,2q/(1+q^2))\).

## 5. Exact sign verification

The supplied standard-library `verify_poly.py` constructs the polynomials specified above using arbitrary-precision integers and rational numbers; the full run takes a few seconds. Its calculation gives
\[
 (1+q^2)^{112}P\!\left(q,\frac{2q}{1+q^2}\right)=q^4 R(q),
\]
where \(R\) has degree 266 and \(R(0)=37/6\). **Every one of the 267 Bernstein coefficients of \(R\) on \([0,7/10]\) is strictly positive.** Explicitly, write \(R(q)=\sum h_j q^j\); the tested coefficient at index \(i\) is
\[
 \sum_{j=0}^i h_j(7/10)^j{ i\choose j}/{266\choose j},\qquad 0\le i\le266.
\]
This is the change of basis obtained by expanding \(x^j\) in the degree-266 Bernstein basis on \([0,1]\). The basis functions are nonnegative and sum to one, so positivity of this finite exact list proves \(D>0\) for \(0<q\le7/10\). The program computes the denominator degree, vanishing order and fourth coefficient from the formula, not by fitting values. No subdivision, floating-point arithmetic, quadrature, or unproved numerical margin is needed. Together with Section 2 this proves (2) on the whole noncircle range.
