# Balanced actual triples prevent a positive-only estimate of Vaughan III

This is a diagnostic for the **actual** unmarked semiprime cell of [UnmarkedSemiprimeDualWeilTypeII.md](UnmarkedSemiprimeDualWeilTypeII.md), not a new Type II cancellation theorem. It says that a strategy discarding all negative reflected Vaughan III coefficients cannot certify a uniform upper deficit of \(0.010M_N\) on this cell. It does not contradict a signed estimate, or claim any Goldbach exception.

Write \(N=2x\), \(I=(x/2,x]\), and \(n=sq\in I\) with genuine primes \(s,q\), \(x^{.10}<s<x^{.14}\). Use the nonnegative exact cell weight \(K(n)=(1-t)(1-2t)^2\), \(t=\log s/\log n\), as in the preceding notes. For the reflected \(m=N-sq\in[x,3x/2)\), consider the actual coefficient remaining after the proved Vaughan III product slice:
\[
 C_{\rm rem}(m;U,V,b)=
   \sum_{\substack{d\ell h=m\\d>U,\,\ell>V,\,d\ell>x^b}}\mu(d)\Lambda(\ell).
\]
The cutoffs can depend on the \(s\)-dyad as previously, provided
\(U\ge x^{.45}\), \(U\le x^{1/2}\), \(1\le V\le x^{.03}\), \(b\le 1/2\).
These include the choices in the previous note (e.g. \(U=x^{1/2-\alpha/4-.006}\)). Define
\[
 P_N=\sum_{\substack{s,q\ {\rm prime}\\ sq\in I,\ x^{.10}<s<x^{.14}}}
                K(sq)\max\bigl(C_{\rm rem}(N-sq;U,V,b),0\bigr),
 \quad
 M_N=\mathfrak S(N)x/(2\log x).
\]

For dyadic \(X\to\infty\), we have
\[
 \liminf_{X\to\infty}
 \frac{\sum_{X\le x\le 2X,\ x\in\mathbb Z}P_{2x}}
      {\sum_{X\le x\le 2X,\ x\in\mathbb Z}M_{2x}}
 \ \ge\ .2304\,\bigl(\log(9/7)-.120+.0144\bigr)>.0335 .
\tag{1}
\]
In particular no large-\(N\) uniform bound \(P_N\le(.010+o(1))M_N\) is possible. This also excludes a majorization by the sum of the positive individual \(d,\ell,h\) terms, which is at least \(P_N\).

## 1. Pointwise identity on actual rank three

For \(X\le x\le2X\) choose distinct primes \(p_1,p_2,p_3\le X^{.44}\) with \(m=p_1p_2p_3\) in its original interval. Necessarily \(p_i\ge X^{.12}\), because \(m\ge X\). Thus every \(p_i<U\), every pair \(p_i p_j\ge X^{.56}>U\), and \(p_i>V\), for large \(X\). The only eligible divisor \(d>U\) with a nontrivial remaining \(\ell\) is a product of two of these primes. Its coefficient is \(+1\), the only \(\ell\) is the third prime, and \(h=1\), \(d\ell=m>x^b\). Therefore \(C_{\rm rem}(m)=\log m\), identically on this chamber. This is true without any distribution assertion about reflected primes.

## 2. Independent PNT product measures before imposing the real target sum

Restrict \(s\) further to \(X^{.105}<s<X^{.135}\), a subset of the physical \(s\)-band throughout the dyadic range at large \(X\). The product label \(q\) is still the actual prime. Let \(\mathcal A_X\) be the measure placing mass \(K(sq)\) at \(sq/X\) for these prime products with \(sq/X\in[1/2,2]\). The smaller factor \(s\) is unique. For each fixed interval \(J\subset[1/2,2]\), PNT with partial summation on the \(q\)-interval gives
\[
 \frac{\log X}{X}\mathcal A_X(J)\longrightarrow
       |J|\, C_s,\qquad
 C_s=\int_{.105}^{.135}\frac{(1-2t)^2}{t}\,dt
       =\log(9/7)-.120+.0144.
\tag{2}
\]
Here the uniform \(q\)-scale is \(X/s\in[X^{.865},X^{.895}]\), and \(\log(sq)=\log X+O_J(1)\). Thus \(K(sq)=(1-a)(1-2a)^2+O(1/\log X)\) with \(a=\log_Xs\), while the PNT density for \(q\) has \(1/((1-a)\log X)\). The error after the \(s\)-sum is \(o(X/\log X)\), from the uniform ordinary PNT on fixed relative intervals and the bounded prime reciprocal sum \(\sum_s1/s\); the latter converges against smooth functions of \(a\) to \(da/a\).

Let \(\mathcal B_X\) place mass \(\log m\) at \(m/X\) for the distinct unordered \(p_1p_2p_3\) of section 1 with \(m/X\in[1,3]\). Then for each fixed interval \(J\subset[1,3]\),
\[
  X^{-1}\mathcal B_X(J)\longrightarrow |J|\, C_3,\qquad
 C_3=\frac{1}{6}\int_{\substack{a+b+c=1\\a,b,c\le .44}}
                                  \frac{da\,db}{abc}.
\tag{3}
\]
Use ordinary PNT uniformly in the third-prime interval on scale \(X/(p_1p_2)\) when the allowed interval is not short (and by sandwiching in intervals of small fixed relative width otherwise). More explicitly, write \(a=\log_Xp_1,b=\log_Xp_2\), and restrict the projected \((a,b)\) to the interior of the displayed triangle, a fixed log-distance \(\epsilon>0\) from its boundary. There the last prime of size \(X/(p_1p_2)\) lies below \(X^{.44}\) with fixed exponent slack regardless of \(m/X\in J\), and has \(1/\log p_3=(1+o(1))/((1-a-b)\log X)\). The uniform PNT for its fixed relative interval and the convergence of the first two prime harmonic measures give the restricted integral. The true projected support fits the triangle expanded by \(O(1/\log X)\); the strip of width \(\epsilon\) outside the inner approximation costs \(O(\epsilon X)+o(X)\) by the same PNT as an upper bound on a full third-prime interval without its extra upper cutoff, and the first two prime harmonic measures. All exponents in this calculation are bounded below by \(.12-o(1)\). Let \(\epsilon\downarrow0\). Divide by 6 for distinct unordered triples. Repeated factors are negligible: if \(p^2 r\asymp X\) then \(p\ge X^{.12}\), so summing the upper bound \(O(X/p^2+1)\) over \(p\le X^{.44}\), even without primality, costs \(O(X^{.88}+X^{.44})\) before the log weight. This also covers \(p^3\).

In the simplex of (3), set \(d_i=.44-a_i\), so \(d_i\ge0\) and \(\sum d_i=.32\). The area in the projected \(da\,db\) convention is \(.32^2/2\). Since \(abc\le 1/27\) by AM–GM,
\[
                 C_3\ge (27/6)(.32^2/2)=.2304.
\tag{4}
\]

For the **joint** average, the measures in (2) and (3) multiply, as each \(n,m\) pair specifies \(N=n+m\) uniquely. Both products are odd, so \(N\) is automatically even, with no loss factor. On the positive chamber, section 1 gives the exact summand \(K(n)\log m\). Take the normalized target region with coordinates \(u=n/X,v=m/X,w=(u+v)/2\):
\[
               1\le w\le2,\qquad w/2<u\le w .
\]
The boundary is a finite union of line segments. Fixed rectangle meshes from inside and outside give the product-measure limit from (2) and (3) and ordinary Lebesgue area; let the mesh tend to zero **after** \(X\to\infty\). The Jacobian \(|\partial(u,v)/\partial(w,u)|=2\) and the area's value \(2\int_1^2(w/2)dw=3/2\) give
\[
           \sum_{X\le x\le2X}P_{2x}
                \ \ge\ (C_sC_3+o(1))\frac{3X^2}{2\log X}.
\tag{5}
\]
No assumption on the distribution of such products *at each target* is made; (5) is a large enough average to refute the proposed uniform positive-only upper.

## 3. Singular-series comparison

Write \(C_2=\prod_{p>2}(1-1/(p-1)^2)\). Expanding
\(\mathfrak S(2x)=2C_2\prod_{p>2,\,p\mid x}(1+1/(p-2))\)
and averaging gives mean \(2C_2\prod_{p>2}(1+1/(p(p-2)))=2\). This is justified by dominated convergence: for each squarefree odd \(d\) in the expansion the fraction of \(x\le Y\) divisible by \(d\) is at most \(1/d\), and the multiplied Euler series is absolutely convergent. Partial summation at weight \(x/(2\log x)\) then gives
\(\sum_{X\le x\le2X}M_{2x}\sim3X^2/(2\log X)\). Combining with (4)–(5) proves (1). For the strict displayed decimal bound one may use
\(\log(9/7)=2\sum_{j\ge0} (1/8)^{2j+1}/(2j+1)>.2513\), giving \(C_s>.1457\) and \(.2304\cdot .1457>.0335\).

The consequence concerns **this upper-bounding strategy for a signed residual**. In particular, some genuinely negative contributions must be retained unless a separate mechanism changes the residual or reallocates the quantitative budget. This is not a lower bound on the actual signed remainder, on the missing prime-mask discrepancy, or on the number of exceptional \(N\).
