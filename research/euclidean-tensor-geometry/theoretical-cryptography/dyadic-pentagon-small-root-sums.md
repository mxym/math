# Small root sums at dyadic conductors: a sharp pentagon-window transition

**Scope.** The symmetric five-root geometric family centered at the
regular pentagon is studied when the conductor is exactly a power of
two. The main result is an infinite-subsequence upper bound with a
logarithmic gain, and an exact law for the rare near cancellations in
a specified pentagon window. It is not a global upper-bound improvement:
Dubickas (2026) already gives the stronger uniform order \(N^{-3/2}\)
for the unrestricted five-term problem. It does not give a global lower
bound or settle Myerson's problem. A separate exact
four-term statement concerns distinct folded coefficient positions.
These are pure statements about cyclotomic sums.

## 1. Dyadic five-term result

Write \(N=2^m\), \(\zeta=\exp(2\pi i/N)\), and put
\[
 S_N(a,b)=1+\zeta^a+\zeta^{-a}+\zeta^b+\zeta^{-b}.
\]
For all four congruence classes of \(m\bmod4\), there are infinitely
many \(m\) in the class and integers \(a,b\) near \(N/5,2N/5\) with
\[
 0<|S_N(a,b)|\ll \frac{N^{-4/3}}{\log N}.\tag{1}
\]
The five exponents can be taken distinct modulo \(N/2\), not merely
modulo \(N\).

The following describes the window and the limiting density.
Set
\[
 \phi=(1+\sqrt5)/2,\quad \phi'=(1-\sqrt5)/2,\quad
 u=5a-N,\quad v=5b-2N,\quad T=u\phi+v,\quad T'=u\phi'+v,
\]
\[
 \rho=N^{1/3},\quad x=\rho T,\quad y=T'/\rho,\quad
 A=\frac{4\pi\sin(\pi/5)}5,\qquad
 B=\frac{2\pi^2(\phi^3-\phi^{-1})}{125}>0.
\]
Fix rectangular bounds \(|x|\le X, |y|\le Y\) with \(Y>0\) and
\(X>(B/A)Y^2\), and define
\[
  Y_0=(5A/B)^{1/3},\qquad Y_1=(10A/B)^{1/3},\qquad
  C_0=B Y_0^2.
\]
This window is of angular size \(O(N^{-2/3})\), with the linear
combination transverse to the cancellation curve restricted more tightly.

**Theorem 1.**

* If \(Y<Y_0\), the scaled magnitude \(N^{4/3}|S_N|\) is bounded
  below by a strictly positive constant on the window for all
  sufficiently large \(m\).
* For \(Y>Y_0\), the logarithmic gain of (1) occurs inside the window,
  infinitely often in each \(m\bmod4\) class. This holds at \(Y=Y_0\)
  as well.
* If \(Y_0<Y<Y_1\), let \(D_r(\tau)\) be the limiting fraction of
  \(m\) in a fixed residue class modulo 4 for which some window
  point satisfies \(N^{4/3}|S_N(a,b)|\le\tau\).
  For all sufficiently small fixed \(\tau>0\) this fraction exists
  and is independent of the residue class. Let \(h_-(\tau)<0<h_+(\tau)\)
  be the two boundary points of
  \(C_0 |e^{-2h}-e^h|\le\tau\). Then
  \[
    D_r(\tau)=\frac{h_+(\tau)-h_-(\tau)}{\log(\phi^4)}
       =\frac{2\tau}{3C_0\log(\phi^4)}+O(\tau^2).\tag{2}
  \]
  If \(Y=Y_0\), replace the numerator by \(h_+(\tau)\); only the
  positive half of the crossing remains.

For linear and quadratic cancellation the critical norm is 5,
not a density assumption on the input lattice. The formula for
small fixed \(\tau\) is a statement about the frequency of **existence**
of a suitable symmetric configuration, not the global minimum
over all possible five-root geometries.

### 1.1 The limit polynomial

Put \(\alpha=a/N-1/5\) and \(\beta=b/N-2/5\).
A direct Taylor expansion of the two cosines gives
\[
 \begin{split}
 S_N(a,b)
  ={}&-4\pi\sin(\pi/5)(\phi\alpha+\beta)\\
     &-2\pi^2(\phi^{-1}\alpha^2-\phi\beta^2)
       +O(|\alpha|^3+|\beta|^3).
 \end{split}\tag{3}
\]
Indeed, \(2\cos(2\pi/5)=\phi^{-1}\),
\(2\cos(4\pi/5)=-\phi\), and
\(\sin(2\pi/5)=\phi\sin(\pi/5)\). The sign of the second
quadratic coefficient is important in the cancellation window.
The identity \(u=(T-T')/\sqrt5\) gives, exactly,
\[
 \alpha=-\frac{y}{5\sqrt5\,\rho^2}
          +\frac{x}{5\sqrt5\,\rho^4},\qquad
 \beta=\frac{\phi y}{5\sqrt5\,\rho^2}
     +\frac{x(1-\phi/\sqrt5)}{5\rho^4}.
\]
In particular \(\rho^4(\phi\alpha+\beta)=x/5\).
Substitution gives the uniform approximation
\[
 \rho^4 S_N(a,b)= G(x,y)+O_{X,Y}(\rho^{-2}),\qquad
 G(x,y)=-Ax+By^2.\tag{4}
\]
All points in a fixed window have \(a=N/5+O_{X,Y}(N^{1/3})\),
\(b=2N/5+O_{X,Y}(N^{1/3})\). At large \(N\) the five exponents
are therefore distinct even modulo \(N/2\): their five ratios
modulo \(1/2\) tend to five distinct points. In the dyadic case
these five signed basis coordinates cannot cancel, since
\(X^{N/2}+1\) is the minimal polynomial of \(\zeta\).
Equivalently, a sum of five dyadic roots is nonzero because all five
reduce to 1 at the prime above 2.

### 1.2 A periodic Minkowski lattice coset

Work in \(\mathcal O=\mathbb Z[\phi]\), with the two real embeddings.
For \(r=N\bmod5\in\{1,2,3,4\}\), the allowed \(T\) lie in the coset
\[
   \mathcal C_r=\{T\in\mathcal O:T\equiv -r(\phi+2)\pmod{5\mathcal O}\}.
\]
Here \(\phi+2=\sqrt5\,\phi\), so every member is a nonzero
multiple of \(\sqrt5\). In particular its absolute norm is a
positive multiple of 5. The norm of \(\sqrt5\) has absolute value
5, and \(\mathcal O/(\sqrt5)\simeq\mathbb F_5\) with
\(\phi\equiv3\). Hence
\[
 \lambda=\phi^4>1,\qquad \lambda'=1/\lambda,\qquad
 \lambda\mathcal C_r=\mathcal C_r .
\]
In fact \(\lambda-1\in(\sqrt5)\), and multiplication by it of any
member of the coset lands in \(5\mathcal O\).
Consequently the scaled lattice coset
\[
  \{(\rho T,T'/\rho):T\in\mathcal C_r\}
\]
is exactly periodic under \(\rho\mapsto\lambda\rho\). Over one
period, write \(\sigma=\rho\lambda^{-j}\in[1,\lambda)\) and use
the equivalent fixed candidates \((\sigma T,T'/\sigma)\).
Only finitely many \(T\) can enter any fixed compact rectangle
during that period: \(|T|\le X,\ |T'|\le\lambda Y\), and the
Minkowski image of \(\mathcal O\) is a discrete rank-two lattice.

If \(G(x,y)=0\) at a candidate, then \(x>0\) and
\[
    |xy|=|\operatorname{Norm}(T)|=(B/A)|y|^3.\tag{5}
\]
Thus no such zero is possible for \(Y<Y_0\).
The finite candidate representation over a compact phase circle
gives a uniform positive gap away from zero in this case; (4)
proves the first assertion of the theorem.

If \(Y<Y_1\), the only possibilities at a zero are
\(T>0,\ |\operatorname{Norm}(T)|=5\).
For such \(T\), division by \(\sqrt5\) is an algebraic integer of
norm \(\pm1\). The positive units of \(\mathbb Z[\phi]\) are exactly
the powers of \(\phi\). An elementary verification is to multiply
a positive unit by a power of \(\phi\) to put it in \([1,\phi)\).
For norm \(+1\) its integer trace lies in \([2,\sqrt5)\) and
forces the unit to be 1; for norm \(-1\) its trace lies in
\([0,1)\), which would again force it to be 1, contrary to the norm.
Therefore the candidates of positive first embedding and absolute
norm 5 are
\[
  T=\sqrt5\,\phi^j,\qquad 3^{j-1}=-r\text{ in }\mathbb F_5 .
\]
There is exactly one such orbit under \(\lambda\) in each coset,
since 3 has order 4 in \(\mathbb F_5^\times\).
As the phase runs around the circle it crosses the zero for this
orbit exactly once: for any representative \(T>0\) the unique
positive scale at the zero satisfies \(\sigma^3=B(T')^2/(AT)\).
Changing \(T\) by \(\lambda\) moves the scale by the inverse
factor. At the zero \(|y|=Y_0,\ x=(B/A)Y_0^2\).
It is interior if \(Y>Y_0\).

### 1.3 Density, the logarithmic gain, and the remaining gap

Write \(h\) for the local displacement of log phase from the norm-5 zero.
On the unique crossing branch,
\[
  x=x_* e^h,\qquad y=y_* e^{-h},\quad |y_*|=Y_0,\qquad
  G=C_0(e^{-2h}-e^h).\tag{6}
\]
Its derivative at zero is \(-3C_0\).
In the window \(Y_0<Y<Y_1\), all other candidate branches on
the compact period have a positive absolute gap away from this
crossing, by (5) and finiteness. Thus at small \(\tau\) the
event in the limit phase consists of the one interval in (2).
At \(Y=Y_0\) it consists of the right half, since
\(|y|=Y_0e^{-h}\) and the restriction on \(X\) is strict.
On the phase circle
\(\log\rho=(m/3)\log2\bmod\log\lambda\), and for each
\(m\bmod4\) the increment divided by the period is irrational.
Otherwise some nonzero integral power of 2 would equal a power
of the unit \(\lambda\), contradictory after taking norms.
The phase is therefore uniformly distributed in log scale in each
class. The error in (4) tends uniformly to zero and for small
fixed \(\tau\) the limiting event boundaries consist of finitely
many points. Sandwiching between the intervals at
\(\tau-\epsilon,\tau+\epsilon\) proves (2) as written. The expansion
of their lengths follows from the nonzero derivative in (6).

For the sharper infinite-subsequence upper bound, one can use an
elementary inhomogeneous approximation observation. For any
irrational step \(\omega\) and target phase \(\theta\), there are
unbounded positive \(j\) with \(j\omega\) within \(O(1/j)\) of
\(\theta\) on the circle, from a prescribed side if desired.
For a continued fraction approximant \(p/q\), the grid
\(\{jp/q:0\le j<q\}\) is uniformly spaced and the displacement
to \(j\omega\) is at most \(1/q\). Choose a grid point on the
desired side between \(2/q\) and \(4/q\) from the target. It
gives the stated approximation with \(j<q\).
The indices have an unbounded subsequence, since a bounded
subsequence would converge to an exactly equal orbit point and
the choice stayed strictly on one side. This argument also handles
a target already on the orbit. Apply it to the irrational increment
with \(m\) advancing in one residue class. Then along infinitely
many \(m\), a window point has \(h=O(1/m)\); at \(Y=Y_0\)
choose the positive side. Equation (4) gives
\(N^{4/3}|S_N|=O(1/m)+O(N^{-2/3})=O(1/\log N)\).
This proves (1) with the stated window and per-residue scope.

There is also an exact bookkeeping reduction for further work
near this single crossing. Write \(q=N^{-2/3}\) and use
\(x=x_*e^h,y=y_*e^{-h}\) in the exact formulas for
\(\alpha,\beta\). The rescaled cosine expression
\(q^{-2}S_N(a,b)\) extends analytically as a real function of
\((q,h)\) near \(q=h=0\): the zero and first-order terms in \(q\)
vanish identically. Its derivative in \(h\) at the origin is
\(-3C_0\). Thus the exact local zero is an analytic moving target
\(h_*(q)=O(q)\), and the exact rescaled magnitude is comparable
to \(|h-h_*(q)|\) there, with fixed multiplicative constants.
Any fixed power gain beyond \(N^{-4/3}\) in the strict window
would require exponentially small hits in the exponent \(m\)
for this inhomogeneous log rotation. Ordinary density does not
prove such hits, and no such claim or global lower bound is made.

## 2. A four-term folded-sparse comparison

This part uses \(N=2n\) even with \(N\ge14\), not necessarily dyadic.
A folded-sparse four-term sum is
\[
    Z=\sum_{j=1}^4 \epsilon_j \zeta^{a_j},\qquad
    \epsilon_j\in\{1,-1\},\quad a_j\text{ distinct modulo }n .
\]
Equivalently absorb the signs into exponents modulo \(N\);
no two exponents agree or are antipodal. Then
\[
        \min |Z| = 4\sin(\pi/N)\sin(2\pi/N).\tag{7}
\]
The minimizers, as root multisets up to global rotation, are
the four terms of \((1-\zeta)(1-\zeta^2)\).

For any constant \(C>0\) and all sufficiently large \(N\)
(depending only on \(C\)), a sum with \(|Z|\le C/N^2\) is more
generally forced to have the shape
\[
    Z=\zeta^r(1-\zeta^a)(1-\zeta^b),\qquad
    a>b\ge1,\quad ab\le C/16,\tag{8}
\]
where the statement is equality of the multiset of the four terms
after expanding, not just equality of their totals. An overall
minus can be absorbed in \(r\).

### 2.1 The sharp minimum

Pair the four terms in any way and put \(s=\pi/N\).
For each pair let its unsigned shortest arc gap in root steps
be \(d_i\in\{1,\ldots,n-1\}\), so its nonzero length is
\(\ell_i=2\cos(d_i s)\). Its midpoint phase is a multiple
of \(s\) of the same parity as \(d_i\). If their directions
differ from opposite by angle \(\delta\in[0,\pi]\), then
\[
       |Z|^2=(\ell_1-\ell_2)^2+
                4\ell_1\ell_2\sin^2(\delta/2).
\]
Here \(\delta/s\) is an integer of the same parity as
\(d_1-d_2\), since \(N\) is even.

If the gaps differ by at least two, monotonicity of the sine
in the cosine difference formula gives
\(|\ell_1-\ell_2|\ge 4\sin s\sin(2s)\), with equality requiring
gaps 1 and 3 and \(\delta=0\).
For adjacent gaps \(d,d+1\), one has \(\delta\ge s\).
Substituting \(\delta=s\) gives exactly \(4\sin^2 s\) for the
right side, by the identity
\(\cos(ds)\cos((d+1)s)=\cos^2((d+1/2)s)-\sin^2(s/2)\).
This is strictly larger than the square of (7) for \(N\ge14\).

If the gaps are equal, \(\delta=0\) would make the pairs
opposite copies and repeat folded positions. Thus
\(\delta\ge2s\). For \(d\le n-2\) one has
\(\ell_i\ge2\sin(2s)\), giving (7) as a lower bound with
equality only at \(d=n-2,\delta=2s\).
For \(d=n-1\), the two folded positions in a pair differ
by one. The case \(\delta=2s\) would make the second pair
an opposite copy after shifting by one step, again repeating
a folded position. Hence \(\delta\ge4s\), which gives (7)
with equality only at \(\delta=4s\).

Rotating the exponent of one endpoint to zero gives the
following equality representatives (with a possible reflection):
\(\{0,1,n-1,n+2\}\) for gaps 1 and 3;
\(\{0,n-2,n+1,N-1\}\) for common gap \(n-2\); and
\(\{0,n-1,n+2,1\}\) for common gap \(n-1\). Each is the expansion
of \((1-\zeta)(1-\zeta^2)\) up to a common root factor.
A reflection gives the same family, because replacing
\(\zeta\) by \(\zeta^{-1}\) in that expanded product
changes it by the common factor \(\zeta^{-3}\).
The displayed product has four distinct folded coordinates and
attains (7).

### 2.2 The complete \(N^{-2}\) window

Among four roots there is a pair with shortest arc gap at most
\(N/4\), so use it as the first pair: \(\ell_1\ge\sqrt2\).
For \(|Z|\le C/N^2\), the other pair has length at least 1
at large \(N\). If the directions are not opposite, the angle
error \(\delta\ge \pi/N\) gives a lower bound of order \(1/N\),
a contradiction. They are therefore opposite, and the pair
gaps \(d_1,d_2\) have the same parity and cannot be equal.
Let \(a=(d_1+d_2)/2\), \(b=|d_1-d_2|/2\). Both are positive
integers with \(a>b\), and the magnitude is
\(4\sin(as)\sin(bs)\ge 16ab/N^2\).
The aligned midpoint condition gives the stated four-term
factorization directly: if the smaller-gap pair is \(p,p+a-b\),
the larger-gap pair is \(p-b+n,p+a+n\), with exponents modulo
\(N\). Their sum is
\(-\zeta^{p-b}(1-\zeta^a)(1-\zeta^b)\). This proves (8).

One consequence for explicitly given four-term signed
polynomials at dyadic roots is a finite search for every
embedding in this small-value window. For a fixed constant
\(C\), there are boundedly many candidate step pairs \(a,b\),
and a constant number of assignments of the four signed
exponents to the expanded product. A Galois embedding is
multiplication of exponents by an odd \(k\bmod N\); after
eliminating the common rotation, membership is a system of three
linear congruences in \(k\). For sufficiently large \(N\), the accepted step pairs
for a fixed threshold \(C/N^2\) are precisely those with
\(4\pi^2ab\le C\), by the sine formula, its limit, and its strict
upper bound at equality. Thus for fixed \(C\) the arithmetic step
uses polynomial bit length in \(\log N\), instead of enumerating
all embeddings. No uniform algorithm in an input threshold
specified to arbitrary accuracy is claimed. This observation is only for the
four-term folded-sparse family.

## Prior work and exact limits of these results

* [Myerson, *How Small Can a Sum of Roots of Unity Be?* (1986)](https://doi.org/10.1080/00029890.1986.11971853)
  asks the underlying questions. [Barber, *Small sums of five roots of unity*, arXiv:2104.15057v2](https://arxiv.org/pdf/2104.15057)
  gives the regular-pentagon perturbation, an \(O(N^{-4/3})\)
  bound for unrestricted conductors and \(O(N^{-7/3})\) infinitely often.
  Barber's proof of the latter selects an integer conductor near
  a real root of a quadratic (Section 5); it does not require or
  ensure an exact power of two. The contribution here is the
  log-periodic unit-lattice analysis with that requirement and
  its critical-radius and density consequences. Barber's
  four-term Proposition 3 permits repeated roots; its extremizer
  has a repetition, excluded by the distinct folded condition here.
* [Dubickas, *Uniform upper bounds for small sums of roots of unity*, Ramanujan Journal 71 (2026)](https://doi.org/10.1007/s11139-026-01482-7)
  proves the stronger global uniform upper bound \(f(5,N)=O(N^{-3/2})\)
  for all sufficiently large conductors, with repetitions allowed. The
  near-pentagon result (1) describes a constrained pattern and does not
  improve that global exponent. Its quantitative content is the window
  threshold/density and the specific occurrence on exact dyadic inputs.
* [Qi Cheng, arXiv:2610.27231v1](https://arxiv.org/pdf/2610.27231)
  considers the same symmetric five-term expression for all
  conductors, bounds the number of unusually small conjugates
  at a much smaller threshold, and separates a conditional
  general lower bound. Here the conductor is explicitly dyadic
  and the target is a constructive upper bound and density in
  a restricted geometric window. Neither the unrestricted
  five-term minimum nor the exceptional-embedding lower-bound
  problem is resolved.
* [Kalogirou, arXiv:2607.06098v1](https://arxiv.org/pdf/2607.06098)
  gives further upper bounds for fixed lengths or with
  divisibility assumptions, distinct from the specified dyadic
  pentagon window. No global novelty claim is made for using
  paired chord geometry or the golden-ratio Taylor expansion.

The companion finite checks validate exact algebraic and numerical
identities on generated mathematical inputs. Density and lower
gap conclusions are proved in the text, not inferred from samples.
