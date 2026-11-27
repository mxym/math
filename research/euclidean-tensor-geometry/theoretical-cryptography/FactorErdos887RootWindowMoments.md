# First and second moments of the one-sided root-window divisor count (Erdős #887)

Fix \(C>0\), and define
\[
 R_C(n)=\#\{d\mid n:\sqrt n<d<\sqrt n+C n^{1/4}\}.
\]
This note does not solve the pointwise absolute-bound question in [Erdős #887](https://www.erdosproblems.com/887). It gives the first two aggregate moments at the conjecture's critical \(n^{1/4}\) window scale, including an explicit collision constant and an \(O_C(X^{1/4})\) error.

**Theorem.** For fixed \(C>0\) and \(X\to\infty\),
\[
 \sum_{n\le X}R_C(n)
 =\frac{4C}{3}X^{3/4}-(C^2+\tfrac12)X^{1/2}+O_C(X^{1/4}),
 \tag{1}
\]
and
\[
 \sum_{n\le X}\binom{R_C(n)}2
 =J(C)X^{1/2}+O_C(X^{1/4}),\qquad
 J(C)=\sum_{\substack{u,v\ge1\\uv<C^2}}
       \frac{\varphi(u)}{u}\operatorname{arcosh}\!\left(\frac{C}{\sqrt{uv}}\right).
 \tag{2}
\]
Here \(\varphi\) is the Euler totient, and an empty sum is zero. As a separate limit of the coefficient, \(J(C)=\frac{12}{\pi^2}C^2\log C+O(C^2)\) as \(C\to\infty\). The error in (2) is only for fixed \(C\).

For \(0<C\le\sqrt 2\), there are at most two upper divisors per integer. Thus in this range
\[
 \#\{n\le X:R_C(n)=2\}=J(C)X^{1/2}+O_C(X^{1/4}),
\]
where \(J(C)=0\) for \(C\le1\) and \(J(C)=\operatorname{arcosh} C\) for \(1<C\le\sqrt2\). Moreover
\[
 \#\{n\le X:R_C(n)\ge1\}
 =\frac{4C}{3}X^{3/4}
  -(C^2+\tfrac12+J(C))X^{1/2}+O_C(X^{1/4})
 \quad (0<C\le\sqrt2).
 \tag{3}
\]
For every fixed \(C>0\) one gets \(\#\{n\le X:R_C(n)\ge1\}=(4C/3)X^{3/4}+O_C(X^{1/2})\). For every fixed \(C>1\) the order of the number with two or more is exactly \(X^{1/2}\); for \(C\le1\) there are none.

## 1. First moment

For a factorisation \(n=ab\) with \(b>a\) the normalised upper displacement is
\[
 D(a,b)=\frac{b-\sqrt{ab}}{(ab)^{1/4}}
       =\sqrt a\left[(b/a)^{3/4}-(b/a)^{1/4}\right].
\]
It is strictly increasing in \(b\) for fixed \(a>0\). With \(b=a+s\), there is a single real \(s_C(a)>0\) with \(D(a,a+s_C(a))=C\). By comparing \(s\) with fixed multiples of \(\sqrt a\) we first get \(s_C(a)\asymp_C\sqrt a\) for large \(a\). The quadratic term in the Taylor expansion of \((1+h)^{3/4}-(1+h)^{1/4}\) vanishes. Hence
\[
 D(a,a+s)=\frac{s}{2\sqrt a}+O_C(a^{-1})\quad(s=O_C(\sqrt a)),
 \qquad s_C(a)=2C\sqrt a+O_C(a^{-1/2}).
\]
The number of positive integers \(s<s_C(a)\) therefore differs from \(\lfloor2C\sqrt a\rfloor\) only when \(2C\sqrt a\) lies within \(O_C(a^{-1/2})\) of an integer. For \(a\le T\), there are \(O_C(\sqrt T)\) such \(a\): for each possible integer \(j=O_C(\sqrt T)\), squaring shows \(|a-(j/(2C))^2|=O_C(1)\). The finitely many small \(a\) can be absorbed into the error. This reasoning includes equality cases in the strict inequality.

Put \(T=\sqrt X\). Without the upper restriction \(a(a+s)\le X\), the sum of these counts for \(a\le T\) is
\[
 \sum_{a\le T}\lfloor 2C\sqrt a\rfloor+O_C(\sqrt T)
 =\frac{4C}{3}T^{3/2}-\frac12T+O_C(\sqrt T).
 \tag{4}
\]
To see the second equality, replace the monotone floor sum by its integral with error \(O_C(\sqrt T)\), then use \(v=2C\sqrt a\). The integral of the fractional part is \(T/2+O_C(\sqrt T)\), since \(\int_0^V(\{v\}-\tfrac12)v\,dv=O(V+1)\), by integrating over individual unit intervals.

The product restriction removes counts only for \(a=T-t\) with \(0\le t=O_C(\sqrt T)\). On that strip its upper limit for \(s\) is \(T^2/a-a=2t+O_C(1)\), while the window permits \(s<2C\sqrt T+O_C(1)\). The lost count at \(a\) is \((2C\sqrt T-2t)_++O_C(1)\), where \(z_+=\max(z,0)\). The integral of this triangular profile is \(C^2T\), and the lattice and pointwise errors are \(O_C(\sqrt T)\). Subtracting from (4) proves (1).

## 2. Collisions as a two-dimensional lattice count

Take two distinct upper divisors \(b_1<b_2\), and set \(a_i=n/b_i\). Then \(a_1>a_2\). Their greatest common divisor \(g=\gcd(a_1,a_2)\) gives a unique presentation
\[
 a_2=gs,\qquad a_1=g(s+u),\qquad
 b_1=(g+v)s,\qquad b_2=(g+v)(s+u),
 \tag{5}
\]
where \(g,s,u,v\) are positive integers, \(\gcd(s,u)=1\), and \(vs>gu\). In fact the equality of the two products first forces \(b_1=hs,\ b_2=h(s+u)\) for some \(h\); the strict inequality \(b_1>a_1\) gives \(h>g\) and \(v=h-g>0\). Conversely every such tuple is exactly one unordered pair of strictly upper divisors of its indicated \(n\), and both fit the window exactly when \(D(a_2,b_2)<C\) because \(b_2\) is larger. This bijection counts divisor pairs, not necessarily distinct integers.

In (5), the Cauchy–Schwarz inequality gives
\[
 \sqrt{(g+v)(s+u)}-\sqrt{gs}\ \ge\ \sqrt{uv}.
\]
The displacement \(D(a_2,b_2)\) is this square-root difference multiplied by \((b_2/a_2)^{1/4}>1\). Consequently \(uv<C^2\) is an exact necessary condition. Fix one of these finitely many \((u,v)\).

Let \(Y=X^{1/4}\), \(w=gs\), \(t=vs/(gu)>1\). For a tuple satisfying \(D(a_2,b_2)<C\), the bound \(\sqrt{b_2}-\sqrt{a_2}< C\) shows
\[
 vs+gu+uv=b_2-a_2<C(2\sqrt{gs}+C).
\]
It follows that \(g\asymp_C s\) and, since \(n\ge(gs)^2\), that \(s,g=O_C(Y)\). In this comparable range,
\[
 D(a_2,b_2)
 =\frac{vs+gu}{2\sqrt{gs}}+O_C(g^{-1})
 =\frac{\sqrt{uv}}2(\sqrt t+1/\sqrt t)+O_C(g^{-1}).
 \tag{6}
\]
This follows by the first-order Taylor expansion of \(D\) at \(b_2/a_2=1\), using \(b_2-a_2=vs+gu+uv=O_C(g)\). The term \(uv/(2\sqrt{gs})\) is part of the error.

Write
\[
 T_{u,v}=\left(\frac C{\sqrt{uv}}+\sqrt{\frac{C^2}{uv}-1}\right)^2>1 .
\]
We claim the actual \((g,s)\) count differs by \(O_C(Y)\) from the count in the ideal region \(0<w\le Y^2,\ 1<t<T_{u,v}\), in both cases imposing \(\gcd(s,u)=1\). In this ideal region \(s,g\) are also comparable. In either comparable range \(\sqrt n =w+O_C(\sqrt w)\) and \(w\le Y^2\). A disagreement at the product cutoff is therefore restricted to \(Y^2-O_C(Y)\le w\le Y^2\); here \(g\asymp_C Y\), and there are \(O_C(1)\) possible \(s\) per \(g\). A disagreement at the \(C\) cutoff of (6) can occur, for every sufficiently large \(g\), only when \(t\) is \(O_C(1/g)\) from \(T_{u,v}\): the leading function is strictly increasing for \(t>1\) and has strictly positive derivative at \(T_{u,v}>1\). This puts \(s\) within \(O_C(1)\) of a fixed multiple of \(g\). Bounded \(g\) add only \(O_C(1)\) points. These estimates give the asserted error without relying on whether a boundary lattice point is included.

For each integer \(g\) in the ideal region, the allowed \(s\) lie in an interval with length
\[
 \max(0,\min(\beta g,Y^2/g)-\alpha g),
 \qquad \alpha=u/v,\quad \beta=\alpha T_{u,v}.
\]
The coprimality condition selects a proportion \(\varphi(u)/u\) with an \(O_u(1)\) discrepancy in each interval, by periodicity modulo \(u\). The function giving interval length is piecewise monotone with total variation \(O_C(Y)\), so summing it over \(g\) instead of integrating changes the answer by \(O_C(Y)\) as well. The area is especially simple in \((w,t)\) coordinates: \(s=\sqrt{(u/v)wt}\), \(g=\sqrt{(v/u)w/t}\) have absolute Jacobian \(1/(2t)\). Thus it is
\[
 \int_0^{Y^2}\int_1^{T_{u,v}}\frac{dt\,dw}{2t}
 =Y^2\operatorname{arcosh}\!\left(\frac C{\sqrt{uv}}\right).
\]
Summing over \((u,v)\) proves (2).

## 3. Narrow windows and the large-\(C\) coefficient

For any upper divisor \(b\), the sum of its two complementary factors satisfies
\[
 0<b+n/b-2\sqrt n=\frac{(b-\sqrt n)^2}{b}<C^2
\]
whenever \(b\) lies in the window. As \(b\) increases above \(\sqrt n\), the sum is strictly increasing and integer-valued on divisors. Thus \(R_C(n)\le\lceil C^2\rceil\) for all \(n\), the strict-endpoint version of the classical sum-of-factors bound. For \(C\le\sqrt2\) this is at most two, so subtracting (2) from (1) counts the integers with a nonempty window and proves (3). For larger fixed \(C\), an integer with two or more contributes between 1 and \(\binom{\lceil C^2\rceil}{2}\) to (2), so their order is \(X^{1/2}\) whenever \(J(C)>0\), i.e. \(C>1\). The \(O_C(X^{1/2})\) difference between the first moment and the number with at least one follows since \(r-1\le\binom r2\) for \(r\ge1\).

For the iterated large-\(C\) limit, set \(A(Z)=\sum_{uv\le Z}\varphi(u)/u\). Then
\[
 A(Z)=Z\sum_{u\le Z}\frac{\varphi(u)}{u^2}+O(Z)
     =\frac6{\pi^2}Z\log Z+O(Z).
\]
The second equality follows by inserting \(\varphi(u)/u=\sum_{d\mid u}\mu(d)/d\) and evaluating the inner harmonic sum. Write \(Z=C^2\) and \(h(t)=\operatorname{arcosh}(t^{-1/2})\) on \(0<t\le1\); its derivative is \(-1/(2t\sqrt{1-t})\). Partial summation gives
\[
 J(C)=\frac12\int_1^Z\frac{A(x)}{x\sqrt{1-x/Z}}\,dx
     =\frac6{\pi^2}Z\log Z+O(Z),
\]
since the integral of \((1-t)^{-1/2}\) over \((0,1)\) is 2 and that of \(|\log t|(1-t)^{-1/2}\) is finite.

## Prior work and scope

* Erdős–Rosenfeld, [*The factor-difference set of integers*](https://bibliotekanauki.pl/articles/1390928.pdf), Acta Arith. **79** (1997), 353–359, Section 4 and Proposition 4.1, use the complementary-factor sum for a pointwise bound and give explicit examples with four nearby divisors. Equations (1)–(2) address their nearby scale in aggregate: Proposition 4.1 does not yield the collision constant.
* Chan, [*Factors of almost squares and lattice points on circles*](https://arxiv.org/abs/1406.2230), studies uniform bounds for special almost-square families. The [recent #887 report](https://erdosproblemaday.com/report/887) uses a Pell family for five nearby divisors, not the moments of all integers. Neither is replaced by these counts. No claim is made here about a general absolute \(K\) or the exact frequency of three or more near-root divisors.
* The exact-arithmetic companion tests the factor-pair bijection and its boundary handling for several rational \(C\). Its numerical main-term values are sanity checks, not proofs of the asymptotic.
