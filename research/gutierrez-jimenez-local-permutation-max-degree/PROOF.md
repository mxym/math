# Exact maximum-degree test for Gutierrez–Jiménez Urroz Conjecture 1

Fix an odd prime power \(q=p^r>3\). In this note every function on a finite field or its Cartesian powers is represented by its unique polynomial of degree at most \(q-1\) in each variable. Define \(I(x)=x^{q-2}\) (inversion, extended by \(I(0)=0\)); let \(t\) swap \(0,1\) and fix all other field elements. The cited recurrence is
\[
f_1(x_1)=x_1,\qquad f_n=t\big(I(f_{n-1})+I(x_n)\big)\quad(n\geq2).
\tag{1}
\]
It gives local permutations because both \(I\) and \(t\) are permutations and addition is a permutation in each argument separately. Every local permutation has degree at most \(q-2\) in each variable: the coefficient of \(X^{q-1}\) equals minus the sum of the values in that variable, which is zero for a permutation. Since this holds for every specialization, that coefficient vanishes identically. Consequently the only possible monomial of total degree \(n(q-2)\) is the product of all \(x_i^{q-2}\); denote its coefficient by \(c_n\).

**Theorem 1.** For \(n\geq2\) write either \(n=2j+2\) or \(n=2j+3\), with \(j\geq0\). In the first case \(c_n=2s_j\), in the second \(c_n=-4s_j\), where \(s_j\in\mathbb F_p\) is the coefficient of \(u^j\) in the following power series:
\[
S_{p,r}(u)=
\begin{cases}
\displaystyle\frac{1+u}{(1+4u)(1-u)}, & r\geq2,\\[5pt]
\displaystyle\frac{(1+u)(1-(-u)^h)}{(1+4u)(1-u+2u(-u)^h)}, & r=1,\quad h=\frac{p-1}{2}.
\end{cases}
\tag{2}
\]
In particular the proposed maximum holds exactly when \(s_j\ne0\). For \(r\geq2\),
\[
s_j=
\begin{cases}
(3(-4)^j+2)/5 & (p\ne5),\\
2j+1 &(p=5),
\end{cases}
\tag{3}
\]
in the prime field. At \(n=1\), \(f_1\) has degree 1; the theorem addresses the intended nontrivial recurrence \(n\geq2\).

## 1. A coefficient-extraction operator

For a reduced univariate polynomial \(g\),
\[
[X^{q-2}]g=-\sum_{x\in\mathbb F_q}xg(x).
\tag{4}
\]
Indeed, among exponents \(1+i\) with \(0\leq i\leq q-1\), only \(q-1\) yields a nonzero power sum (equal to \(-1\)). Likewise if \(G\) is any reduced polynomial, then
\[
\sum_{z\in\mathbb F_q} z^{q-2}G(y+z)=-G'(y)
\tag{5}
\]
because the only surviving power of \(z\) in the expansion of \(G(y+z)\) is the first. For a function \(g\), let
\[
P(g)=((g\circ t)' )\circ I
\]
where the derivative acts on the reduced representative of \(g\circ t\), and the result is again reduced. Using the bijection \(z=I(x_n)\) in (4), and then (5), yields
\[
[x_n^{q-2}]\,g(f_n)=P(g)(f_{n-1}).
\]
Repeating from \(x_n\) down to \(x_2\) proves
\[
c_n=h_0(P^{n-1}X),\qquad h_0(g)=[X^{q-2}]g.
\tag{6}
\]

Put \(\ell(g)=g(1)-g(0)\) and \(A(g)=g'\circ I\). The difference \(g\circ t-g\) takes the values \(\ell(g)\) at 0 and \(-\ell(g)\) at 1, and is zero elsewhere. Its reduced polynomial is \(\ell(g)((X-1)^{q-1}-X^{q-1})\). Accordingly
\[
P(g)=A(g)+v\ell(g),\qquad
v=\big(X^{q-2}-(X-1)^{q-2}\big)\circ I
=1-\sum_{i=2}^{q-2} iX^i .
\tag{7}
\]
For the last equality, \(X^{q-2}-(X-1)^{q-2}=\sum_{j=0}^{q-3}(j+1)X^j\): expand the binomial using \(\binom{q-2}{j}=(-1)^j(j+1)\) in \(\mathbb F_p\) for \(j\leq q-2\). This identity also follows by comparing coefficients below degree \(q-1\) in \((1+X)^{q-2}=(1+X^q)/(1+X)^2\). Inversion sends \(X^j\) to \(X^{q-1-j}\) for \(1\leq j\leq q-3\), giving (7).

Both \(A\) and \(P\) preserve the span of \(1,X,\ldots,X^{q-2}\). Now \(A(1)=0\), \(A(X)=1\), and
\[
A(X^i)=iX^{q-i}\qquad(2\leq i\leq q-2).
\tag{8}
\]
On the pair of exponents \(\{i,q-i\}\), \(A^2=-i^2\) times the identity. The pair \(\{2,q-2\}\) in \(v\) has coefficients \((-2,2)\), whence
\[
h_0((1-zA)^{-1}v)=\frac{2-4z}{1+4z^2}.
\tag{9}
\]
Here and below inverses of operators are formal power series with constant term the identity.

## 2. Generating function and complete criterion

The even powers have \(\ell(A^{2a}v)=0\): the two monomial coefficients of each pair cancel and the constant contributes zero. For odd powers,
\[
\ell(A^{2a+1}v)=\sum_{i=2}^{q-2}(-i^2)^{a+1}.
\tag{10}
\]
Indeed the coefficient \(-i\) in \(v\) is multiplied by \(i\) when applying \(A\), and the exponent pairing only permutes the indices. If \(r\geq2\), sum over all integers \(i=0,\ldots,q-1\) first. Each residue modulo \(p\) occurs a multiple of \(p\) times, so the sum is zero; removing \(i=0,1,q-1\) gives \(2(-1)^a\). If \(r=1\), the full sum is \((-1)^a\) when \(h\mid a+1\) and zero otherwise, by the multiplicative power-sum rule over \(\mathbb F_p\). Thus
\[
M(z):=\ell((1-zA)^{-1}v)=\frac{2z}{1+z^2}+
\begin{cases}
0&(r\geq2),\\
\displaystyle\frac{z(-z^2)^{h-1}}{1-(-z^2)^h}&(r=1).
\end{cases}
\tag{11}
\]
Let \(g=(1-zP)^{-1}X\). Equation (7) gives
\[
g=(1-zA)^{-1}X+z(1-zA)^{-1}v\ell(g).
\]
But \((1-zA)^{-1}X=X+z\) has \(\ell=1\) and \(h_0=0\). Apply \(\ell\) and then \(h_0\), and use (6) and (9):
\[
\sum_{n\geq1}c_n z^{n-1}
=\frac{z(2-4z)}{(1+4z^2)(1-zM(z))}.
\tag{12}
\]
Substituting (11) and putting \(u=z^2\) yields precisely \((2z-4z^2)S_{p,r}(z^2)\). The partial fraction decomposition for \(r\geq2\) gives (3); when \(p=5\), the denominator is \((1-u)^2\). This proves Theorem 1.

For prime \(q=p\), (2) is a finite-order recurrence and gives an exact test for every input \(p,j\). Its coefficients are periodic from the beginning. More precisely, discard the common factors \((1+u)^2(1+4u)\); the remaining denominator has degree \(h-1\) and is squarefree. For \(D_p(u)=1-u+2u(-u)^h\), \(D_p'(u)=(-u)^h-1\) in characteristic \(p\), so any repeated root is \(-1\), where \(D_p''(-1)=-h\ne0\). The numerator in (2) is also divisible by \((1+u)^2\). At \(u=-1/4\) we have \((-u)^h=(1/4)^h=1\), and \(D_p(-1/4)=3/4\ne0\); hence \(1+4u\) cancels as well. After cancellation the numerator has degree less than the denominator. The roots of the denominator are nonzero; over a splitting field, partial fractions express \(s_j\) as a linear combination of powers of the reciprocal roots. In particular a valid period is the least common multiple of their multiplicative orders. This also gives a finite periodic zero test without recursing through all \(j\).

## 3. Counterexamples, minimality, and checks

For every \(q\) in scope the first four nontrivial top coefficients at \(n=2,3,4,5\) are respectively \(2,-4,-4,8\) in characteristic \(p\). They are all nonzero, so no counterexample has \(2\leq n\leq5\). The first deficit in arity occurs at \((q,n)=(25,6)\): \(s_2=2\cdot2+1=0\) in \(\mathbb F_5\), so \(c_6=0\). For a prime \(p\geq7\), the correction term in (11) first affects \(s_j\) at \(j=h\geq3\), so at \(j=2\) we have \(s_2=10\ne0\). At prime \(q=5\), (2) cancels to \(1/(1+2u)\), giving no zeros for any \(j\). For nonprime \(q\), (3) gives \(s_2=10\) reduced in characteristic \(p\), including \(p=5\) using its separate formula. Thus 25 is the least field order with a failure at \(n=6\). In fact when \(p=5\) and \(r\geq2\), the failures are exactly \(j\equiv2\pmod5\). When \(p=3\) and \(r\geq2\) there are no failures.

For prime \(q=7\), the first five coefficients \(s_0,\ldots,s_4\) of (2) are \(1,5,3,5,0\); therefore \(q=7\) is the smallest field order in scope with any failure and at that order the first failure is \(n=10\). For prime \(q=19\), \(s_3=-38=0\) in \(\mathbb F_{19}\), since the correction occurs only at \(j=h=9\), so \(n=8\) is another failure.

The exact total degrees of these examples can be certified without constructing their multivariate polynomials. For exponents \(0\leq e_i\leq q-2\), a direct application of (4)'s power-sum argument gives
\[
[x_1^{e_1}\cdots x_n^{e_n}]f_n
=(-1)^n\sum_{x\in\mathbb F_q^n} f_n(x)\prod_{i=1}^n x_i^{q-1-e_i}.
\tag{13}
\]
An exact finite replay computes that sum by aggregating partial products over the \(q\) possible values of \(f_i\) at each step, using the actual field operations and (1), independently of (5)–(12). Taking all exponents equal to \(q-2\) except one at \(q-3\) gives:

| \(q\) | \(n\) | lower exponent at variable | coefficient in \(\mathbb F_p\) | exact degree |
|---:|---:|---:|---:|---:|
| 25 | 6 | 5 | 1 | 137 |
| 19 | 8 | 1 | 18 | 135 |
| 7 | 10 | 1 | 3 | 49 |

All have top coefficient zero, so a nonzero one-degree-deficit coefficient certifies the exact degree. The checker also cross-checks the formal operator, rational generating function, and direct weighted sums on prime and nonprime fields, plus direct complete grids on smaller examples. This settles the maximum-degree question for (1), not a claim that the listed exact low degrees describe every failure. The distinct existence question is addressed in [PRIME_FIELD.md](PRIME_FIELD.md).
