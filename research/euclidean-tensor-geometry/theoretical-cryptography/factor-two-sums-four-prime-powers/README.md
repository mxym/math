# Two high-power divisor sums for all integers with at most four prime factors

## Result

> **Theorem.** Let \(n\ge 2\) satisfy \(\omega(n)\le 4\), with arbitrary
> prime multiplicities. Put
> \[
> M=\lceil\log_2 n\rceil,\qquad J=\max(2,M).
> \]
> Given the two exact, nonadaptive values
> \[
> S_1=\sigma(n^J),\qquad S_2=\sigma(n^{2J}),
> \]
> the complete prime-power factorization of \(n\) can be recovered
> deterministically in \(\operatorname{poly}(\log n)\) bit operations.

This is a bounded-\(\omega\) oracle theorem, not an ordinary polynomial-time
algorithm for general integer factorization. It does not claim that two
queries are necessary, or that one query is insufficient on integer inputs.

For \(\omega(n)\le3\), the first sum alone already suffices by the neighboring
\`factor-one-sum-three-prime-powers\` result. The new work here is the
arbitrary-multiplicity four-prime case: an exact \(2+2\) eliminant closes the
nonuniform branch, while two coprime effective cyclic resultants close the
uniform branch.

## 1. Either sum recovers the totient

Write
\[
 n=\prod_{i=1}^k p_i^{a_i},\qquad q_i=p_i^{a_i}.
\]
For every \(L\ge2\),
\[
 \frac{\varphi(n)\sigma(n^L)}{n^{L+1}}
 =\prod_i\left(1-p_i^{-(a_iL+1)}\right)=:P_L.
\]
Moreover
\[
 1-P_L\le\sum_i p_i^{-(a_iL+1)}
 \le\sum_{m=2}^{\infty}m^{-(L+1)}<2^{-L}.
\]
When \(L\ge M\),
\[
 (\varphi(n)+1)(1-P_L)<n2^{-L}\le1,
\]
and hence
\[
 \boxed{\displaystyle
 \varphi(n)=\left\lfloor\frac{n^{L+1}}{\sigma(n^L)}\right\rfloor.}
\]
In particular, \(S_1\) determines \(\varphi(n)\).

The first-sum procedure for \(\omega(n)\le3\) is explicit: prime powers are
recognized by exact roots and AKS; two-prime-power inputs are recovered from
the integer roots of
\[
 H_{a,b}(X)=w^{b-1}X^a(X-1)^b-(dX-w)^b,\qquad
 d=w-\varphi(w);
\]
nonuniform triprimes are split by the equal-order argument below; and a
uniform triprime \(w=(pqr)^a\) is closed by the one-variable resultant in the
neighboring proof. Every candidate is checked against \(w,\varphi(w)\), and
the supplied divisor sum. Thus this procedure can first be run as a verified
candidate generator; if it returns nothing under the promise
\(\omega(n)\le4\), the remaining case has exactly four distinct primes.

## 2. The exact equal-order split

Put
\[
 r=\frac{n}{\gcd(n,\varphi(n))},\qquad
 U=\gcd(n,r^M),\qquad V=n/U.
\]
For every \(p^a\parallel n\), the exponent of \(p\) in \(r\) is either zero or
one. The largest prime divisor of \(n\) belongs to \(r\), so \(r>1\).
Consequently \(r\) is squarefree and
\[
 U=\prod_{p\mid r}p^{v_p(n)}
\]
is a nonempty product of complete prime-power components; \(V\) is the
coprime complementary product.

The support inside \(U\) can be grouped by exponent without factoring \(r\).
Set
\[
 h_j=\frac{\gcd(U,r^j)}{\gcd(U,r^{j-1})}
     =\prod_{\substack{p\mid r\\v_p(n)\ge j}}p,\qquad
 b_j=h_j/h_{j+1}.
\]
Then \(b_j\) is exactly the squarefree product of the primes occurring to
exponent \(j\).

Under the remaining promise \(\omega(n)=4\), the following exhaustive
algorithmic cases result.

* If \(U\) or \(V\) is a prime power, exact-root testing identifies and
  removes it. The residual has at most three distinct primes.
* If \(V>1\) and neither side is a prime power, both sides have exactly two
  distinct primes. If the two primes in \(U\) have different exponents, the
  nontrivial \(b_j\)'s identify them separately. Otherwise
  \(U=u^a\), where the known integer \(u=r\) is squarefree semiprime.
* If \(V=1\), then \(r=\operatorname{rad}(n)\). Any prime \(b_j\) is a
  known singleton and can be removed. If there is more than one exponent
  group and none is prime, the only possible partition is \(2+2\), so one
  knows a block \(u^a\) with squarefree semiprime base \(u\). If there is
  only one group, then \(n=m^a\) with a known squarefree four-prime base
  \(m=r\).

All tests above are exact and polynomial-time. Thus only the last two
branches need new arguments.

## 3. A one-sum eliminant for the \(2+2\) branch

Suppose a known block has the form
\[
 U=u^a=(pq)^a,\qquad V=x^c y^d,\qquad n=UV,
\]
where \(u\), \(a\), and \(V\) are known, while the distinct primes
\(p,q,x,y\) are not. Enumerate \(1\le c,d\le M\). Use only \(S=S_1\) in
this branch and put
\[
 A=aJ,\qquad
 D(X,Y)=X^{c-1}Y^{d-1}(X-1)(Y-1),\qquad
 C=\frac{\varphi(n)}{u^{a-1}}.
\]
At the true pair \((x,y)\),
\[
 C=\varphi(u)D(x,y),\qquad
 p+q=u+1-\frac{C}{D(x,y)}.
\]

Define the monic degree-\(A\) polynomial
\[
 Q_A(Z)=\operatorname{Res}_W
 \left(W^2-ZW+u,\;G_{A+1}(W)\right),
 \qquad G_t(W)=1+W+\cdots+W^{t-1}.
\]
Its value at \(Z=p+q\) is \(G_{A+1}(p)G_{A+1}(q)\). The monicity can also be
seen without a resultant: if \(L_j=p^j+q^j\), then
\(L_j=ZL_{j-1}-uL_{j-2}\), and
\[
 Q_A(Z)=\sum_{i=0}^A u^i+
 \sum_{j=1}^A\left(\sum_{i=0}^{A-j}u^i\right)L_j(Z).
\]

Write \(Q_A(Z)=\sum_{h=0}^A q_hZ^h\), \(q_A=1\), and clear the only
denominator:
\[
 \widetilde Q_A(D)
 =\sum_{h=0}^A q_hD^{A-h}\bigl((u+1)D-C\bigr)^h.
\]
The true primes satisfy the two polynomial equations
\[
 f(X,Y)=X^cY^d-V=0,
\]
\[
 F(X,Y)=D(X,Y)^A S
 -G_{cJ+1}(X)G_{dJ+1}(Y)\widetilde Q_A(D(X,Y))=0.
\]

The eliminant \(E(X)=\operatorname{Res}_Y(f,F)\) is not the zero polynomial.
Indeed \(f(1,Y)=Y^d-V\) is monic, and the product-over-roots formula gives
\[
 E(1)=\prod_{y^d=V}F(1,y).
\]
Since \(D(1,y)=0\),
\[
 F(1,y)=-(cJ+1)G_{dJ+1}(y)(-C)^A.
\]
Every root of \(y^d=V\) has modulus \(V^{1/d}>1\), whereas every zero of
\(G_{dJ+1}\) has modulus one. Hence \(E(1)\ne0\).

The true integer \(x\) is therefore among the rational roots of a nonzero
univariate polynomial. Factor \(E\) over \(\mathbb Q\), retain positive
integer roots, recover \(y\) by an exact \(d\)-th-root test from
\(V/x^c\), and verify. Then
\[
 \varphi(u)=C/D(x,y)
\]
splits \(u=pq\) through
\[
 T^2-(u-\varphi(u)+1)T+u.
\]
Testing every ordered pair \((c,d)\) and verifying primality, distinctness,
product, totient, \(S_1\), and \(S_2\) removes all spurious candidates.

### Polynomial size

Here \(a,c,d\le M\), \(J=O(M)\), and \(A=O(M^2)\).
The polynomial \(F\) has total degree \(O(M^3)\) and polynomial coefficient
height. A coarse Sylvester bound gives
\(\deg E=O(M^4)\) and polynomial coefficient height (for example
\(O(M^6)\) bits suffices). Exact resultants, rational polynomial
factorization, integer-root extraction, and all \(O(M^2)\) exponent trials
therefore take polynomial bit time.

## 4. Two coprime cyclic resultants for the uniform quartic

It remains to treat
\[
 n=m^a,\qquad m=pqrs
\]
with four distinct primes. The split above gives \(m=r\) and \(a\), and
\[
 \varphi(m)=\varphi(n)/m^{a-1}.
\]
Put
\[
 t_1=aJ+1,\qquad t_2=2aJ+1.
\]
Then
\[
 \gcd(t_1,t_2)=1,
\qquad
 S_i=\prod_{\ell\in\{p,q,r,s\}}G_{t_i}(\ell).
\]

Let \(e_j\) be the elementary symmetric functions of the four primes.
The values \(e_4=m\) and \(P(1)=\varphi(m)\) are known, so
\[
 e_3=1-e_1+e_2+m-\varphi(m)
\]
and
\[
 P_{x,y}(T)=T^4-xT^3+yT^2
 -(1-x+y+m-\varphi(m))T+m.
\]
For \(i=1,2\), form
\[
 F_i(x,y)=\operatorname{Res}_T(P_{x,y},G_{t_i})-S_i.
\]
The true pair \((e_1,e_2)\) is an integer zero.

Set \(D_i=t_i-1\). At a nontrivial \(t_i\)-th root of unity \(\zeta\),
the homogeneous linear part of \(P_{x,y}(\zeta)\) is
\[
 \zeta(\zeta-1)\,[\,y-(1+\zeta)x\,].
\]
Thus the degree-\(D_i\) highest homogeneous part of \(F_i\) is
\[
 H_i(x,y)=t_i\prod_{\substack{\zeta^{t_i}=1\\\zeta\ne1}}
 [\,y-(1+\zeta)x\,]
 =t_i x^{D_i}G_{t_i}(y/x-1).
\]
In particular, the coefficient of \(y^{D_i}\) in \(F_i\) is the nonzero
constant \(t_i\).

Now eliminate \(y\):
\[
 E_4(x)=\operatorname{Res}_y(F_1,F_2).
\]
Scaling \(y=xv\) and using the two homogeneities of the resultant shows
that the coefficient of \(x^{D_1D_2}\) in \(E_4\) is
\[
 \operatorname{Res}_v(H_1(1,v),H_2(1,v)).
\]
But \(H_i(1,v)=t_iG_{t_i}(v-1)\), and coprimality of \(t_1,t_2\) gives
\[
 \prod_{\substack{\zeta^{t_1}=1\\\zeta\ne1}}G_{t_2}(\zeta)
 =\prod_{\zeta\ne1}\frac{\zeta^{t_2}-1}{\zeta-1}=1,
\]
because \(\zeta\mapsto\zeta^{t_2}\) permutes the nontrivial
\(t_1\)-th roots. Therefore
\[
 \deg E_4=D_1D_2,\qquad
 \operatorname{lc}(E_4)=t_1^{D_2}t_2^{D_1}\ne0.
\]

Factor \(E_4\) over \(\mathbb Q\), retain integer \(x\), then factor the
fixed-degree-in-\(y\) specialization \(F_1(x,y)\) and retain integer \(y\).
Reconstruct \(P_{x,y}\), accept only four distinct positive prime roots,
and verify both supplied sums. Since \(D_1,D_2=O(M^2)\), this is
deterministic polynomial bit time.

## 5. What one query does not prove

For an equal-multiplicity real quartet, one divisor sum supplies only the
three smooth invariants
\[
 \prod p_i,\qquad \prod(p_i-1),\qquad \prod G_t(p_i).
\]
At every ordered quartet of distinct real \(p_i>1\), their logarithmic
Jacobian has rank three, so the implicit-function theorem leaves a local
one-dimensional positive-real fiber. This is an obstruction to isolating
the quartet by the naive three-invariant algebraic method. It is **not** an
integer collision, an information-theoretic lower bound, or evidence that
one exact sum cannot factor integer quartets.

## 6. Reproducibility and checked scope

The dependency-free checker verifies:

* the sharp totient floor on 7,458 inputs with at most four distinct primes;
* all 10,206 four-prime exponent/cross-divisibility cases in a finite
  classification grid;
* exact \(2+2\) cleared identities and explicit \(E(1)\ne0\) resultants;
* 378 equal-quartic instances with coprime effective indices and exact
  two-sum identities.

A separate symbolic review built full \(2+2\) eliminants, including
\(n=1386\), \(U=77\), \(V=18\), where the true-exponent eliminant has
degree 77, \(E(1)\) is nonzero, and the true root recovers
\((2,3,7,11)\). It also checked cases with two nontrivial exponent groups
and with \(\gcd(c,d)>1\).

The exact prior-art comparison is in \`UPSTREAM.md\`. No absolute priority
claim is made.
