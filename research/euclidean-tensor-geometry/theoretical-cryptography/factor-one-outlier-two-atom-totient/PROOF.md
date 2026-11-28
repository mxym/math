# Proof

## 1. The two-atom equation

Put \(m=k-1\), let
\[
 a=\left(\prod_{i=1}^{m}p_i\right)^{1/m},
 \qquad N=a^mq,
\]
and define
\[
 y(x)=N/x^m,\qquad
 G(x)=m\log(x-1)+\log(y(x)-1)
\]
on \(1<x<N^{1/m}\). Direct differentiation gives
\[
 G'(x)=
 \frac{m(y(x)-x)}{x(x-1)(y(x)-1)}.                        \tag{1}
\]
Thus \(G\) strictly increases up to \(u=N^{1/k}\) and strictly
decreases afterwards. At both endpoints it tends to \(-\infty\).

Write \(u'=T^{1/k}\). Maclaurin's inequalities applied to the distinct
positive integers \(p_i-1\) give
\[
 N>(1+u')^k,
\]
so \(u-u'>1\). Equivalently,
\[
 G(u)=k\log(u-1)>\log T.
\]
Therefore \(G(x)=\log T\) has exactly two roots, one on each side of
\(u\). Clearing denominators gives the integer polynomial equation
\[
 (x-1)^m(N-x^m)-Tx^m=0.                                  \tag{2}
\]
It has fixed degree \(2m\), so both roots can be isolated
deterministically in time polynomial in \(\log N\).

## 2. One branch locates the outlier

Let \(z_i=\log p_i\), \(\bar z=m^{-1}\sum_i z_i=\log a\), and
\[
 h(z)=\log(e^z-1).
\]
Since
\[
 h''(z)=-\frac{e^z}{(e^z-1)^2},
\]
Taylor's theorem on the fixed comparable-factor interval gives
\[
 0\le E:=
 m h(\bar z)-\sum_{i=1}^m h(z_i)
 =G(a)-\log T
 \le C_{k,c,C}\frac{W^2}{X^3}.                            \tag{3}
\]
The left inequality is strict unless the clustered factors coincide.

If \(q>a\), the relevant root \(s\) lies below \(a\), and
\(t=y(s)>q\). If \(q<a\), the relevant root lies above \(a\), and
\(t<q\). The two algebraic roots are both tried.

At any solution,
\[
 \frac TN=(1-1/s)^m(1-1/t).
\]
The true factors are comparable, so \(T/N\ge1-O_k(1/X)\). Each factor
on the right is at least their product; hence \(s,t\gg X\). The product
identity \(s^mt=N\) then also gives \(s,t\ll X\), including throughout
the segment between \(s\) and \(a\).

Along the relevant segment,
\[
 |y(x)-x|\ge |q-a|\ge\delta X.
\]
Using (1), (3), and the mean-value theorem,
\[
 |s-a|\le C_{k,c,C,\delta}\frac{W^2}{X},
 \qquad
 |t-q|\le C_{k,c,C,\delta}\frac{W^2}{X},                  \tag{4}
\]
where the second inequality also uses
\(|y'(x)|=my(x)/x=O_{k,c,C}(1)\).

Under the promise (1), the exponent in (4) is
\[
 \frac4{k-1}-1<\frac2k\qquad(k\ge4).                      \tag{5}
\]
Fixed-degree exact root isolation, followed by interval evaluation of
\(t=N/s^m\), supplies rational approximations with absolute error below
one.

## 3. Classical unknown-divisor recovery

First suppose \(\gcd(N,T)=1\). Put \(M=NT\). For an integer center \(B\),
CRT constructs \(C_B\) with
\[
 C_B\equiv B\pmod N,\qquad
 C_B\equiv B-1\pmod T.                                   \tag{6}
\]
For \(w=q-B\), (6) gives
\[
 q(q-1)\mid w+C_B,\qquad q(q-1)\mid M.                    \tag{7}
\]

Let \(r\) be the current number of prime factors,
\(L=\lceil\log_2M\rceil\), and for large \(M\) take
\[
 \beta=\frac1r-\frac{1+\lceil\log_2L\rceil}{L},\qquad
 R=\frac{\lfloor M^{1/r^2}\rfloor}{L^2}.                  \tag{8}
\]
Fixed comparability implies, for all sufficiently large inputs,
\[
 M^\beta\le q(q-1),\qquad R\le M^{\beta^2}.               \tag{9}
\]
Theorem 1.1 of Cohn--Heninger, which records the
Coppersmith--Howgrave-Graham--May unknown-divisor theorem, finds every
integer \(w\) with \(|w|\le R\) and
\(\gcd(w+C_B,M)\ge M^\beta\), in deterministic polynomial time.

By (4), (5), a polynomial number of adjacent radius-\(R\) center blocks
around each algebraic candidate covers the true \(q\). No width or gap
is required as input: the blocks may be dovetailed by increasing
geometric budget. Every output is checked for primality and divisibility
of \(N\).

After finding \(q\), put
\[
 N'=N/q,\qquad T'=T/(q-1).
\]
The geometric mean \((N')^{1/m}\) lies inside the short cluster. The
same classical CRT small-root procedure, now with \(m\) factors and
radius \(X^{2/m}\) up to fixed polylogarithmic blocks, recovers every
remaining prime.

## 4. The non-coprime case

For sufficiently large comparable factors, no two members of the
\(o(X)\)-width cluster can divide one another minus one. If the outlier
is smaller, every prime divisor of \(\gcd(N,T)\) must be that outlier.
If it is larger, at most one clustered prime can divide \(q-1\), since
the product of two distinct \(\asymp X\) primes exceeds \(q-1=O(X)\).
Thus a nontrivial \(\gcd(N,T)\) is itself one prime factor.

Remove this prime and divide \(T\) by one less than it. If the removed
prime is the outlier, only the ordinary cluster remains. Otherwise the
same one-outlier argument applies to one fewer factor; its permitted
small-root radius is larger. This gives an induction, with the
semiprime quadratic formula as the terminal case. All fixed finite
exceptions can be handled by fixed trial division.

## 5. Counting a promised shell

Fix a small \(\eta>0\) with \((1+\eta)^k<2\). Reserve two disjoint
positive-length subintervals of \([X,(1+\eta)X]\), separated by
\(\Theta(X)\). Choose the outlier in one and the \(m=k-1\) clustered
primes in the other.

Put \(w=X^{2/m}\) and partition the cluster interval into
\(O(X/w)\) cells. If \(n_j\) is the number of primes in cell \(j\), the
ordinary prime number theorem and discrete convexity give
\[
 \sum_j {n_j\choose m}
 \gg_k
 \frac{(X/\log X)^m}{(X/w)^{m-1}}.                        \tag{10}
\]
There are \(\Omega(X/\log X)\) choices for the outlier. Dividing by only
a fixed labeling multiplicity, the number of distinct products is
\[
 \Omega_k\!\left(
 \frac{X^2w^{m-1}}{(\log X)^k}
 \right)
 =
 \Omega_k\!\left(
 \frac{X^{4-2/(k-1)}}{(\log X)^k}
 \right).                                                  \tag{11}
\]
Writing \(Y=X^k\) proves the shell count in the README.

All chosen factors are odd and have ratio below two. If \(p\mid q-1\),
then \(q-1\ge2p\), contradicting \(q<2p\). Hence this shell also has
\(\gcd(N,\varphi(N))=1\).

## 6. Scope

The theorem fixes \(k,c,C,\delta,A\) before input growth, assumes
squarefreeness and one exact numeric totient value, and requires one
separated factor plus a short cluster. It does not cover growing
\(\omega(N)\), repeated prime powers, arbitrary equal-bitlength inputs,
a Carmichael value, or unassisted factoring.
