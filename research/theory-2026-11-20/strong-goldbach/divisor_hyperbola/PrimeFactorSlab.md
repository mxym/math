# A signed over-root prime-factor slab for the actual divisor hyperbola

Let \(N\) be a fixed even integer, \(L=\log N\), and \(x+y=N\) with the
true condition \((x,N)=1\). Let \(\Psi=\Psi_N\) be supported in a fixed
compact subinterval of \((0,1)\), with each fixed smooth derivative
bounded by a fixed power of \(L\). Use fixed exponents
\(\alpha,\beta>0\), \(0\le\kappa<\alpha\), with \(P\asymp N^\alpha\),
\(Q\asymp N^\beta\), such that
\[
 E+\tfrac32\kappa<1,\qquad \beta+\kappa<1,\qquad
 E=\max\{\beta+\tfrac12\alpha,\ \tfrac12\beta+\tfrac32\alpha\}.
 \tag{1}
\]
The labels on the two arms are independent: \(A=ap\) with
\(a\le N^\kappa\) and a genuine prime \(P<p\le2P\), and
\(Q<r\le2Q\) with \(r\) an arbitrary integer. Let \(b(a,p)\) and \(c(r)\)
be complex, bounded in modulus by \(\tau_K(a)L^B\), \(\tau_K(r)L^B\),
respectively, for fixed \(K,B\). Independently prescribed subintervals
or extra masks on these labels can be included in the coefficients.

**Proposition.** For some fixed \(\delta>0\), uniformly on these supports,
\[
\begin{split}
 &\sum_{\substack{x+y=N\\ (x,N)=1}}\Psi(x/N)
   \sum_{\substack{a\le N^\kappa,\ P<p\le 2P\\ p\ {\rm prime},\ ap\mid x}}
       b(a,p)\sum_{\substack{Q<r\le2Q\\ r\mid y}}c(r)\\
 &\quad=\varphi(N)\int_{\mathbb R}\Psi(t)\,dt
   \sum_{\substack{a\le N^\kappa,\ P<p\le2P,\ Q<r\le2Q\\
            p\ {\rm prime},\ (apr,N)=(ap,r)=1}}
           \frac{b(a,p)c(r)}{apr}
     +O(N^{1-\delta}).
\end{split}                                                       \tag{2}
\]
The constants can depend on the fixed margins in (1) and the weights.
For example \((\alpha,\beta,\kappa)=(.38,.78,.01)\) has
\(E+\tfrac32\kappa=.985\) and pays literal products up to \(N^{1.17+o(1)}\).
Also \((.399,.795,.001)\) gives \(.9975\) in the same inequality.
The entire dyadic product lies strictly above \(N\) in these examples.
The long label need not be prime or have a prescribed prime factor.

## Proof

Both \(A,r\) are target units on the physical rows. If \((A,r)>1\),
a common prime would divide \(x,y,N\), which is impossible. Also \(p>a\)
for large \(N\), so \(A=ap\) is unique on this support. Open
\((x,N)=1\) by \(\sum_{u\mid(x,N)}\mu(u)\). For fixed small
\(\epsilon_0>0\) with \(\epsilon_0+\kappa+\beta<1\), discarding
\(u>N^{\epsilon_0}\) costs \(N^{1-\epsilon_0+o(1)}\): on the actual
\(u\mid x\) rows all weights and label multiplicities together are
bounded by fixed divisor powers, hence \(N^{o(1)}\) pointwise; sum
the \(O(N/u+1)\) literal multiples over the divisors of \(N\).

Write \(X=N/u\). With \(u\) fixed, the congruence for
\(m=x/(uA)\) is \(m\equiv X\overline{A}\pmod r\).
Poisson, with \(\mathrm e(t)=e^{2\pi it}\) and
\(\mathrm e_r(t)=\mathrm e(t/r)\), gives
\[
 \frac{X}{Ar}\sum_{\nu\in\mathbb Z}
       \widehat\Psi\!\left(\frac{\nu X}{Ar}\right)
       \mathrm e_r(\nu X\overline A).
 \tag{3}
\]
Restoring all \(u\mid N\) in the zero term gives (2), since
\(N\sum_{u\mid N}\mu(u)/u=\varphi(N)\). The omitted unit labels
in this model cost \(N^{1-\epsilon_0+o(1)}\) by the reciprocal
harmonic of the coefficient bounds. In particular no density
model is imposed on \(r\).

Put \(V=X/(aPQ)\). The sum of \(V(1+|\nu|V)^{-2}\) over
\(\nu\ne0\) is \(O(1)\), for small as well as large \(V\).
For \(|\nu|\ge P\) one has
\(|\nu|V\ge X/(aQ)\gg N^{1-\epsilon_0-\kappa-\beta}\).
Arbitrarily many fixed derivatives of \(\Psi\) make these terms
power-small even summed absolutely over all \(a,p,r,u\).
For the remaining nonzero frequencies, \(|\nu|<P<p\) and
\(p\nmid X\), so \(C=\nu X\) is a unit at \(p\).
Reciprocity is exact:
\[
 \mathrm e_r(C\overline A)
       =\mathrm e_A(-C\bar r)\,\mathrm e(C/(Ar)).
 \tag{4}
\]
Since \((a,p)=1\), split by \(r\bmod a\) into its unit classes \(j\).
The factor at modulus \(a\) in (4) is constant of modulus one for
fixed \(p,j\); the factor at \(p\) is \(\mathrm e_p(-C\bar a\bar r)\).
It is considered only on units modulo \(p\). In particular \(p\mid r\),
including \(r=p\) if the intervals overlap, is not inserted.
The target-unit mask on \(r\) is part of \(c(r)\) throughout.

For any common prefix \(t\in[Q,2Q]\), put
\[
 S_{p,j}(\chi;t)=\sum_{\substack{Q<r\le t\\r\equiv j\ (a)}}
                            c(r)\chi(r).
\]
Expanding the inverse phase over the \(p-1\) multiplicative
characters gives principal coefficient \(-1/(p-1)\).
The sum of squared moduli of the normalized expansion coefficients
is exactly 1 by Parseval on the units. Thus the nonprincipal prefix
is bounded by \((\sum_{\chi\ne\chi_0}|S_{p,j}(\chi;t)|^2)^{1/2}\).
Every such character of prime modulus is primitive. The
[classical primitive large sieve](https://doi.org/10.1112/S0025579300004708)
with weights \(p/\varphi(p)\ge1\) gives
\[
 \sum_{P<p\le2P,\ p\ {\rm prime}}\sum_{\chi\ne\chi_0\bmod p}
       |S_{p,j}(\chi;t)|^2
       \ll (Q+P^2)\sum_{r\equiv j\ (a)}|c(r)|^2 .
\]
The interval has length \(O(Q)\); the right side can use the full
dyad instead of the prefix. Cauchy first over the \(O(P)\) true primes
and then over the at most \(a\) classes bounds the sum of absolute
nonprincipal prefixes by
\[
 \sqrt{aP(Q+P^2)}\,\|c\|_2
       \ll \sqrt{a P Q(Q+P^2)}\,L^{O(1)}.                           \tag{5}
\]
The principal prefixes summed over \(p,j\) cost \(O(Q L^{O(1)})\),
using \(\sum_{P<p\le2P}1/(p-1)\ll1\) and the actual \(\ell^1\) norm of \(c\).

Insert the last factor of (4) into the amplitude in (3).
Its supremum plus \(Q\) times the supremum of its \(r\)-derivative
is \(O(L^C V(1+|\nu|V)^{-2})\), by Fourier decay even after the
derivative hits \(\mathrm e(C/(Ar))\). Partial summation uses (5)
at a **common** real prefix inside the integral, not at separate
maximizing endpoints for each modulus. Multiply by the bound for
\(b(a,p)\), sum amplitudes over \(\nu\), and use
\(\sum_{a\le N^\kappa}\tau_K(a)\sqrt a\ll N^{3\kappa/2}L^{O(1)}\).
Nonprincipal and principal costs are then
\(N^{E+3\kappa/2+o(1)}\) and \(N^{\beta+\kappa+o(1)}\), respectively.
The remaining \(u\)'s cost only \(N^{o(1)}\). The errors are strict
powers by (1), proving (2).

This uses an inverse phase at the genuinely prime **shorter
modulus** after reciprocity and arbitrary long divisor coefficients.
It is distinct from [Baker's maximal-numerator result](https://www.impan.pl/shop/en/publication/transaction/download/product/82065)
or [Irving's prime reciprocal bounds](https://arxiv.org/abs/1301.6372)
on both actual prime labels near the root; compare the
[actual two-prime blocks](../nearfull_high_vaughan/JointGiantPrimeInverseBlock.md)
and [near-full prime-reciprocal application](../nearfull_high_vaughan/PrimeInverseAveraging.md).
No general improvement of those estimates is asserted.

## Application to the exact complex-order hyperbola

For bounded complex \(w\), the identity \(\tau_{1+w}=1*\tau_w\)
holds at each integer. In the exact expanded pairing of
\(\tau_{1+w}(x)\) and \(\tau_{1+w}(y)\), (2) evaluates the actual
label sector with \(d=ap\) on the left and \(r\) in the opposite
dyad: set \(b(a,p)=\tau_w(ap)\), \(c(r)=\tau_w(r)\).
There is no second occurrence of \(ap\), and \(r\) can contain
arbitrarily many prime factors. Different sectors cannot be added
where their physical labels overlap.

There is also exact size bookkeeping for the full two-long-divisor
remainder, independent of (2). Fix \(\eta>0\), retain any specified
label selection with \(d\mid x,\ r\mid y,\ d,r>N^\eta\),
independent of \(w\), and a bounded spatial weight.
For \(|w|\le c/(1+\log\log N)\), its genuine expanded sum is
\[
 w^2\!\!\sum_{\substack{x+y=N,\ (x,N)=1\\ p\mid x,\ q\mid y\\ 
                  p,q>N^\eta\ {\rm prime}\\
                  (x,y,p,q)\ {\rm in\ the\ selection}}}
       \Psi(x/N)
  +O_\eta\!\left(N|w|^3(1+\log\log N)
                +N^{1-\eta/4}|w|^2\right).                         \tag{6}
\]
The bounded weight may have either sign, and its supremum is
included in the constant (as is fixed \(c\)).
To prove (6), first keep all prime-power labels \(p^j,q^k\)
in the quadratic coefficient, with weights \(1/j,1/k\).
These are the exact linear terms of \(\tau_w(d),\tau_w(r)\).
All coefficients of \(\tau_v(d)\) in \(v\) are nonnegative, and
\[
 \sum_{d\mid n}\tau_v(d)\log d
       =\frac{v}{1+v}\log n\ \tau_{1+v}(n).
 \tag{7}
\]
This follows one prime power at a time from
\(j\tau_v(p^j)=v\tau_{1+v}(p^{j-1})\), summing in \(j\).
Hence the positive two-long polynomial at
\(v_0=c/(1+\log\log N)\) is \(O_\eta(N v_0^2)\): apply (7)
with denominator \(\eta L\), then Cauchy and
\(\tau_{1+v_0}(n)^2\le\tau_{(1+v_0)^2}(n)\) prime power by prime
power. The elementary bound \(\sum_{n\le N}\tau_{1+s}(n)\le
N\prod_{p\le N}(1-1/p)^{-s}\ll N L^s\), for \(s=2v_0+v_0^2\),
gives the assertion. All degree at least three terms cost at most
\((|w|/v_0)^3\) times this bound. Finally on the opposite leg the sum
of \(1/k\) over \(q^k\mid y,\ q^k>N^\eta\) is at most
\(\log y/(\eta L)\). Actual multiples of \(p^j>N^\eta,\ j\ge2\)
have total \(O_\eta(N^{1-\eta/4})\) by
\(\sum_{j\ge2,p^j>N^\eta}p^{-j}\ll N^{-\eta/4}\), using the
convergent sum of \(p^{-3j/4}\). This proves (6).

The contribution on (1) can thus be priced without completing the
opposite quotient. The rest includes balanced labels beyond the
large-sieve rails, labels without the selected prime-factor
decomposition, and the genuine prime–prime atom \(d=x,\ r=y\)
when \(x,y\) are prime. That atom is **absent** from (2), where
\(ap,r\) are polynomially smaller than their central coordinates.
Neither the whole complex-order pairing nor the sign of its
remaining sector is established.
