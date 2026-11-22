# A positive true semiprime sector of a wide no-high covariance

Let \(N=2X\) be an individual large even target, \(L=\log N\),
and \(J\subset[1/2,2/3]\) a fixed nondegenerate interval.
Write \(y=N-x\), \(M=|J|N\mathfrak S(N)\), and
\[
 \Pi(n)=(\log n)1_{n\ {\rm prime}},\qquad
 \langle V,W\rangle_J=\sum_{\substack{x\in NJ\\(x,N)=1}}V(x)W(N-x),
 \qquad R_J=\langle\Pi,\Pi\rangle_J.
\]
All scores below keep these true target units.

Use the affine mark construction with the **new** fixed parameters
\[
 \lambda=.0001,\quad k=(1-\lambda)^{-1},\quad
 \rho=.999,\quad b=.4996,\quad v=.498,\quad w=.499.
\]
Thus \(F(t)=(1+kt)C(t)\) on \(t\ge0\), where the fixed smooth \(C\)
equals one through \(.4992\), vanishes from \(b\) on, and is in
\([0,1]\). Let \(\chi\in[0,1]\) be a fixed smooth cap, one through
\(.4985\) and zero from \(w\) on. Use the literal marked scores
\[
\begin{split}
 Q_F(m;n)&=\sum_{d\mid m}\mu(d)F(\log(dN/n)/L),\\
 P_F(n)&=\sum_{\substack{r\mid n,\ r\ {\rm prime}\\N^\lambda<r<n}}
                    (\log r)Q_F(n/r;n),\\
 B(n)&=\sum_{\substack{r\mid n,\ r\ {\rm prime}\\N^\lambda<r\le N^v}}
       (\log r)\sum_{d\mid n/r}\mu(d)F(\log(dN/n)/L)
                                  \chi(\log(rd)/L),\\
 E(n)&=\frac{k}{L}\sum_{\substack{n=r m,\ r\ {\rm prime}\\
                                     r>N^\rho,\ m>1}}
                       (\log r)\Lambda(m),\qquad T=P_F+E-B.
\end{split}                                                       \tag{1}
\]
The physical argument in
[the wide no-high decomposition](../nearfull_high_vaughan/WideLowNoHighRemainder.md)
applies with these parameters: \(P_F+E\) uses exactly the actual
marks \(\le N^\rho\), and \(T(n)=0\) if a genuine prime factor
of \(n\) exceeds \(N^\rho\). In fact any low-mark divisor \(d\)
containing that high prime has zero profile since \(b<\rho\);
otherwise its product \(rd\) divides the high prime's cofactor
and is \(<N^{1-\rho}\), so both \(B\)-caps hold. On the high
mark itself the profile is exactly affine by \(1-\rho<.4992\).
This reasoning does not require squarefreeness.

Let \(a=.204\), \(g=.4979\), and let \(S(n)=\log n\) when
\(n=r m\) is a squarefree product of actual primes \(m<r\) with
\(X^a<m\le N^g\), and zero otherwise.

**Theorem.** At every sufficiently large even target satisfying
\(R_J\le .01M\),
\[
                        \langle S,T\rangle_J<-.036M.              \tag{2}
\]
There is a literal fractional allocation \(0\le h(x)\le1\),
supported on \(S(x)>0\), with
\(\langle hT,T\rangle_J>.0058M\) **including all opponent
signs**. In particular the subpopulation with \(S(x)>0\)
and \(T(y)<0\) contributes \(>.0058M\) to the same
\(T(x)T(y)\) correlation. There are a fixed integer \(K\ge2\)
and \(0<\eta<.001\) for which the further restriction
\[
        y\ {\rm squarefree},\qquad P^-(y)>N^\eta,\qquad
                                      2\le\omega(y)\le K
\]
still leaves \(>.0056M\) of the **signed** allocated
correlation, and hence of the positive physical sector.
There are \(\gg M/L^2\) such genuine rows. Both integers are
composite and have no prime factor exceeding \(N^\rho\).
The statement neither separates exact rank two on the second
arm nor bounds the net \(T\times T\) contribution.

## 1. Actual source and signed short cross

The true central rough anchor in
[the moved affine cutoff, Theorem 1](../moved_affine_cutoff/Proof.md)
gives \(R_J+D_2(a)>.755M\) for two distinct actual prime factors
both above \(X^a\). The central interval is this same \(J\), not
its reflection. Remove the actual semiprime tail with smaller
prime \(>N^g\) by
[the true angular 3.446 upper](../angular_prime_first_composite/Proof.md).
Its ordinary rank-two integral is \(\log((1-g)/g)\), using
\(du/[u(1-u)]\) for the smaller own-log angle. The target and
own-log thresholds differ by \(O_J(1/L)\), paid by fixed
outward collars and then shrinking their widths. Central true
prime nonunits cost \(O(L^2)\). Under the stated hypothesis,
\[
        \langle S,\Pi\rangle_J
          \ge\{.755-.01-3.446\log((1-g)/g)+o(1)\}M .              \tag{3}
\]
Its coefficient is \(>.7160\).

Put \(J_0=\log(g(1-a)/(a(1-g)))\) and
\(c(h)=\prod_{p\mid h,\ p>2}(p-1)/(p-2)\). The genuine
unconditioned source satisfies
\[
        \sum_{\substack{x\in NJ\\(x,N)=1}}S(x)c(x)
                            =(J_0+o(1))|J|N.                    \tag{4}
\]
At each real prime \(m\), use PNT in the actual \(r\)-interval
from \(mr\in NJ\), by partial summation with \(\log(mr)\).
The scale \(N/m\gg N^{.5021}\) is polynomial; the summed
arbitrary-log errors are paid by \(\sum_{m\le N^g}1/m\ll L\).
Both prime labels exceed \(N^{.203}\) for large \(N\); removing
target primes is power-small and \(c(x)=1+O(N^{-.203})\).
After changing the real integration variable to \(x\), the
prime \(m\)-reciprocal harmonic has multiplier
\(\log x/\log(x/m)=(1-\log m/L)^{-1}+O_J(1/L)\).
PNT gives \(J_0=\int_a^g du/[u(1-u)]\), including the harmless
lower threshold \((N/2)^a\). The strict \(m<r\) holds
automatically since \(2g<1\).

Apply the genuine product distribution of
[the whole one-mark transfer, §1](../nearfull_high_vaughan/WholeMarkPrimeTransfer.md)
to the source \(S\). Its two actual factors are the prime \(r\)
weighted by \(\log r\) and the prime \(m\) in its above window,
with multiplier \(\log(rm)/\log r\). Separate the latter via
partial summation in \(r\) and the same real product-interval
reconstruction. This uses the actual reduced mean and allows
fixed divisor powers on the modulus. The ceilings
\(N^{b+\lambda}=N^{.4997}\) and \(N^w\) are below the root.

For the short score \(A_F\) of the one-mark transfer, open its
actual moduli \(d\) and \(dj\), where \(j\le N^\lambda\) is a
prime power. Product BV makes the real principal have the exact
unit mask \(Nx\) at each actual \(x\). The signed one-variable
harmonic has coefficient \(F(0)-(1-\lambda)F'(0)=0\), so
\(\langle S,A_F\rangle_J=o(M)\) by (4). Now
\(A_F=P_F+F(\log(N/y)/L)\Pi\) except on the true support
of proper prime powers \(>N^\lambda\) dividing \(y\),
of size \(N^{1-\lambda/2+o(1)}\). Those rows are paid by fixed
divisor bounds. The central multiplier \(1+O_J(1/L)\) is
discarded only against the true \(O(M)\) angular upper on \(S\Pi\).
Thus
\[
                         \langle S,P_F\rangle_J
                                 =-\langle S,\Pi\rangle_J+o(M).   \tag{5}
\]

Likewise open the true product \(q=rd\le N^w\) in \(B(y)\).
Use the same harmonic as in
[the no-high decomposition, §3](../nearfull_high_vaughan/WideLowNoHighRemainder.md),
with source \(S\). Uniformly at the actual \(x\) the reduced
model is \(-k(v-\lambda)\mathfrak S(Nx)+o(\mathfrak S(Nx))\).
The cap is one on the completed short box
\(d\le\exp((\log L)^4)\), and its full varied tail is allowed
by smooth partial summation. The projected \(r\mid d\)
terms cost a reciprocal prime power, and exclusions \(r\mid Nx\)
cost a polynomially small prime harmonic. No actual common factor
of a mark and its own \(d\) is dropped. By (4) and
\(\mathfrak S(Nx)=\mathfrak S(N)c(x)\) on target units,
\[
                          \langle S,B\rangle_J
                              =-k(v-\lambda)J_0M+o(M).          \tag{6}
\]

## 2. An upper bound on the genuine high opponent

Put \(\delta=1-\rho=.001\) and \(Q=N^{b+\lambda}\). For \(E(y)\)
fix its actual cofactor \(u=y/s>1\) from (1). Thus \(u\le N^\delta\),
\((u,N)=1\), and \(\Lambda(u)>0\). The two prime factors of
every source \(x\) exceed \(N^{.203}\), so \((x,u)=1\) on
this source: the prime underlying \(u\) is at most \(N^\delta\).
No such coprimality is asserted for general semiprime sources.

Use the upper linear sieve for the prime \(s=(N-x)/u\) at level
\(D_u=Q/u\) and sifting range \(z_u=\sqrt{D_u}\). Primes dividing
\(N\) are omitted. Every true \(s>N^\rho\) is above \(z_u\).
After positive sieve majorization drop \(s>N^\rho\) and replace
\(\log s/L\) by its upper bound 1. The resulting actual moduli
are \(ud\le Q\), with \(d\) squarefree. In the true weighted
product-BV error at \(q=ud\), all choices of \(u\) cost at most
\(\tau(q)\) and \(\Lambda(u)\le L\); the upper-sieve coefficients
are at most 1 in absolute value. Thus the total simultaneous
error is \(o(M)\), not a separate bound at every \(u\).

The reduced principal at each fixed actual \(x\) has outside
factor \(1/\varphi(u)\). Its dimension-one prime densities are
\[
       g_{x,u}(p)=
       \begin{cases}
        0,&p\mid Nx,\\
        1/p,&p\mid u,\\
        1/(p-1),&p\nmid Nxu .
       \end{cases}                                               \tag{7}
\]
In fact the congruence \(x\equiv N\bmod ud\) is reduced at
the literal \(ud\), and its reduced model excludes \(p\mid x\).
A prime \(p\mid u\) yields an extra power in the actual modulus,
with ratio \(\varphi(u)/\varphi(up)=1/p\), not \(1/(p-1)\).
The uniform sieve dimension upper condition follows from
\(g_{x,u}(p)\le1/(p-1)\) for \(p>2\) and \(g_{x,u}(2)=0\).
The upper sieve limit at \(s=2\) is \(F_{\rm lin}(2)=e^\gamma\);
see the normalization in
[the central rough lower](../central_rough_chen_2663/Proof.md).
The literal local Mertens product is
\[
 \prod_{p\le z_u}(1-g_{x,u}(p))
    =(1+o(1))\frac{e^{-\gamma}\mathfrak S(Nx)}{\log z_u}\,c'(u),
 \qquad
 c'(u)=\prod_{p\mid u}\frac{(p-1)^2}{p(p-2)}.
\]
Every prime of \(u\) is below \(z_u\); the factors at primes of
\(Nx\) above \(z_u\) cost \(O(L/z_u)\) uniformly. Thus the
sieve main is at most \((2+o(1))\mathfrak S(Nx)c'(u)/\log D_u\)
before the outside \(1/\varphi(u)\). The error is uniform since
\(D_u\ge N^{.4987}\) and the dimension constant above is absolute.
On odd prime powers
\(\sum_{1<u\le N^\delta}\Lambda(u)c'(u)/\varphi(u)=\delta L+O(1)\);
indeed the correction to \(1/u\) is summable with the prime-power
weight. Dropping \((u,N)=1\) in this positive *upper* sum and
using (4) gives
\[
                 \langle S,E\rangle_J
                     \le\left\{\frac{2k\delta J_0}{.4987}
                                        +o(1)\right\}M<.0055M.  \tag{8}
\]
This is a true upper, not an independence estimate for two
actual prime products.

## 3. Same-score positive physical sector

Equations (3), (5), (6), and (8) give (2) by \(T=P_F+E-B\).
The [rational checker](check.py) certifies a strict margin
\(>.036\) before the vanishing errors.

For every actual \(x=r m\) in \(S\), both genuine marks
exceed \(N^\lambda\) and \(m\le N^g<N^v\), while
\(r\gg_J N^{1-g}>N^v\) and \(r\ll_J N^{1-a}<N^\rho\).
The smaller mark's \(d=1\) term is removed by \(\chi=1\)
and its \(d=r\) term has argument
\(\log(N/m)/L\ge1-g>b\). The larger mark is uncapped and
its two arguments are in the exact affine region, as
\(\log(N/r)/L\le g+O_J(1/L)\). Hence
\[
                T(x)=-k\frac{\log m\log r}{L},
                \qquad -T(x)>.162S(x)
\]
for large \(N\), because \(a(1-a)=.162384\) and the smaller
own-log angle is \(\ge a-O_J(1/L)\). There are no other
actual marks on this squarefree row. Set
\[
             h(x)=
       \begin{cases}
           .162\,S(x)/(-T(x)),&S(x)>0,\\
           0,&S(x)=0.
       \end{cases}
\]
This is an actual \([0,1]\)-valued source allocation; in
particular \(hT=-.162\,S\) exactly and
\(\langle hT,T\rangle_J>.0058M\) by (2). The remaining
\(\langle(1-h)T,T\rangle_J\) is not estimated. Since
the fraction \(h\) is nonnegative and at most one,
the full positive physical subpopulation
\(S(x)>0,\ T(y)<0\) satisfies the same lower bound.

For the fixed-rank version use the smooth cap envelope in
[the prime-rank pressure, §3](../nearfull_high_vaughan/WideNoHighPrimeRankPressure.md)
for \(T\) and the fixed-\(m\) estimate in
[the mixed rank reservoir, §2](../nearfull_high_vaughan/WideAffineMixedRankReservoir.md).
At fixed source prime \(m\), the primitive forms are
\(r,N-mr\) at actual interval length \(\asymp_J N/m\), and the
genuine \(r\) is majorized by the \(N^{.01}\)-rough indicator.
The leading prime \(m\) has bounded local cost. Use \(S\le L\)
and the genuine \(m\)-reciprocal sum \(O(1)\). The corrected
Henriot estimate, with \(\theta^{\omega(y)}\), yields
\(\ll_{\theta,F,\chi,J}M\theta^{-K}\) against \(S|T|\) on
\(\omega(y)>K\). To mark an actual \(p\mid y\), \(p\le N^\eta\),
one has \(p\nmid Nm\) and writes \(r=r_0+pj\) with
\(m r_0\equiv N\bmod p\). The primitive forms \(r_0+pj\)
and \((N-mr_0)/p-mj\) have resultant \(N\); their interval
has length \(\asymp_J N/(mp)\gg_J N^{.501}\).
Reset the \(y/p\)-leg weight at every positive \(p\)-power,
extracting the true single \(p\)-factor even upon repetitions.
The additional harmonic
\(\sum_{p\le N^\eta}(|1-e^{it\log p/L}|+\log p/L)/p
\ll \eta(1+|t|)\) yields \(O_{F,\chi,J}(\eta M)\).
In the capped part the frequency \(t\) is a sum of the two
Schwartz frequencies, so the same moment is finite.
All estimates retain the genuine unit masks.

Fix \(K\) and then \(\eta\) so these losses against \(S|T|\)
sum to \(<.0009M\). On the remaining rough rows any repeated
prime square uses a prime \(>N^\eta\), giving \(O(N^{1-\eta})\)
actual integers and a power saving even after divisor weights.
Thus the remaining signed \(S\times T\) sum is \(<-.035M\),
giving \(>.0056M\) on the bounded ranks via the same
\(hT=-.162\,S\). The prime \(y\) score \(T\) vanishes, and
each retained product weight is \(O_K(L^2)\).
