# A calibrated block leaving only no-high rows in the wide low–low remainder

Let \(N\) be any large even target, \(L=\log N\), \(J\Subset(0,1)\) a
fixed nondegenerate interval, and \(M=|J|N\mathfrak S(N)\), with the
binary singular series \(\mathfrak S\). Write \(y=N-x\) and
\[
 \langle V,W\rangle_J=\sum_{\substack{x\in NJ\\(x,N)=1}}V(x)W(y),
 \qquad \Pi(n)=(\log n)1_{\{n\ {\rm prime}\}},\quad R_J=\langle\Pi,\Pi\rangle_J.
\]
Keep the original wide affine profile of
[WholeMarkPrimeTransfer](WholeMarkPrimeTransfer.md):
\[
 \lambda=.006,\quad U=N^\lambda,\quad \rho=.518,\quad k=(1-\lambda)^{-1},
 \qquad F(t)=(1+kt)\chi(t).
\]
The fixed smooth cutoff \(\chi\) equals 1 through \(.486\), 0 from
\(.490\), and takes values in \([0,1]\). Put \(t_d(n)=\log(dN/n)/L\).
The original score and its actual low-mark part on central integers are
\[
 P(n)=\sum_{\substack{r\mid n,\ r\ {\rm prime}\\ U<r<n}}
   (\log r)\sum_{d\mid n/r}\mu(d)F(t_d(n)),
 \qquad \mathcal L(n)=\sum_{\substack{r\mid n,\ r\ {\rm prime}\\ U<r\le N^\rho}}
   (\log r)\sum_{d\mid n/r}\mu(d)F(t_d(n)).
\]
Here \(r<n\) is automatic in \(\mathcal L\). Define literal caps
\(v=.498,w=.499\), and write \(\Delta=v-\lambda=.492\). Put
\[
 B(n)=\sum_{\substack{r\mid n,\ r\ {\rm prime}\\ U<r\le N^v}}
    (\log r)\sum_{\substack{d\mid n/r\\rd\le N^w}}\mu(d)F(t_d(n)),
 \qquad T(n)=\mathcal L(n)-B(n),                                  \tag{1}
\]
and
\[
 E(n)=\frac{k}{L}\sum_{\substack{n=rm,\ m>1,\ r\ {\rm prime}\\ r>N^\rho}}
                       (\log r)\Lambda(m).                       \tag{2}
\]

**Theorem.** Uniformly as \(N\) tends to infinity through the even
integers, \(T(n)=0\) on every central integer having an actual prime
factor \(>N^\rho\), and
\[
 \begin{split}
 \langle\mathcal L,\mathcal L\rangle_J&=c_*M+\langle T,T\rangle_J+o(M),\\
 R_J&=c_*M+\langle T,T\rangle_J-\langle E,E\rangle_J+
       \langle E,\Pi\rangle_J+\langle\Pi,E\rangle_J+o(M),
 \qquad c_*=\frac{261744}{988036}>.264 .
 \end{split}                                                     \tag{3}
\]
The evaluated block in the first line includes all terms on physical
rows with a high prime on at least one side, but also includes terms
with no high prime on either side. It does **not** separately evaluate
the sum over high-containing rows. There is no sign assertion about
\(\langle T,T\rangle_J\). Neither \(\langle E,E\rangle_J\) nor either
genuine prime cross is discarded.

## 1. Physical support and exact decomposition

If \(s\mid n\) is an actual prime \(s>N^\rho\), then \(s^2>N\).
A term of \(\mathcal L(n)\) with \(s\mid d\) has \(F(t_d(n))=0\),
since \(\rho>.490\). Otherwise \(rd\mid n/s\), so
\(r\le rd<N^{1-\rho}=N^{.482}\), satisfying both caps in (1).
Thus \(T=0\) there exactly, with no squarefreeness assumption.
On the high mark \(s<n\) itself, all \(d\mid n/s\) satisfy
\(t_d(n)\le\log(N/s)/L<.482\). The affine score and
\(\sum_{d\mid n/s}\mu(d)=0\),
\(\sum_{d\mid n/s}\mu(d)\log d=-\Lambda(n/s)\) give
\(P=\mathcal L-E\) exactly, keeping proper prime powers in (2).

Here \(F(0)=1,\ F'(0)=k,\ a_F=F(0)-(1-\lambda)F'(0)=0\).
[The two-endpoint correlation](JointGiantEndpointDerivative.md) gives
\(\langle P,P\rangle_J=R_J+o(M)\). Apply
[WholeMarkPrimeTransfer](WholeMarkPrimeTransfer.md) to the actual
high mark \(P-\mathcal L=-E\). Then
\[
 \langle E,P\rangle_J=-\langle E,\Pi\rangle_J+o(M),\qquad
 \langle P,E\rangle_J=-\langle\Pi,E\rangle_J+o(M).                  \tag{4}
\]
The second statement reflects \(J\) to \(1-J\). Thus the second
line of (3) follows from the first.

## 2. Simultaneous CRT on the real short product divisors

Let \(A=A_F\) be the true short-divisor score
\[
 A(n)=\sum_{e\mid n}\mu(e)F(t_e(n))
   \left(\log(n/e)-\sum_{\substack{j\mid n/e\\j\le U}}\Lambda(j)\right).
\]
As in [the two-endpoint correlation, §1](JointGiantEndpointDerivative.md),
\(A=P+\Pi_F\) except on divisibility by a proper prime power
\(>U\), with \(\Pi_F(n)=F(t_1(n))\Pi(n)\). The exceptional support
has size \(O(N^{1-\lambda/2+o(1)})\); every physical score here is
bounded by a fixed divisor power times \(L\). The exception changes
our correlations by \(o(M)\).

In \(B(x)A(y)\) the actual moduli are \(rd\le N^w\) and \(e\)
or \(ej\le N^{.490+\lambda}=N^{.496}\). In \(B(x)B(y)\) both are
\(\le N^w\). On every physical target-unit pair the moduli are
relatively prime and individually coprime to \(N\). For fixed labels
the CRT density is \((\varphi(N)/N)/(q_1q_2)\), after opening target
units over the divisors of \({\rm rad}(N)\). The total floor errors
are \(N^{.995+o(1)}\) and \(N^{.998+o(1)}\), respectively, including
the divisor multiplicities, weights, and partial summation over
the real central interval. There is no extra full \(r\)-sum for a
fixed product modulus.

Use the simultaneous short-\(\mu\) calculation in
[the two-endpoint correlation, §2](JointGiantEndpointDerivative.md).
Here are the exact cutoffs and leading moments for this application.
Fix the genuine prime \(r\) and the opposite short label \(j\)
(or the opposite prime in \(B\times B\)); put \(j=1\) for the
unmarked free-log term. The \(B\)-leg cap \(N^w/r\ge N^{.001}\)
is independent of the real spatial variable and exceeds
\(S=\exp((\log L)^4)\), and the opposite smooth profile is also
supported beyond \(S\) in its divisor. Cut the two signed
\(\mu(d)/d,\mu(e)/e\) tails successively at \(S\), keeping the
full polynomial opposite-modulus mask each time. The cut errors
are arbitrarily log-small, including all absolute divisor and
mark harmonics in the model. In \(B\times A\) one has \(r>U\ge j\),
hence \((r,j)=1\); no coprimality of a divisor with its *own* mark
is imposed. For compatible opposite labels the full masks are
\((d,Nj)=(e,Nr)=(d,e)=1\). Both zeta-inverse zeros in that calculation
annihilate every zeroth harmonic in either variable; the first
log moment on each side, with the target unit factor, is
\[
                    \mathfrak S(N)c(rj),\qquad
 c(a)=\prod_{\substack{p\mid a\\p>2}}\frac{p-1}{p-2}.               \tag{5}
\]
Indeed a prime in exactly one mark is omitted only from the opposite
divisor's Euler factor, producing the indicated factor \(c\).
Higher fixed moments are \((\log L)^{O(1)}\), as in the cited
calculation. Taylor-expand only now on \(d,e\le S\). The first
coefficient on the \(B\)-leg is \(k/L+O(L^{-2})\) before its positive
log mark. On the unmarked \(A\)-leg it is \(k-1+O(L^{-1})\), from
\(F(t_e(y))\log(y/e)\); on the marked \(A\)-leg it is
\(-k/L+O(L^{-2})\) before \(\Lambda(j)\). These retain the true
bounded spatial shifts at the indicated precision. Higher moments
are \(o(M)\): after the constant term vanishes, a higher order on
one leg supplies an additional \(1/L\), and the external marked
harmonics cost \(O(L)\) each. Degree-three Taylor remainder
\(O((1+\log S)^4/L^4)\) is also \(o(1)\) after the absolute short
box harmonics and the two external log powers.

The ordinary PNT and summable local corrections give
\[
 \sum_{\substack{U<r\le N^v\\r\ {\rm prime},\ (r,N)=1}}
           \frac{\log r}{r}c(r)=\Delta L+o(1),\qquad
 \sum_{\substack{j\le U\\(j,N)=1}}\frac{\Lambda(j)}j c(j)
              =\lambda L+O(\log L).                            \tag{6}
\]
In the first sum target deletions are polynomially small; in the
second, the omitted prime-power harmonic is \(O(\log L)\) by
splitting the target's prime factors at \(L^2\), and
\(c(p^a)-1=O(1/p)\) away from 2. Because \(c(rj)=c(r)c(j)\) for
compatible labels, the opposite unmarked and marked coefficients
together are \(k-1-k\lambda=-a_F=0\). Thus
\[
              \langle B,A\rangle_J=o(M),\qquad
              \langle B,B\rangle_J=k^2\Delta^2M+o(M).              \tag{7}
\]
For the second equality apply (6) to both sides; the incompatible
common prime is omitted with power-small principal cost
\(\sum_{r>U}(\log r)^2/r^2\).

## 3. Two genuine-prime distribution calculations

First apply ordinary maximal-prefix Bombieri–Vinogradov to
\(\langle B,\Pi_F\rangle_J\) at modulus \(rd\le N^w\).
Keep \(F(t_1(y))\) inside the real spatial calculation. At fixed
spatial \(x,y\), the reduced principal on the \(B\)-leg has multiplier
\(1/\varphi(rd)\) and mask \((rd,N)=1\). The terms \(r\mid d\)
are power-small in this **principal**, by writing \(d=rd'\),
\((r,d')=1\), and bounding by
\(L^{O(1)}\sum_{r>U}(\log r)/r^2\).
No actual row is dropped. Otherwise
\(\varphi(rd)=(r-1)\varphi(d)\); the zeroth and first log moments of
the masked \(\mu(d)/\varphi(d)\) are respectively \(0\) and
\(-\mathfrak S(Nr)\), with arbitrary-log completion at \(S\), by
[WholeMarkPrimeTransfer, §2](WholeMarkPrimeTransfer.md). The literal
cap admits all \(d\le S\). Taylor expansion after completing the
tail costs \(O((1+\log S)^3/L^2)\) before the \(O(L)\) mark harmonic.
As \(\mathfrak S(Nr)=\mathfrak S(N)c(r)\) on target units, (6)
gives \(-k\Delta\mathfrak S(N)+o(\mathfrak S(N))\) per unit length.
It is only in this evaluated model that \(F(t_1(y))=1+O(1/L)\)
is replaced by 1. Together with (7) this gives
\[
            \langle B,\Pi_F\rangle_J=-k\Delta M+o(M),
       \qquad \langle B,P\rangle_J=k\Delta M+o(M).                \tag{8}
\]

For \(\langle E,B\rangle_J\) apply the genuine product
Bombieri–Vinogradov theorem of
[WholeMarkPrimeTransfer, §1](WholeMarkPrimeTransfer.md), with
source \(x=sm\), \(\alpha(s)=\log s\) on actual primes \(s>N^\rho\),
and \(\beta(m)=k\Lambda(m)/L,\ m>1\). Its modulus is exactly
\(q=rd\le N^w\), with divisor multiplicities and spatial tests
allowed by that theorem. The reduced principal retains
\((x,rd)=1\) as well as \((N,rd)=1\). At each fixed true \(x\),
the previous one-variable calculation therefore has the **actual
even mask \(H=Nx\)**. Terms \(r\mid d\) are again power-small in
the model, and \(r\mid Nx\) costs \(O(L^{O(1)}/U)\) in (6).
The resulting uniform pointwise model is
\(-k\Delta\mathfrak S(Nx)+o(\mathfrak S(Nx))\).

The positive source itself satisfies
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}} E(x)=k(1-\rho)|J|N+o(N),
 \qquad
 \sum_{\substack{x\in NJ\\(x,N)=1}} E(x)|c(x)-1|=o(N).              \tag{9}
\]
For the first formula fix the literal \(m\le N^{1-\rho}\).
Apply genuine PNT on \(s\) at scale \(N/m\ge N^\rho\), keeping
\(s>N^\rho\) by real prefixes. The summed PNT errors are
\(O_A(NL^{-A})\); removing \(s\mid N\) costs at most
\(N^{1-\rho+o(1)}\). At real spatial \(u\in NJ\) the inner harmonic
\(\sum_{1<m<u/N^\rho,(m,N)=1}\Lambda(m)/m\) is
\((1-\rho)L+O_J(\log L)\), by the Mertens harmonic with true target
deletions. For the second formula use \(c(sm)\le c(s)c(m)\),
\(c(s)-1=O(N^{-\rho})\), and
\(\sum_{m>1}\Lambda(m)(c(m)-1)/m<\infty\), since \(m\) is a prime
power. Chebyshev on the true \(s\) sum gives \(O(N/L)\) for the
contribution of \(c(m)-1\). The identity
\(\mathfrak S(Nx)=\mathfrak S(N)c(x)\) is exact on target units,
so (9) gives
\[
                \langle E,B\rangle_J=-k^2\Delta(1-\rho)M+o(M).   \tag{10}
\]
The reflected statement holds on \(1-J\). Proper powers are kept
throughout this calculation.

## 4. Reassemble only once

By \(\mathcal L=P+E\), (8) and (10) give
\[
     \langle B,\mathcal L\rangle_J
      =\langle\mathcal L,B\rangle_J+o(M)
      =k^2\Delta(\rho-\lambda)M+o(M).
\]
The exact decomposition \(\mathcal L=B+T\) gives (3): add the two
mixed values, subtract \(\langle B,B\rangle_J\) from (7), and keep
\(\langle T,T\rangle_J\) exactly once. The coefficient is
\[
  2k^2\Delta(\rho-\lambda)-k^2\Delta^2
   =\frac{.512^2-.020^2}{.994^2}=\frac{261744}{988036}>.264 .
\]
This overlaps the small-mark strips in
[the grouped mark covariance](WideGroupedMarkCovariance.md); it
is not an additional credit to those strips. No separate sign of
rank-two by rank-three rows or asymptotic for actual semiprime by
semiprime rows is required or obtained.

One may alternately take a fixed smooth multiplier in \(\log(rd)/L\)
instead of \(1_{\{rd\le N^w\}}\) in (1), equal to 1 through \(.4985\),
0 from \(.499\), and in \([0,1]\) between. It is identically 1 on
the completed short box \(r\le N^v,d\le S\), and on every actual
high-containing term, and has bounded variation for the longer
signed tails. All the evaluations and exact support statements
remain valid, with \(T\) always taken for the cap actually chosen.
