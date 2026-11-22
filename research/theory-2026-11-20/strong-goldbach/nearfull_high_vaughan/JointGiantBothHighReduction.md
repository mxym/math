# The true both-high correlation and its one-prime terms

Let \(N,J,L,x,y,M_N,R_J(N),\Pi,P_F,P_G\) have their meanings
in [the joint derivative identity](JointGiantEndpointDerivative.md)
and [the whole super-root transfer](WholeSuperrootPrimeTransfer.md).
In particular \(\Pi(n)=1_{n\ {\rm prime}}\log n\),
\(x\in NJ\), \(y=N-x\), and every pairing below keeps
\((x,N)=1\). The cutoffs are \(U_i=N^{\lambda_i}\), the
fixed smooth real profile \(i=F,G\) is supported on
\([0,b_i]\), and
\[
    0<b_i\le .002,\qquad 0<\lambda_i<1/2-b_i .
\]
Choose fixed \(\rho\) satisfying
\[
          1/2<\rho\le .518,\qquad \rho+\lambda_F>1,
                  \qquad \rho+\lambda_G>1 .
\]
For example \(\lambda_F=\lambda_G=.497\) and \(\rho=.518\)
are allowed for both \(b_i\le .002\).

Split the true marks in each original composite score into
two disjoint half-open ranges: \(L_F\) uses \(U_F<r\le N^\rho\)
and \(H_F\) uses \(N^\rho<r<x\); define \(L_G,H_G\)
in the same way on the other arm. Thus \(P_i=L_i+H_i\) is a
literal row identity. Write
\(\langle U,V\rangle=\sum_{x\in NJ,\,(x,N)=1}U(x)V(N-x)\).
Set
\[
        F_0=F(0),\quad G_0=G(0),\quad
        a=1-\lambda_F,\quad b=1-\lambda_G,\quad c=1-\rho .
\]

**Theorem.** At each sufficiently large even \(N\),
\[
\begin{split}
 \langle H_F,H_G\rangle={}&G_0\langle L_F,\Pi\rangle
                 +F_0\langle \Pi,L_G\rangle+F_0G_0R_J(N)\\
 &+M_N\big[-F_0G_0+(a-c)F'(0)G_0
                   +(b-c)F_0G'(0)+c^2F'(0)G'(0)\big]+o(M_N).
 \tag{1}
\end{split}
\]
The true prime terms in this formula retain the complete
physical low mark windows. In particular if both profiles
are flat on a fixed interval at zero and \(F_0=G_0=1\),
\[
 R_J(N)= M_N+\langle H_F,H_G\rangle
            -\langle L_F,\Pi\rangle-\langle \Pi,L_G\rangle+o(M_N).
 \tag{2}
\]
Neither of the three genuine correlations on the right is
individually evaluated or given a sign by this identity.
At a hypothetical empty binary target, a lower bound for
their signed difference strictly above \(-M_N\) with a
fixed margin would be sufficient. No such lower bound is
claimed here.

## 1. Unconditioned mean of the actual composite mark

For any fixed \(0<\rho<1\) and any actual real interval
\(\mathcal R=(R_-,R_+]\subset(N^\rho,N]\), let
\[
 B_{F,\mathcal R}(x)=
 \sum_{\substack{r\mid x,\ r\ {\rm prime}\\r\in\mathcal R,\ r<x}}
                 (\log r)\,Q_F(x/r;x),\qquad
 Q_F(m;x)=\sum_{d\mid m}\mu(d)F(\log(dN/x)/L).
\]
If \(F\) is flat on \([0,a_0]\), \(a_0>0\), then uniformly
in both real endpoints,
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}}B_{F,\mathcal R}(x)
                                  =O_{A,F,J,\rho}(NL^{-A})
                           \quad(A>0).                            \tag{3}
\]
For any fixed smooth \(F\), not necessarily flat, the full
window \(\mathcal R=(N^\rho,N]\) has
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}}B_{F,\mathcal R}(x)
                      =-(1-\rho)F'(0)|J|N+o_{F,J,\rho}(N).
 \tag{4}
\]
This calculation uses genuine primes, unrestricted target
radical, and no sieve model for pair correlations.

Fix the actual cofactor \(m>1\), \((m,N)=1\). The mark \(r\)
has the exact interval from \(mr\in NJ\) and \(\mathcal R\).
Classical prime number theorem with its zero-free-region
error, and partial summation against \(Q_F(m;mr)\), give
the real integral over that interval. Use the polynomial
lower bound \(r>N^\rho\) and fixed coefficient variation
\(O_F(\tau(m))\). The aggregate error is arbitrary-log, since
\(\sum_{m\le N}\tau(m)/m\ll L^2\). Removing the primes
\(r\mid N\) costs \(O(L^2\tau(m))\) for each \(m\), hence is
also power-small after summing \(m\ll N^{1-\rho}\).
With \(v=mr\) the resulting expression is, up to these errors,
\[
       \int_{NJ}
         \sum_{\substack{m>1,\ (m,N)=1\\
                          v/R_+\le m<v/R_-}}
                      \frac{Q_F(m;v)}{m}\,dv .                    \tag{5}
\]
The inequalities in \(m\) are the real ones induced by the
half-open prime interval. Endpoint equalities have
measure zero in the integral.

Here is the uniform harmonic calculation needed for (5).
Put \(S=\exp((\log L)^4)\). For \(j=0,1,2\), the tails
after \(S\) of the unit-masked signed moments
\(\sum_{(d,N)=1}\mu(d)(\log d)^j/d\) are
\(O_A(L^{-A})\), uniformly also on any truncated interval
past \(S\). For clarity, write
\(\mu(d)1_{(d,N)=1}=(\mu*h_N)(d)\), where \(h_N(e)=1\)
if every prime factor of \(e\) divides \(N\), and zero
otherwise. In a tail beginning at \(Y\ge S\), for
\(e\le\sqrt Y\) use the ordinary signed Möbius
harmonic tails with log moments at \(Y/e\).
These follow from the classical zero-free-region
Mertens estimate and partial summation. For
\(e>\sqrt Y\) use Rankin with
\(\theta=1/(2\log L)\); uniformly,
\[
 \sum_{e\ge1} \frac{h_N(e)}{e^{1-\theta}}
 =\prod_{p\mid N}(1-p^{-1+\theta})^{-1}
                           \ll (1+\log L)^C .
\]
Indeed \(p\le L^2\) costs a power of \(\log L\) by the
ordinary prime harmonic, and \(p>L^2\) costs \(O(1)\)
since there are \(O(L)\) target primes. Log moments may
be absorbed using half the tilt. The tail \(e>\sqrt Y\)
therefore beats arbitrary powers of \(L^{-1}\).
At zero the Dirichlet series
\(\zeta(1+s)^{-1}\prod_{p\mid N}(1-p^{-1-s})^{-1}\)
gives the zeroth and first log moments \(0\) and
\(-N/\varphi(N)\), respectively. The second absolute
moment through \(S\) is at most \(O((1+\log S)^3)\).

For any real \(N^\delta\le W\le N\), fixed \(\delta>0\),
open \(m=d h\) in the upper prefix of (5), initially
including \(m=1\). Interchange, and at fixed \(h\) remove
\(d>S\) by the uniform unit-masked tails and smooth
partial summation, then sum \(1/h\ll L\) harmonically.
The actual unit harmonic of \(h\) at \(Y=W/d\) is
\[
 \sum_{\substack{h\le Y\\(h,N)=1}}\frac1h
    =\frac{\varphi(N)}N
       \left(\log Y+\gamma+\sum_{p\mid N}\frac{\log p}{p-1}\right)
          +O\!\left(\frac{L\tau(N)}Y\right).
\]
This follows by the exact divisor opening at \(e\mid N\)
and the ordinary harmonic expansion; the omitted \(e>Y\)
in the principal cost \(O(L\tau(N)/Y)\) too.
On \(d\le S\) the floors are power-small, including the
\(\tau(N)=N^{o(1)}\) factor. Taylor expand \(F\) at zero
inside the resulting \(d\)-sum. Its constant part contributes
\(F_0\), by the two moments just computed. The term
\(F'(0)(\log d+\log(N/v))/L\) against the \(\log W\)
part contributes \(-F'(0)\log W/L\); all other linear
terms and the Taylor remainder are \(o(1)\) uniformly.
For these use the absolute fixed log moments up to \(S\),
and \(\sum_{p\mid N}\log p/(p-1)\ll \log L\), by splitting
the prime sum at \(L^2\). Subtract the actual \(m=1\) term
\(F(\log(N/v)/L)=F_0+O(1/L)\). Thus for nonflat \(F\)
the upper prefix with \(m>1\) is
\(-F'(0)\log W/L+o(1)\). In the full window (4) the upper
endpoint \(W=v/N^\rho\) is polynomial, and the lower
endpoint \(v/N<1\) is automatic for \(m>1\).

If \(F\) is flat, no Taylor error is present: it is
exactly \(F_0\) on all \(d\le S\) for central \(v\),
and the \(m=1\) term is exactly \(F_0\).
For either endpoint \(W\ge N^{a_0/2}\) the preceding
argument therefore gives an arbitrary-log zero prefix.
For \(W<N^{a_0/2}\), every \(d\mid m\le W\) is already
in the flat region of the actual profile, so each
\(Q_F(m;v)=0\) for \(m>1\). This proves (3) on
both endpoints of (5), including windows of arbitrarily
small real width, and proves (4) as well.

## 2. Inclusion and exclusion of the same actual marks

The square rail of
[the prime-inverse block](JointGiantPrimeInverseBlock.md)
uses exactly the two low windows and gives
\[
        \langle L_F,L_G\rangle
           =(a-c)(b-c)F'(0)G'(0)M_N+o(M_N).
 \tag{6}
\]
Write \(a_F=F_0-aF'(0)\) and \(a_G=G_0-bG'(0)\).
The two uses of
[the whole super-root transfer](WholeSuperrootPrimeTransfer.md)
have \(\rho+\lambda_i>1\), and refer to the same high
prime-mark windows as (1). With (4) they give
\[
 \langle H_F,P_G\rangle
      =-c F'(0)a_G M_N-G_0\langle H_F,\Pi\rangle+o(M_N),
\quad
 \langle P_F,H_G\rangle
      =-c G'(0)a_F M_N-F_0\langle \Pi,H_G\rangle+o(M_N).
 \tag{7}
\]
The second is applied on the reflected \(J\); its length
and target-unit mask are unchanged. For flat profiles
(3) is a stronger estimate on their unconditioned terms.

By the genuine one-prime calibration in §1 of
[the joint derivative identity](JointGiantEndpointDerivative.md),
with unweighted prime profile \(\Pi\),
\[
 \langle P_F,\Pi\rangle=a_F M_N-F_0R_J(N)+o(M_N),
 \qquad
 \langle \Pi,P_G\rangle=a_G M_N-G_0R_J(N)+o(M_N).
 \tag{8}
\]
Target primes in the two-prime atom change this by at
most a logarithmic error, since the central nonunit
prime-prime row would have \(x=y=N/2\).
Use the full genuine \(\langle P_F,P_G\rangle\)
from the same derivative theorem. The exact algebra is
\[
 \langle H_F,H_G\rangle
   = \langle H_F,P_G\rangle+\langle P_F,H_G\rangle
       -\langle P_F,P_G\rangle+\langle L_F,L_G\rangle .
\]
Inserting (6)–(8), and replacing each high true-prime
cross by its total minus its low true-prime cross,
gives (1). In particular the derivative-by-derivative
coefficient reduces to
\(cb+ca-ab+(a-c)(b-c)=c^2\).
This calculation neither deletes a portion of a true
one-prime term nor adds any overlapping mark rectangles.
