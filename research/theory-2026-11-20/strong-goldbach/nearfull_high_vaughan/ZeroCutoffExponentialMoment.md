# A true positive prime-row moment from the zero-cutoff boundary

Use the literal notation of
[the polynomial smooth giant reduction](PolynomialSmoothedGiantReduction.md):
\(N\) is an individual even target, \(J\Subset(0,1)\) is fixed and
nondegenerate, \(L=\log N\), \(y=N-x\), and
\(M_N=|J|N\mathfrak S(N)\). Let \(R_J(N)\) be the original weighted
binary prime count. Fix \(0<\lambda<1/2\), put \(b=1/2-\lambda\),
and take \(U=N^\lambda L^{-C_D}\) with a sufficiently large fixed
Bombieri--Vinogradov denominator power. All summands below keep
both \(x,r\) genuine primes, the actual equality \(x+mr=N\), the
literal \(x\in NJ\), the true \(r>U\), and \(m>1\).
The error below does not require any restriction on the radical
of \(N\).

For \(F\) smooth on \([0,\infty)\) and identically zero on
\([b,\infty)\), do **not** require \(F\) to be constant near zero.
Write
\[
 {\cal C}_{\lambda,F}
  =\sum_{\substack{x+mr=N,\ x,r\ {\rm prime},\ x\in NJ\\ r>U,\ m>1}}
    (\log x)(\log r)
       \sum_{d\mid m}\mu(d)F\!\left(\frac{\log(dN/y)}{L}\right).
\]
Then uniformly as \(N\to\infty\) at fixed \(F,\lambda,J\),
\[
 {\cal C}_{\lambda,F}
     = \bigl(F(0)-(1-\lambda)F'(0)\bigr)M_N
                 -F(0)R_J(N)+o_{F,\lambda,J}(M_N).               \tag{1}
\]
The derivative is the right derivative. Formula (1) is an
endpoint calibration, not an extrapolation of the constant
principal beyond its valid Mertens range.

For each fixed sufficiently small \(\beta>0\) define the actual
**nonnegative** statistic
\[
 P_{\lambda,\beta}
 =\beta
 \sum_{\substack{x+mr=N,\ x,r\ {\rm prime},\ x\in NJ\\ r>U,\ m>1}}
   (\log x)(\log r)
       (y/N)^{1/(\beta L)}
                  \prod_{p\mid m}(1-p^{-1/(\beta L)}).
                                                                    \tag{2}
\]
All prime powers in \(m\) are allowed; the product is over
distinct primes. Then
\[
 P_{\lambda,\beta}
 = (1-\lambda+\beta)M_N-\beta R_J(N)
       +O_{\lambda,J}\!\left(e^{-b/(3\beta)}M_N\right)
       +o_{\lambda,\beta,J}(M_N).                                  \tag{3}
\]
The fixed \(\beta\) limit in \(N\) precedes \(\beta\downarrow0\);
no growing inverse smoothing parameter is used.
In particular the normalized double-limit value is \(1-\lambda\),
using only \(R_J(N)\ll_J M_N\).
For two fixed \(0<\lambda_1<\lambda_2<1/2\), use the same \(C_D\)
in \(U_i=N^{\lambda_i}L^{-C_D}\). The difference
\(P_{\lambda_1,\beta}-P_{\lambda_2,\beta}\) is the **positive true
subsum** on \(U_1<r\le U_2\). Its normalized value is
\(\lambda_2-\lambda_1+O(e^{-(1/2-\lambda_2)/(3\beta)})+o_\beta(1)\),
since the same binary term cancels. This prices true
positive marked bands strictly below the root for the new
weight. It does not bound the unpriced super-root part to
the accuracy of the binary term in (3).

## 1. Exact finite principal before letting the cutoff reach zero

Here \(0\le\tau\le b\), \(B_\tau=N^{1-\tau}\) and
\(T_\tau(y)=y/B_\tau\). Retain the actual strict complements,
and fix the same \(U=N^\lambda L^{-C_D}\) for every \(\tau\).
Use the divisor identity and true prime BV argument of
[the original giant reduction, §§1--3](../giant_prime_divisor_remainder/Proof.md),
but keep its finite upper model. Write
\[
 Q_{\tau,y}(m)=\sum_{\substack{d\mid m\\d<T_\tau(y)}}\mu(d).
\]
After the ordinary \(p\mid N\) and proper-power exceptions,
the same uniform identities give
\[
 R_J(N)=A_\tau-{\cal C}_\tau+G_\tau+O_D(NL^{-D}),                   \tag{4}
\]
where \({\cal C}_\tau\) is the genuine \(m>1,r>U\) score with
\(Q_{\tau,y}\), \(G_\tau\) is the actual binary count on
\(y\le B_\tau\), and
\[
 A_\tau=\int_{NJ}\sum_{\substack{n<T_\tau(y)\\(n,N)=1}}
    \frac{\mu(n)}{\varphi(n)}
     \left(\log(y/n)
       -\sum_{\substack{d\le U\\(d,N)=1}}
                \Lambda(d)\frac{\varphi(n)}{\varphi(dn)}\right)\,dx,
 \qquad y=N-x.                                                     \tag{5}
\]
In (5), \(x\) is the real integration variable. To see the
exact signs, subtract from the full \(\log\)-divisor convolution
the short-mark convolution using
\(\sum_{d\mid j,d\le U}\Lambda(d)\) at the divisor \(j\).
The complete latter convolution is zero on the actual \(y>U\).
For the upper divisor \(j>B_\tau\) its true complementary
modulus is \(n=y/j\); opening a short mark gives the actual
product modulus \(dn\). This yields (5) with the minus sign
and true totient, by actual prime BV on \(x\) at scale \(N\).
Here \(n\le N^b\) and \(dn\le N^{\lambda+b}L^{-C_D}
=\sqrt N/L^{C_D}\); the weighted maximal-prefix argument
loses only fixed divisor/log powers, as in the original proof.
No large-\(T_\tau\) limit is used in (5).
The errors from genuine proper-power \(x,y\) and proper-power
marks \(>U\) are power-small uniformly, the last by the
bound \(N^{1+o(1)}U^{-1/2}\).

In the lower divisor sum \(j\le B_\tau\), each remaining
actual prime mark \(r>U\) has \(j=rt\), \(m=y/r\). If \(m>1\)
its coefficient is \(-Q_{\tau,y}(m)\) by complementary
divisors. The prime gate \(r\le B_\tau\) can be dropped
for \(m>1\) because \(Q_{\tau,y}(m)=0\) when \(T_\tau(y)>m\).
If \(m=1\), however, its single lower-divisor mark contributes
the **positive** actual binary term when \(y=r\le B_\tau\);
this is exactly \(G_\tau\), not part of \({\cal C}_\tau\).
As \(y\gg_J N\), this term is supported in
\(\tau\le O_J(1/L)\).
The genuine two-affine positive sieve at \(m=1\), as in §2 of
the polynomial reduction (or the same Selberg proof directly),
gives \(R_J(N)\ll_J M_N\). Thus for each fixed smooth \(w\),
\(\int_0^b w(\tau)G_\tau\,d\tau=O_{J,w}(M_N/L)\).

## 2. The missing derivative atom

Take \(w(\tau)=-F'(\tau)\), so \(\int_0^b w=F(0)\).
Integrating \({\cal C}_\tau\) against \(w\) gives exactly
\({\cal C}_{\lambda,F}\), since \(d<T_\tau(y)\) is equivalent
to \(\tau>\log(dN/y)/L\). This last value is always positive.
Set \(H=(\log L)^4\), \(\tau_0=H/L\) and \(S=e^H\).
For \(\tau_0\le\tau\le b\), the uniform masked Möbius
harmonics of the original reduction give
\(A_\tau=M_N+O_D(NL^{-D})\): the zeroth \(n\)-sum kills
\(\log y\) and the short terms at each \(d\), and the first
logarithmic moment gives \(\mathfrak S(N)\).

For \(0\le\tau\le\tau_0\), the bracket in (5) is instead
\[
                        (1-\lambda)L+O_J(H)                      \tag{6}
\]
uniformly in the actual \(n\) and \(x\).
Indeed the ratio \(\varphi(n)/\varphi(p^j n)\) is \(p^{-j}\)
when \(p\mid n\), and \(p^{-j}/(1-1/p)\) otherwise.
The entire correction to the harmonic with \(1/d\) is
\(O(\sum_p(\log p)/p^2)\), on summing all powers.
Omitting \(p\mid N\) adds at most
\(O(\sum_{p\mid N}\log p/(p-1))=O(\log L)\), by splitting at
\(L^2\) and using \(\sum_{p\mid N}\log p\le L\).
The usual \(\sum_{d\le U}\Lambda(d)/d=\log U+O(1)\) therefore
gives the short-mark bracket \(\log U+O(\log L)\).
Also \(\log n\le H\), \(\log y=L+O_J(1)\), and
\(\log U=\lambda L-C_D\log L\). This proves (6).

For a fixed real central \(y\), integrate the *finite*
short prefix exactly:
\[
\begin{split}
 &\int_0^{\tau_0}
    \sum_{\substack{n<(y/N)N^\tau\\(n,N)=1}}
                       \frac{\mu(n)}{\varphi(n)}\,d\tau\\
 &\quad=
    \left(\tau_0-\frac{\log(N/y)}{L}\right)
        \sum_{\substack{n<(y/N)S\\(n,N)=1}}\frac{\mu(n)}{\varphi(n)}
     -\frac1L\sum_{\substack{n<(y/N)S\\(n,N)=1}}
                         \frac{\mu(n)\log n}{\varphi(n)}
   =\frac{\mathfrak S(N)}{L}+O_D(L^{-D}).
\end{split}                                                        \tag{7}
\]
The shifted threshold remains real, and
\((y/N)S\asymp_J S\) supplies the arbitrary-log Mertens tails
for both harmonics. Each fixed \(n\) begins contributing
exactly at \((\log n+\log(N/y))/L\), so the equality is not
an approximation at the small endpoint. On the small range
\(\sum_{n<T_\tau(y)}|\mu(n)|/\varphi(n)=O(H+1)\).
Using this bound, replacing the bracket by (6)'s leading
term and \(w(\tau)\) by \(w(0)\) costs at most
\(O_{F,J}(N(1+H)^3/L)=o(M_N)\) after integration.
The leading small-\(\tau\) contribution is consequently
\((1-\lambda)w(0)M_N\). The other \(\tau\)'s contribute
\(F(0)M_N+o(M_N)\). Inserting these and the true \(G_\tau\)
estimate into (4) gives (1), since \(w(0)=-F'(0)\).
This extra atom can be nonzero despite a smooth averaging
density, precisely because that density does not vanish
at the zero cutoff.

## 3. Complete the exponential without hiding a longer divisor sum

Fix a smooth \(\chi\) on \([0,\infty)\), equal to 1 on
\([0,b/2]\) and zero on \([b,\infty)\).
Use \(F_\beta(t)=\chi(t)e^{-t/\beta}\) in (1).
It has \(F_\beta(0)=1\) and \(F_\beta'(0)=-1/\beta\).

For each actual divisor \(d\mid m\) the argument
\(t=\log(dN/y)/L\) is at most
\(\log(N/r)/L\le1-\lambda+C_D\log L/L\).
Choose a fixed smooth compact cutoff identically 1 up to
\(1-\lambda+1/2\) on the actual nonnegative arguments
and equal to zero beyond \(1-\lambda+1\).
Thus the tail \((1-\chi(t))e^{-t/\beta}\) on the actual arguments
has a smooth compact extension, zero near \(t=0\), whose
\(j\)-th derivative has \(L^1\)-norm
\(O_{j,b}((1+\beta^{-j})e^{-b/(2\beta)})\).
For the full actual quotient range \(m\le N^{1-\lambda}L^{C_D}\),
the positive prime-row Fourier--Euler estimate of
[the polynomial reduction, §§2--3](PolynomialSmoothedGiantReduction.md)
applies to this compact tail. In fact its elementary Fourier
bound (7) in the earlier smoothed proof only uses the compact
extension and an integrable Fourier majorant, not that the
tail itself represents an original cutoff.
Integrating by parts a fixed number of times larger than its
Euler polynomial degree bounds the **actual absolute** tail
score by \(O_{\lambda,J}(e^{-b/(3\beta)}M_N)\).
This includes all prime powers in \(m\) and the true local
factor \(c(m)\) in the positive bound; it is not a main-term
calculation for long moduli.

Without the cutoff the Möbius divisor sum for the exponential
factors exactly as
\[
   \sum_{d\mid m}\mu(d)e^{-\log(dN/y)/(\beta L)}
       =(y/N)^{1/(\beta L)}\prod_{p\mid m}(1-p^{-1/(\beta L)}).
\]
Combine this with (1) and the paid tail to obtain (3).

The zero-cutoff term is related to the finite-prefix boundary
in logarithmic integrations of the original marked identity,
but (1) allows an independent fixed polynomial mark threshold
and any smooth zero-endpoint derivative. The nonnegative
all-even moment (2) is evaluated for the actual two genuine
prime labels, not an integer parity model. The error in
(3) still leaves the binary term undetermined. An upper
strictly below \((1-\lambda+\beta)M_N\) by more than its
exponentially small tail and eventual \(o_\beta(M_N)\) would
imply binary positivity; no such upper is asserted.
