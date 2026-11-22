# An asymmetric over-root correlation of two arbitrary divisor labels

Let \(N\) be even, \(L=\log N\), \(D\asymp N^\alpha\) and
\(Q\asymp N^\beta\), with fixed \(0<\alpha,\beta<1\). Let \(a_A,b_r\)
be arbitrary complex coefficients on \(D<A\le2D\), \(Q<r\le2Q\),
bounded by fixed divisor powers times fixed powers of \(L\).
Neither label is required to be prime or to have a particular
factorization, and separate support masks on them are permitted.
Let \(\Psi=\Psi_N\) be supported in a fixed compact subinterval of
\((0,1)\), with each fixed smooth derivative bounded by a fixed
power of \(L\).

**Proposition.** If
\[
                     E=\max\{\beta+\alpha/2,\ \beta/2+3\alpha/2\}<1,
                                                                    \tag{1}
\]
then for some fixed \(\delta>0\) the true fixed-target sum satisfies
\[
 \sum_{\substack{x+y=N\\ (x,N)=1}}\Psi(x/N)
          \sum_{A\mid x}a_A\sum_{r\mid y}b_r
 =
 \varphi(N)\int_{\mathbb R}\Psi(v)\,dv
     \sum_{\substack{(Ar,N)=1\\ (A,r)=1}}\frac{a_A b_r}{Ar}
 +O(N^{1-\delta}).                                                  \tag{2}
\]
This includes \((\alpha,\beta)=(.399,.795)\), at which
\(E=.996\) and the literal products have size \(N^{1.194+o(1)}\).
One can exchange the arms using the reflected \(\Psi(1-v)\).
The argument does not give saving at \((1/2,1/2)\) or in the entire
over-root triangle. The unit condition and the coprimality on the
right of (2) are exactly those from the physical pairing.

## Proof

First restrict the label sum to \((Ar,N)=(A,r)=1\), a necessary
condition on every physical row. Then open \((x,N)=1\) by
\(\sum_{u\mid(x,N)}\mu(u)\). Terms with \(u>N^{\epsilon_0}\), for
a small fixed \(\epsilon_0>0\), have total absolute weight
\(O(N^{1-\epsilon_0+o(1)})\). Indeed, each row has at most a fixed
divisor power in its two weights together, there are
\(O(N/u+1)\) literal multiples, and \(\tau(N)=N^{o(1)}\).
The truncated zero-mode main term also differs from the full one
by \(O(N^{1-\epsilon_0+o(1)})\), by the \(1/u\) harmonic
and the two divisor-bounded label harmonics.

At fixed \(u\mid N\), write \(X=N/u\).
Because \((u,Ar)=1\), the physical row is \(x=uA m\), with
\(m\equiv X\overline A\bmod r\). Its weight \(\Psi(x/N)\) is
\(\Psi(A m/X)\). With \(e(z)=\exp(2\pi i z)\), Poisson summation
on this residue class gives
\[
 \sum_{\nu\in\mathbb Z}\frac{X}{Ar}\,
       \widehat\Psi\left(\frac{\nu X}{Ar}\right)e_r(\nu X\overline A).
                                                                    \tag{3}
\]
The zero mode sums to the stated main once one restores
\(\sum_{u\mid N}\mu(u)/u=\varphi(N)/N\).
For \(\nu\ne0\), reciprocity on compatible rows gives
\[
            e_r(\nu X\overline A)
               =e_A(-\nu X\overline r)e(\nu X/(Ar)).                  \tag{4}
\]
Fix \(\nu\), put \(V=X/(DQ)\), and separate the smooth factor in (3)
and the last factor in (4) from the reciprocal phase.
On \(1\le s,t\le2\) the resulting kernel is
\[
 K_\nu(s,t)=\frac{V}{st}\,
           \widehat\Psi\left(\frac{\nu V}{st}\right)
           e\left(\frac{\nu V}{st}\right).
\]
The kernel, its two first partial derivatives, and its mixed
derivative are all \(O(L^C V(1+|\nu|V)^{-2})\), using any fixed
additional Fourier decay needed for the differentiations.
Integrating first in \(s\) and then in \(t\) from the upper ends
of their intervals expresses its contribution by a sum of bounded
endpoint integrals of the **same** reciprocal sum with independent
prefixes \(A\le sD,\ r\le tQ\). In particular the total cost of
this step is \(O(L^C V(1+|\nu|V)^{-2})\) times a bound uniform in
those prefixes. This separation is made before any additive
frequency grouping. The sum of \(V(1+|\nu|V)^{-2}\) over
nonzero \(\nu\) is \(O(1)\), uniformly for \(V>0\).
The frequencies \(|\nu|>N^2\) in (3) can be discarded at an
arbitrary power of \(N^{-1}\) using the absolute label bound
and additional Fourier decay, since \(V\gg N^{-1-\epsilon_0}\).

Thus fix \(0<|\nu|\le N^2\), put \(C=-\nu X\), and use the original
independent coefficients with any desired prefix masks. On the
unit group modulo \(A\) the phase is \(e_A(C\overline r)\); extend
it by **zero** on the nonunits so the gcd restriction is retained.
The complete additive expansion is
\[
  1_{(r,A)=1}e_A(C\overline r)
       =\sum_{0\le j<A}c_A(j)e(jr/A),\qquad
  c_A(j)=\frac1A\sum_{v\bmod A}^{*}e_A(C\overline v-jv).
                                                                    \tag{5}
\]
The [Weil--Estermann Kloosterman bound](https://doi.org/10.1112/S0025579300002187)
gives \(|c_A(j)|\le\tau(A) A^{-1/2}(C,j,A)^{1/2}\),
including \(j=0\). As \((X,A)=1\), a reduced frequency \(j/A=h/k\)
has \(A=k\ell,\ (j,A)=\ell\) and \((C,j,A)=(\nu,\ell)\).
This includes the frequency zero with \(h=0,k=1\).
The coefficient \(B(h/k)\) obtained by summing \(a_A c_A(j)\)
over all contributing \(A\) has the uniform bound
\[
 |B(h/k)|
   \ll D^{-1/2}N^{o(1)}\sum_{D/k<\ell\le2D/k}\sqrt{(\nu,\ell)}
   \ll N^{o(1)}\frac{\sqrt D}{k}.                                   \tag{6}
\]
In fact the inner sum is at most
\[
    \sum_{g\mid\nu}\sqrt g\,\#\{\ell\le2D/k:g\mid\ell\}
       \le (2D/k)\sum_{g\mid\nu}g^{-1/2}.
\]
All labels \(A,r\) not coprime to \(N\) remain masked in their own
coefficients. The estimate is uniform for subsets of the labels and
does not approximate nonprimitive frequencies by independent ones.

Distinct reduced frequencies have spacing at least \(1/(4D^2)\)
modulo one. By the additive [large sieve of Montgomery and Vaughan](https://doi.org/10.1112/S0025579300004708),
Cauchy, (6), and \(\sum |b_r|^2\ll QN^{o(1)}\), the independently
prefixed reciprocal sum is
\[
 \left|\sum_{k\le2D}\sum_{h\bmod k}^{*}
                 B(h/k)\sum_r b_r e(hr/k)\right|
       \ll N^{o(1)}\sqrt{D Q(Q+D^2)}.                               \tag{7}
\]
Here \(\sum_{h/k}|B(h/k)|^2\ll DN^{o(1)}\),
since \(\sum_{k\le2D}\varphi(k)/k^2\ll\log(2D)\).
The \(k=1\) coefficient is included once. No division by a prime
label, character primitivity condition, or removal of a physical
diagonal is used. Formula (5) enforces all label diagonals exactly.

Finally sum the separated kernel costs over the Poisson frequencies
and the \(N^{o(1)}\) divisors \(u\mid N\).
The exponent of (7) is precisely (1). This proves (2), including
the restored tails, with a fixed power margin.

## Scope in the actual complex-order hyperbola

The identity \(\tau_{1+w}=1*\tau_w\) makes (2) apply to the
**entire** indicated divisor dyad of
\(\sum_{x+y=N,(x,N)=1}\Psi(x/N)\tau_{1+w}(x)\tau_{1+w}(y)\),
uniformly on a fixed compact set of complex \(w\).
One may use two independently varying orders. The sector is no
longer restricted to a genuine prime times a short factor as in the
[prime-factor slab](PrimeFactorSlab.md); signed \(\mu\) coefficients
or other truly composite divisor weights are also permitted.
This uses only classical complete Kloosterman and large-sieve bounds,
not an optimal theorem for bilinear Kloosterman fractions.
For comparison the balanced reciprocal methods in
[the actual two-mark block](../nearfull_high_vaughan/JointGiantActualMarkBlock.md)
use a different bound. Formula (2) does **not** handle the terminal
actual divisor pair \(A=x,r=y\), which contains the binary prime
atom in the small-order expansion, or evaluate any growing sum of
uncovered slabs without a fresh margin. It gives no lower bound for
that atom or for any whole compensated Goldbach score.
