# Absolute finite angular ranks for the genuine two-leg giant correlation

Use the exact notation of
[JointSharpGiantCorrelation.md](JointSharpGiantCorrelation.md):
\(N\) is any sufficiently large even integer,
\(x+y=N\), \(x\in NJ\Subset(0,N)\) is central, \(L=\log N\),
\(\ell=\log L\), \(M=|J|N\mathfrak S(N)\), and
\(R=R_J(N)\) is the genuine weighted binary count.
Here restrict the fixed profile endpoint to
\[
       0<a<b\le .002,\qquad
       \lambda=\tfrac12-b,\qquad U=N^\lambda e^{-\ell^3}.
\]
Let \(F,G\) be fixed real smooth profiles, constant on \([0,a]\)
and zero on \([b,\infty)\). The actual composite-leg score is
\[
 P_F(x)=\sum_{\substack{r\mid x,\ r\ {\rm prime}\\U<r<x}}
                 \log r\sum_{d\mid x/r}\mu(d)
                           F\!\left(\frac{\log(dN/x)}L\right),
\]
and analogously for \(P_G(y)\). All statements retain the genuine
target-unit mask \((x,N)=1\), equivalent to \((y,N)=1\);
there is no radical restriction.

For positive angles \(u_1,\ldots,u_k\) of total one put
\[
 \mathcal K_{\lambda,F}(u)=
    \sum_{i:\,u_i>\lambda} u_i
       \sum_{I\subseteq[k]\setminus\{i\}}(-1)^{|I|}
                             F\!\left(\sum_{j\in I}u_j\right).
\]
If a squarefree integer \(n\) has prime factors \(p_i\), its angles
are \(u_i(n)=\log p_i/\log n\).

**Theorem.** For every fixed \(\varepsilon>0\) there are fixed
\(0<\eta<\lambda\) and \(K\ge2\) such that the actual sum
\[
 \sum_{\substack{x+y=N,\ x\in NJ,\ (x,N)=1\\
                 x,y\ {\rm squarefree}\\
                 2\le\omega(x),\,\omega(y)\le K+1\\
                 P^-(x),\,P^-(y)>N^\eta}}
  (\log x)(\log y)
          \mathcal K_{\lambda,F}(u(x))
          \mathcal K_{\lambda,G}(u(y))                           \tag{1}
\]
equals \(F(0)G(0)(R-M)+O(\varepsilon M)+o_{\eta,K,F,G,J}(M)\).
The tolerance can be prescribed for each fixed pair of profiles;
it is not a growing-rank assertion. Both arguments in (1) are
genuine composite integers at the **same** target. A prime
mark in either kernel is an actual factor of that integer.
The result supplies no lower bound for the actual signed
joint angular sum.

The key new point is an aggregate genuine two-prime upper
with independent quotient weights, even in the part where
the elementary fixed-quotient line length is short.

## 1. A two-quotient positive upper

Take nonnegative \(w(m),v(n)\) supported on
\(2\le m,n\le N/U\) and bounded by fixed multiples of the
same fixed power of \(\tau\). Then
\[
 \begin{split}
 &\sum_{\substack{m r+n s=N,\ mr\in NJ\\
                  r,s\ {\rm prime},\ r,s>U\\
                  (mr,N)=1}}
           w(m)v(n)(\log r)(\log s)\\
 &\hspace{12mm}\ll
       M\left(\sum_m\frac{c(m)w(m)}m\right)
        \left(\sum_n\frac{c(n)v(n)}n\right)+O(N^{.993}),
                                                               \tag{2}
 \end{split}
\]
where \(c(d)=\prod_{p\mid d,\ p>2}(p-1)/(p-2)\).
The implied constants can depend on the fixed divisor bound,
\(J\) and \(b\), uniformly in the two weights. The numerical
power in the harmless error is not optimal.

Indeed \((mn,N)=1\) and \((m,n)=1\) on an actual row.
If \(mn\le N^{.995}\), fix \(m,n\). The solutions of
\(m r+n s=N\) are \(r=r_0+n k,\ s=s_0-m k\);
the real \(k\)-interval has length \(|J|N/(mn)\).
At every prime dividing \(Nmn\) the product of the forms
has one root, and at every other prime it has two.
For example when \(p\mid m\) the \(s\) form is a constant
nonzero modulo \(p\), by the target-unit hypothesis,
and the \(r\) form has one root. When \(p\mid N\)
the roots coincide, and this includes \(p=2\).
The usual two-dimensional upper sieve, at the polynomial
length \(X=N/(mn)\ge N^{.005}\) and with fixed power reserve,
gives count \(O_J(X\mathfrak S(N)c(mn)/L^2)\).
One may take Selberg support \(X^{1/3}\) and sieve primes
\(\le X^{1/12}\), as in
[the polynomial smooth reduction, §2](PolynomialSmoothedGiantReduction.md);
the two logs now cost at most \(L^2\).
Sum over the allowed \(m,n\), using
\(c(mn)=c(m)c(n)\) there. Dropping their masks in the
resulting **positive upper** gives the asserted part of (2).

For the remaining pairs each coefficient lies in
\([N^{.493-o(1)},N^{.502+o(1)}]\) because \(m,n\le N/U\)
and \(mn>N^{.995}\). Enlarge to this independent rectangle
before splitting into dyads. Retain the outer restrictions
\((mn,N)=1\) and \((m,n)=1\). Choose a fixed nonnegative
smooth \(\Psi\) of compact support in \((0,1)\) with
\(\Psi\ge1_J\). Both genuine primes \(r,s>U\) exceed the
sieving cutoff \(z=N^{.000001}\) by a fixed power. Apply a
nonnegative upper Rosser--Iwaniec beta sieve to \(rs\),
with coefficients \(\lambda_d^+\), support \(d\le N^{.0001}\),
and its underlying prime alphabet \(p\le z\). The universal
coefficients are independent of \(m,n\), have
\(|\lambda_d^+|\le1\), and can use the usual dimension-two
upper fundamental-lemma bound at this fixed large
ratio of logarithmic levels; see [Kurlberg--Lester--Rosenzweig, §2.1](https://kurlberg.github.io/eprints/2dscar.pdf).
We replace the two prime
logs by \(L^2\) only after applying this simultaneously
to the **two genuine prime conditions**.

For each squarefree \(d\) expand the condition \(d\mid r s\)
prime by prime. Use \(d_r\mid r,\ d_s\mid s\), with
\([d_r,d_s]=d\), and coefficient
\((-1)^{\omega((d_r,d_s))}\). This is exact inclusion--exclusion,
including when both forms vanish at a prime. Put
\(j=(d_r,d_s)\). At the retained outer masks a nonempty
physical class requires
\[
       j\mid N,\qquad (m,d_s)=(n,d_r)=1 .
\]
Indeed \(m,n\) are target units and coprime. In addition
these restrictions ensure the effective coefficients
\[
           A=m d_r/j,\qquad B=n d_s/j,\qquad X=N/j
\]
are coprime. Write \(r=d_r R_1,\ s=d_s R_2\);
the literal equation is \(A R_1+B R_2=X\).
With the positive smooth central test, \(R_2\) is
automatically positive whenever the integer progression
for \(R_1\) is satisfied. Dropping the lower mark gates
and the additional \(r,s\)-unit tests on this positive
sieve upper only enlarges it. We never drop the
outer \((mn,N)=1\) or cross compatibility in the
reciprocal estimate.

Poisson on \(R_1\equiv X\bar A\bmod B\) gives terms
\[
 \frac{X}{AB}\widehat\Psi\!\left(\frac{\nu X}{AB}\right)
                 e_B(\nu X\bar A),\qquad \nu\in\mathbb Z.
                                                               \tag{3}
\]
Fix \(d_r,d_s,j\) and the dyads of \(m,n\).
Let \(g_0=\log_X(M_A M_B)\) and
\(m_0=\log_X\max(M_A,M_B)\), with \(M_A,M_B\)
the actual dyadic scales of \(A,B\).
Here \(j\le N^{.0001}\), even at arbitrary radical
of \(N\). Each effective-scale exponent relative to
\(X\) is in \([.492,.504]\) for large \(N\).
For example the upper exponent is at most
\((.502+.0001+o(1))/(1-.0001)<.504\).
The coprime reciprocal sum in (3) is one to which
[Bettin--Chandee, Theorem 1](https://arxiv.org/pdf/1502.00769)
applies. The same Poisson/Mellin calculation as in
[the giant reciprocal seam, §3](../reverse_giant_typeI/GiantReciprocalSeam.md)
has the following exact budgets: cut
\(|\nu|\ll X^\rho(1+M_A M_B/X)\) for arbitrarily small
fixed \(\rho>0\) by rapid Fourier decay. On a signed
frequency dyad of scale \(T\), Mellin-separate
\(\widehat\Psi(\nu X/(AB))\) on its normalized
compact product range. Its Mellin mass is bounded
uniformly using the rapid decay of \(\widehat\Psi\)
and its derivatives. The arbitrary supported
coefficient norms cost
\((T M_A M_B)^{1/2}L^{O(1)}\):
for example \(A\) uniquely determines the actual \(m\)
at fixed \(d_r,j\), and ordinary divisor moments bound
its squared weight. The separated compatibility masks
\((m,d_s),(n,d_r),(mn,N)\) restrict each coefficient;
the remaining genuine \((A,B)=1\) is the coprime
condition of the trilinear estimate itself.
The phase factor is at most
\(X^{(\max(0,1-g_0)+\rho)/2+o(1)}\).

In particular the two exponents relative to the target
scale \(X\) after restoring \(X/(AB)\) in (3) are, before
arbitrarily small fixed losses,
\[
 \begin{array}{ll}
 .7g_0+.25m_0-.85,\quad .875g_0+.125m_0-1, &g_0\ge1,\\
 .5-.65g_0+.25m_0,\quad .5-.625g_0+.125m_0, &g_0<1.
 \end{array}
\]
Here \(.984\le g_0\le1.008\) and \(m_0\le.504\),
so these are bounded above by
\(-.0184,-.055,-.0136,-.052\), respectively.
Taking \(\rho\) and the analytic epsilon small gives
\(O(X^{1-.010})\) for each fixed sieve label pair
and dyad (absorbing fixed log powers).
There are at most \(N^{.0002}\) pairs
\((d_r,d_s)\), since each is at most \(N^{.0001}\).
Thus even their **absolute count**, log dyads and
the two prime logs leave the error stated in (2).
No spectral estimate with \(m,n\) treated as primes
or with a moving unit residue independent of the physical
equation was used.

For the zero mode in (3) reassemble the sieve at
the fixed physical \(m,n\). The split term has density
\(j/(m n d_r d_s)\) in \(x\). At any \(p\mid N\), both
forms have the same root, and the two single-root terms
minus their shared term give exactly \(1/p\) relative to
\(1/(m n)\). At \(p\mid m\) or \(p\mid n\), only one
root is possible, because the form with zero slope
takes a nonzero residue by the target-unit condition.
At any \(p\nmid Nmn\), there are two distinct roots.
The resulting combined local sieve density is therefore
that of the actual two affine forms:
\[
 \frac{N}{m n}\left(\int\Psi\right)
       \sum_d\lambda_d^+\prod_{p\mid d}\frac{\rho(p)}p,
       \quad
 \rho(p)=
  \begin{cases}1&p\mid Nmn,\\2&p\nmid Nmn.\end{cases}
\]
This expression is nonnegative, as the mean of the
nonnegative sieve majorant in the local model.
The dimension-two upper fundamental lemma gives
\(\ll_J N/(mn)\prod_{p\le z}(1-\rho(p)/p)\).
By Mertens and the binary Euler factors the product is
\(\ll L^{-2}\mathfrak S(N)c(m n)\); the factors at primes
dividing \(Nmn\) only cause the displayed correction,
uniformly in the target. This pays **both** prime logs
even in the short central fibre, without using a
pointwise two-prime estimate for that fibre.
Keep the actual compatible outer rows in this zero
mode, then enlarge its positive upper. This proves (2).

## 2. Independent positive quotient envelopes and actual tails

Extend \(F,G\) smoothly with compact support to negative
arguments (their values there are never used).
By Fourier inversion their divisor scores on any real
central argument are bounded absolutely by
\[
 V_F(m)=\int_{\mathbb R}|\widehat F(\xi)|
                 \prod_{p\mid m}|1-e^{i\xi\log p/L}|\,d\xi,
                                                               \tag{4}
\]
and similarly for \(G\), using the convention
\(\widehat F(\xi)=(2\pi)^{-1}\int F(t)e^{-i\xi t}\,dt\).
The common spatial phase has modulus one.
The product uses **distinct prime factors** even at a
prime power. The weight in (4) is nonnegative and
\(O_F(\tau(m))\), so can be used in (2).

For completeness its true positive harmonic estimates
on \(m\le N/U\le N^{.503}\) are
\[
 \begin{array}{ll}
 \displaystyle\sum_m\frac{c(m)V_F(m)}m=O_F(1),&
 \displaystyle\sum_{P^-(m)\le N^\eta}
                     \frac{c(m)V_F(m)}m=O_F(\eta),\\[4pt]
 \displaystyle\sum_{m\ {\rm not\ squarefree}}
                     \frac{c(m)V_F(m)}m=O_F(L^{-1}),&
 \displaystyle\sum_{\omega(m)>K}
                     \frac{c(m)V_F(m)}m=O_{F,t}(t^{-K})
                     \quad(t>1\ {\rm fixed}).
 \end{array}                                                     \tag{5}
\]
These are ordinary integer harmonics used only to
upper-bound the original scores. At fixed \(\xi\) extend
the allowed integers to their positive Euler product
over \(p\le N^{.503}\). Its logarithm is
\(O(\sum_{p\le N^{.503}}\min(2,|\xi|\log p/L)/p)\),
up to an absolute bounded correction. Split at
\(e^{L/(1+|\xi|)}\), use the ordinary reciprocal-prime
bound and the Chebyshev logarithmic prime harmonic,
and get \(O(1+\log(1+|\xi|))\). Thus the product is bounded
by a fixed power of \(1+|\xi|\).
To force a prime \(p\le N^\eta\) use a union over its
factor, paying in addition \(O(|\xi|\eta)\).
To force a repeated prime use the same estimate with
local exponents at least two, paying
\(O(|\xi|L^{-1}\sum_p\log p/p^2)\).
A factor \(t^{\omega(m)}\) merely changes the power
of \(1+|\xi|\), for fixed \(t\).
Rapid Fourier decay gives all of (5).

Now apply (2) independently on the two arms, with
\(w=V_F,v=V_G\), keeping the required positive mask
in the indicated arm for each discarded class. By
(5), true terms where either quotient has a tiny
prime, a repeated prime, or more than \(K\) distinct
factors have total absolute weight
\[
             O_{F,G,J}(\eta M)+O_{F,G,J,t}(t^{-K}M)+o(M).
\]
If a marked prime \(r>U\) divides its own quotient
\(m\), the actual \(r^2\) divides \(x\); sum actual
multiples over \(r>U\). Both product scores have
fixed divisor-power envelopes, so these exceptions
cost \(N^{1-\lambda+o(1)}\), and the same holds for
\(s\) on the other arm. The marked primes themselves
are not tiny if \(\eta<\lambda\) is fixed.
Consequently we have dropped all unwanted squares,
tiny factors and large ranks in the complete factors
of both \(x\) and \(y\), with arbitrarily small chosen
absolute error on the \(M\) scale. This uses positivity
only to control that error, not to assert the sign
of the main score.

On the retained finite ranks and floor, replace
the physical \(r>U\) by
\(\log r/\log x>\lambda\), and similarly for \(s\).
The new gate is a subset of \(r>U\) for large \(N\)
because \(x\asymp_J N\) and \(e^{-\ell^3}\to0\).
A moved \(r\) lies in
\(r=N^\lambda e^{O_J(\ell^3)}\), so its literal
quotient lies in
\(m=N^{1-\lambda}e^{O_J(\ell^3)}\).
Mark a genuine prime factor of \(m>1\) at fixed
other factors. Its reciprocal mass in this
\(e^{O(\ell^3)}\)-ratio interval, starting above
\(N^\eta\), is \(O_\eta((1+\ell^3)/L)=o_\eta(1)\)
by fixed-ratio Chebyshev dyads. All other prime
harmonics on the finite ranks cost bounded factors
depending on \(\eta,K\). Thus (2), with the
actual quotient collar in the first weight, pays
the whole change by \(o_{\eta,K}(M)\) jointly.
The same reasoning applies in the other arm.

Finally \(F(\log(dN/x)/L)\) can be replaced by
\(F(\log d/\log x)\) at \(O_{F,J}(1/L)\) per
actual divisor uniformly, since \(x\asymp_J N\);
there are only finitely many retained subset
positions. The same for \(G\).
The total weight of the finite-rank retained
true rows is \(O_{\eta,K}(M)\) by (2) and their
finite positive prime harmonics, so this last
error is \(o_{\eta,K}(M)\).
Using \(\log r=u_r(x)\log x\) exactly now gives
the sum (1). The signed identity of
JointSharpGiantCorrelation finishes the proof.
