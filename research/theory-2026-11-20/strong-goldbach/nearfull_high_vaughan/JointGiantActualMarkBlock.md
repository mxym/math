# Signed cancellation when both actual giant marks stay near the root

Let \(N\) be any sufficiently large even target, \(J\Subset(0,1)\)
a fixed nondegenerate central interval, \(x\in NJ\), \(y=N-x\),
\(L=\log N\), and \(M_N=|J|N\mathfrak S(N)\).
For fixed smooth real profiles \(F,G\) on \([0,\infty)\)
supported on \([0,b_F]\) and \([0,b_G]\), respectively, use
the true marked composite weight from
[the two-leg giant correlation](JointSharpGiantCorrelation.md).
In this note restrict its prime mark in the \(F\)-leg to an
independent real interval \(\mathcal R=(R_-,R_+]\), and in
the \(G\)-leg to \(\mathcal Q=(Q_-,Q_+]\), where
\(R_-,Q_-\ge N^\xi\) for any fixed \(\xi>0\).
Thus
\[
 P_{F,\mathcal R}(x)
   =\sum_{\substack{r\mid x,\ r\in\mathcal R\\r\ {\rm prime},\,r<x}}
       (\log r)\sum_{d\mid x/r}\mu(d)
                          F\!\left(\frac{\log(dN/x)}L\right),
\]
and similarly for \(P_{G,\mathcal Q}(y)\).
Any original lower mark gate can first be intersected with
the indicated interval.

The following conclusions apply on either set of strict
power rails:
\[
 \begin{array}{ll}
 \text{(balanced)}& b_F,b_G\le .002,\quad
                      \max(R_+,Q_+)\le N^{.510};\\
 \text{(asymmetric)}& b_F,b_G\le .0005,\quad
          \max(R_+,Q_+)\le N^{.565},\quad R_+Q_+\le N^{1.003}.
 \end{array}
\]
The asymmetric case allows its lower mark exponents to be
smaller than the near-root cutoff of the published balanced
score. It does not enlarge that fixed-cutoff geometry.

**Theorem.** At each individual even \(N\), on either pair
of rails, the genuine signed subsum has the asymptotic
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}}
  P_{F,\mathcal R}(x)P_{G,\mathcal Q}(y)
  = F'(0)G'(0)\,M_N\,
      \frac{\log(R_+/R_-)}L\frac{\log(Q_+/Q_-)}L
          +o_{F,G,J,\xi}(M_N),                                   \tag{1}
\]
uniformly in the intervals. If either profile is constant
on a fixed interval right of zero, the entire left side
is \(O_A(NL^{-A})\) for every fixed \(A\).
This is cancellation on actual matched prime marks, not
a positive envelope or a statement about nonprime surrogates.

In particular, in the flat profile setting \(b\le .002\)
of [the joint finite-rank reduction](JointGiantFiniteRank.md),
the entire matched covariance \(F(0)G(0)(R_J(N)-M_N)\)
up to \(o(M_N)\) is on the union of the **actual mark pairs**
for which at least one of \(r,q\) is \(>N^{.510}\).
That mark is the unique prime divisor of its own integer
above the root, and its cofactor is \(\le N^{.490}\).
This assertion is about the mark-pair sum, not a claim
that every integer in the discarded block has no other
qualifying prime label. No sign of the surviving block
is asserted.

## 1. Exact unit opening and real Poisson

Here \(r<x\) and \(q<y\) are automatic uniformly on the
stated rails. On expanding the actual two divisor
weights, the true divisors of \(x,y\) are
\[
                  A=rd,\qquad B=qe,\qquad
                    d\le N^{b_F},\quad e\le N^{b_G}.
\]
Retain \((AB,N)=1\); on target units this is forced,
and compatibility in the two actual progressions
forces \((A,B)=1\). In particular the genuine primes
\(r,q\) are different. It is not necessary to assume
that a mark is coprime to its *own* short divisor.

Smooth the real \(x/N\) test of \(J\) in a collar of
width \(L^{-D_0}\), with \(D_0\) sufficiently large.
The absolute actual coefficient is
\(L^{O(1)}\tau(x)^{O(1)}\tau(y)^{O(1)}\).
Cauchy and the fixed divisor moments count the
global \(O(NL^{-D_0}+1)\) collar with arbitrary-log
accuracy; this does not need any actual prime
distribution. At fixed \(d,e\) the resulting normalized
test is
\[
 \Psi_{d,e}(v)=\psi_J(v)
  F\!\left(\frac{\log(d/v)}L\right)
  G\!\left(\frac{\log(e/(1-v))}L\right).
\]
It is supported in a fixed compact interior interval,
and every fixed derivative norm is log-power bounded
uniformly in \(d,e\).

Keep actual target units by opening \((x,N)=1\) as
\(\sum_{u\mid (x,N)}\mu(u)\), while retaining \(A,B\)
target units. All \(u>N^{.0001}\) are negligible:
there are at most \(N/u\) actual central \(x\)'s
divisible by \(u\), every expansion on that row is
bounded by a fixed divisor power times \(L^{O(1)}\),
and there are \(\tau(N)=N^{o(1)}\) choices. This is
\(N^{1-.0001+o(1)}\).
For the remaining \(u\), since \(u\mid N\) and
\((AB,u)=1\), both free variables are multiples of
\(u\). Divide them and the target by \(u\) and put
\(X=N/u\). The equation really becomes
\(A R_1+B R_2=X\), with \(x/N=A R_1/X\).
Thus Poisson on \(R_1\equiv X\bar A\bmod B\) gives the
frequency terms
\[
   \frac{X}{AB}\,\widehat\Psi_{d,e}
           \!\left(\frac{\nu X}{AB}\right)
                       e_B(\nu X\bar A),\qquad \nu\in\mathbb Z . \tag{2}
\]
All changes of sign/equality at the real physical
endpoints concern only fixed residue prefixes, and
can equivalently be kept as stated half-open windows.

## 2. Full signed nonzero bound for the real mark windows

Fix \(u,d,e\), and dyadically subdivide the two actual
prime windows \(r,q\); their labels themselves are not
smooth-replaced. Write \(A_0,B_0\) for the scales
\(dR_0,eQ_0\) on a pair of such dyads.
If \(A_0 B_0\le N^{.998}\), use ordinary progression
floors (and the smooth test's total variation)
instead of the nonzero modes. The count of actual
prime choices is at most a constant times
\(R_0 Q_0=A_0B_0/(de)\).
Summing \(1/(de)\), the fixed log powers and dyads,
and all \(u\mid N\), gives \(N^{.998+o(1)}\).
Fixed-factor constants in this split do not affect
any strict exponent.

Otherwise put
\[
       g=\log_X(A_0B_0),\qquad m_0=\log_X\max(A_0,B_0).
\]
For large \(N\), \(g\ge .998-o(1)\), and in the two
cases above we respectively have
\[
         g\le1.0242,\quad m_0\le .5121;
         \qquad
         g\le1.005,\quad m_0\le .566.
\]
For example in the first case
\((1.020+.004)/(1-.0001)<1.0242\);
the upper individual exponent is
\((.510+.002)/(1-.0001)<.5121\).
The analogous bounds use \(1.003+.001\) and
\(.565+.0005\) in the second case.

Apply the coprime reciprocal bound of
[Bettin--Chandee, Theorem 1](https://arxiv.org/pdf/1502.00769)
to the genuine outer variables \(A=dr,B=eq\) and
the signed frequency variable in (2). This has
precisely the real phase and norm setup already
used in [JointGiantFiniteRank, §1](JointGiantFiniteRank.md).
Indeed \(d,e\) are fixed, so each label uniquely
recovers the corresponding actual prime. All unit
masks on \(A,B\) restrict individual coefficients;
their coprimality is the condition of the trilinear
bound itself. The coefficients on literal prime
intervals have square norms bounded by \(A_0^{1/2}\)
and \(B_0^{1/2}\) times fixed log powers.
Cut frequencies at \(X^\rho(1+A_0B_0/X)\) for an
arbitrarily small fixed \(\rho>0\).
Rapid Fourier decay and the above derivative norms
make the discarded part arbitrary-log small,
also after summing the label counts. On a signed
frequency dyad the Fourier profile separates by
Mellin on its compact normalized product range;
its Mellin mass costs fixed log powers, since the
normalized derivatives of its Fourier transform
decay to any fixed order. The phase factor in the
trilinear estimate is at most
\(X^{\max(0,1-g)/2+\rho/2+o(1)}\).

To make the power audit explicit, the two
exponents relative to \(X\) after the prefactor
\(X/(AB)\) in (2), before arbitrarily small losses,
are
\[
 \begin{array}{ll}
 .7g+.25m_0-.85,\quad .875g+.125m_0-1,
                                      &g\ge1,\\
 .5-.65g+.25m_0,\quad .5-.625g+.125m_0,
                                      &g<1.
 \end{array}
\]
On the balanced rails they are all \(<-.005\)
(after an arbitrarily small dyad-scale slack);
the limiting closest one is at most
\(.7(1.0242)+.25(.5121)-.85=-.005035\).
On the asymmetric rails they are all \(\le-.005\),
the nearest being
\(.7(1.005)+.25(.566)-.85=-.005\).
Choose \(\rho\) and the analytic epsilon small
to keep an \(X^{1-.0045}\) bound, absorbing
logarithmic dyads, derivative norms, and smooth
spacing losses. The number of \(d,e\) pairs is
at most \(N^{.004}\) (at most \(N^{.001}\)
in the asymmetric case), and there are \(N^{o(1)}\)
target divisors \(u\). Since \(X\le N\), the summed
nonzero bound is power-small. Prime logs on the
outer factors cost only fixed log powers.
This uses the actual two signed divisor
coefficients, not two independently modeled primes.

## 3. The exact zero mode for the same real prime marks

Reassemble both the CRT and Poisson principal
terms, keeping the complete physical \(r,q\) windows.
Restore the omitted \(u\)'s in the zero mode:
\(\sum_{u\mid N,\ u>N^{.0001}}1/u
 \le N^{-.0001}\tau(N)\), and all remaining
absolute harmonic sums cost fixed log powers.
Thus its unit coefficient is exactly
\(\varphi(N)/N\). At each fixed true target-unit
\(r,q\) with \(r\ne q\), the remaining signed
\(d,e\) harmonic, after the explicit \(1/(rq)\),
has the masks
\((d,Nq)=(e,Nr)=1,\ (d,e)=1\).
These are actual compatibility masks; there is
no average over a moving unrelated residue.

The two-coordinate moments in
[JointGiantEndpointDerivative, §2](JointGiantEndpointDerivative.md)
apply with these fixed outer primes in place of the two
short marks \(k_1,k_2\). For clarity, first truncate \(d\)
and then \(e\) at \(\exp((\log L)^4)\), by the uniform
signed tail with actual opposite mask \(Nqe\) and then
\(Nrd\), paying the fixed other harmonic powers.
On that short box the double Möbius Dirichlet series
factors with two \(\zeta^{-1}\) zeros. The one-log
moment on each side, including the CRT target-unit
density, is exactly \(\mathfrak S(N)c(rq)\), with
\(c(rq)=\prod_{p\mid rq}(p-1)/(p-2)\).
Taylor through degree three in each of
\(\log(dN/x)/L\) and \(\log(eN/y)/L\).
Only derivatives of order at least one on both sides
survive. The first coefficients are
\(F'(0)/L+O(1/L^2)\) and \(G'(0)/L+O(1/L^2)\).
Higher joint terms are \(O((\log L)^{O(1)}/L^3)\)
uniformly after the unit density; the absolute short
Taylor remainders are also negligible at that scale
after the fixed harmonic powers. If either profile
is flat on an initial interval, that leg is literally
constant on the entire short box, and the complete
principal instead saves arbitrary log powers.

Finally the original logs of \(r,q\) sum with their
true reciprocal harmonics over the fixed real windows.
Uniformly in polynomial lower endpoints,
\[
 \sum_{\substack{R_-<r\le R_+,\ r\ {\rm prime}\\r\nmid N}}
        \frac{\log r}{r}c(r)
    =\log(R_+/R_-)+O(1).
\]
The change from \(c(r)\) and the actual target-prime
exclusions costs \(o(1)\). The possible shared
prime diagonal, forbidden by compatibility, has
total \(\ll\sum_{p>\min(R_-,Q_-)}(\log p)^2/p^2=o(1)\).
The second harmonic is identical with its own windows.
Thus the complete mode-zero density is (1), using the
length \(|J|N\) after restoring the previously paid
central collar. The two-log absolute harmonic factor
is at most \(O(L^2)\), so the higher derivative
errors really are \(o(M_N)\).
If either profile is flat, the arbitrary-log
Möbius bound likewise remains after these two
harmonics. This proves both assertions.

Apply the flat case with \(\mathcal R,\mathcal Q\)
equal to the respective original lower gate up to
\(N^{.510}\) to subtract the actual balanced term
from the calibrated joint covariance. The retained
same-target condition does not imply any positive
or negative sign on the unpriced ultra-root side.
