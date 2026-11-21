# A genuine adverse chamber survives every compact signed average of the one-sided cutoffs

This concerns **pointwise tuning only**, for the single reflected semiprime
profile and one-sided \(\mu\)-center of
[BalancedSemiprimeEvenRankNeck.md](BalancedSemiprimeEvenRankNeck.md).
It is not an obstruction to a signed estimate using the fixed additive
equation.

Use the same notation \(N=2x\), prime \(s\), \(Q_0=x/s\), and \(sq\in(x/2,x]\).
For each normalized cutoff triple \(\xi=(u,z,v)\) in a compact set
\[
             0<v<z\le u<1/2,\qquad u+v<1/2,
\tag{1}
\]
put \(U_\xi=Q_0^u,\ B_\xi=Q_0^{1-z},\ V_\xi=Q_0^v\);
use (2) of the preceding note with these parameters. Denote its
coefficient by \(C_\xi(q)\). Let \(\nu\) be any real finite signed measure
on this compact set with \(\nu(\mathrm{all})=1\), and put
\(C_\nu(q)=\int C_\xi(q)\,d\nu(\xi)\).
This includes arbitrary finite signed combinations with total
coefficient 1, not just probabilities. All statements below are for a
fixed measure. The obstruction below is coefficient-level: it does not assert a uniform whole-exchange formula for the entire family.

**Proposition.** For each such \(\nu\), there is a fixed finite-rank
open chamber of genuine squarefree \(q\) with \(C_\nu(q)\le-\gamma_\nu<0\).
On the genuine \(m=ph=N-sq\) profile of the preceding note its adverse
contribution is \(\gg_{\nu,\eta} M_N\) for at least one (and hence for
infinitely many) even target in every sufficiently large fixed relative
interval \([1.98X,2.02X]\). Neither the value of \(\gamma_\nu\) nor the
rank is uniform in the selected measure. This asserts only an adverse
**subsum**. Other cohorts can compensate it.

## One macro prime gives an incomplete core sum

Let \(v_*=\inf_{\operatorname{supp}\nu}v>0\); the support of its
\(u\)-marginal \(\rho\) is compact in \((0,1/2)\). Define its upper
tail \(H(t)=\rho([t,\infty))\); thus \(H(t)=1\) for small \(t\)
and \(H(t)=0\) for \(t\) just below \(1/2\). For a genuine squarefree
factorization
\[
          q=P r_1\cdots r_k,\qquad
    a_i=\frac{\log r_i}{\log Q_0}<v_*,\qquad
          \frac{\log P}{\log Q_0}>1/2 ,
\]
there is only one eligible true \(\Lambda_{>V_\xi}\) label, \(P\).
Every remaining divisor divides the core \(r_1\cdots r_k<Q_0^{1/2}\)
and falls below **every** \(B_\xi\), so it is never modified by the
long-free \(\mu\) subtraction. The complete Möbius sum on the core
is zero. Hence, without any approximation in the arithmetic,
\[
 C_\nu(q)=-\frac{\log P}{\log q}
       \sum_{I\subseteq\{1,\dots,k\}}(-1)^{|I|}
                   H\!\left(\sum_{i\in I}a_i\right).
\tag{3}
\]
This uses \(r>U_\xi\) sharp, so \(H(t)\) includes the endpoint in its
complementary test. It also applies to signed smooth cutoff
averages, by finite summation within the integral. No assumption of
factor independence in the fixed additive equation enters (3).

Set \(t_*=\inf\{t>0:H(t)\ne1\}\in(0,1/2)\).
There are continuity points \(t>t_*\) arbitrarily close to \(t_*\)
with \(H(t)\ne1\): the tail of a finite signed measure is left
continuous and has at most countably many discontinuities, and a
nonzero departure at any point persists in a sufficiently small
interval to its left. Choose one sign of \(H(t)-1\) occurring
arbitrarily close in this way. Fix \(k\ge2\), of whichever parity
makes \((-1)^k(H(t)-1)>0\) on this sequence, and large enough that
\(t_*/k<v_*\). Now choose such a continuity point \(t\) sufficiently
close to \(t_*\) that
\[
                 t/k<v_*,\qquad t(1-1/k)<t_*.
\tag{4}
\]
At \(a_i=t/k\) all **proper** subset sums are below \(t_*\), so
(3) is exactly \(-(\log P/\log q)(-1)^k(H(t)-1)<0\).
The inequalities in (4) are strict, and \(H\) is continuous at
\(t\). Perturb the \(a_i\) into distinct fixed positive exponent
intervals near \(t/k\), so the same strict inequality holds with a
negative bound \(-\gamma_\nu\) on a product of open intervals.
Choose the large prime to maintain \(q\asymp Q_0\); then its share
is within a fixed arbitrarily small distance of \(1-t>1/2\), plus
the \(O(1/\log Q_0)\) central-interval error. All proper sums still
stay \(<t_*\).
This proves the pointwise claim, including smooth or signed averages.

## The adverse cohort occurs in the literal prime-product equation

Use a large auxiliary \(X\) and \(s\) genuine prime with exponent in a
fixed compact subinterval of \((.10,.14)\) relative to \(X\).
Choose the distinct genuine primes \(r_i\) in the fixed small
exponent bands just constructed relative to \(X/s\).
For each such tuple put \(R=\prod r_i\) and take the genuine prime
\[
                       .79X/(sR)<P<.81X/(sR).
\]
This forces \(n=sq\in[.79X,.81X]\).
Each core prime band has a positive bounded harmonic mass,
uniformly in \(s\), by Mertens or ordinary prime PNT.
The macro prime PNT applies uniformly to the displayed fixed-ratio
interval, whose length is polynomial in \(X\). Thus the number of
available \(q\) at fixed \(s\) is \(\gg_\nu X/(s\log X)\).
Overlaps of ordered labels can be excluded by taking disjoint
exponent bands for the \(r_i\), as already arranged above.

Next take true prime \(p\) with
\[
          X^{1/2-\eta-w/2}<p s^{1/2}<X^{1/2-\eta+w/2},
\]
and true prime \(h\) in \([1.19X/p,1.21X/p]\).
Demand that both \(p,h\) avoid the at most \(k+2\) true prime
bases of \(n\). By the same harmonic and prime PNT estimates,
the resulting \(m=ph\) count is \(\gg wX/\log X\) at each fixed
\(s,q\); the excluded prime labels cost a negative power.
The genuine small \(p\) and large \(h\) have separated exponents,
so every \(m\) has unique labels on this support.

All these choices are odd, hence \(N=n+m\) is even,
\(N\in[1.98X,2.02X]\), and \(x=N/2\in[.99X,1.01X]\).
They give exactly the central physical window, with
\((m,N)=(m,n)=1\). Passing from \(X\) to the true \(x\)
changes all normalized sizes by \(O(1/\log X)\). The
strict inner \(p\)-band with \(w/2\) still obeys the real
\(p\)-band of width \(w\), and the fixed open adverse exponent
chamber stays valid (shrink core boxes once in advance).
On the whole chosen support \(W_s(q)\gg1\) and
\(-F_s(m)\asymp\log X\). Summing the exact positive
adverse subsum \(W_s(q)F_s(m)C_\nu(q)\) over the even targets
of this interval therefore gives
\[
                      \gg_{\nu,\eta} X^2/\log X.
\tag{5}
\]

Finally \(\sum_{N\le 3X,\,2\mid N}\mathfrak S(N)\ll X\).
Indeed expand the odd-prime factors
\(\prod_{\ell\mid N,\ell>2}(1+1/(\ell-2))\) over squarefree
divisors and bound the number of their multiples by \(3X/d\);
the ensuing Euler product \(\prod_{\ell>2}(1+1/(\ell(\ell-2)))\)
converges. Thus the sum of \(M_N\) on this interval is
\(O(X^2/\log X)\), and (5) forces some even \(N\) with adverse
subsum \(\gg_{\nu,\eta}M_N\). This does not say every \(N\) has
this population. It shows that a compact signed average of
these cutoffs cannot by itself make the adverse population
\(o(M_N)\) uniformly by pointwise sign tuning. Any favorable
**net** estimate must use arithmetic cancellation or a
different weight family. No Goldbach conclusion follows.

## Related work

[Arneth VII, September 28, 2026](https://zenodo.org/records/23011047) describes an obstruction to defeating parity by a coefficient-level recoding; [Arneth XII, September 28, 2026](https://zenodo.org/records/23016346) considers prime-filter obstructions and balanced five-factor coefficients. The result here concerns the specified compact signed class of one-sided cutoffs, with a genuine fixed-rank prime-product cohort and no cancellation claim. The existing [marginal witness](JointMarginalParityWitness.md) is about a different relaxation and does not supply the literal prime-product cohort used here.
