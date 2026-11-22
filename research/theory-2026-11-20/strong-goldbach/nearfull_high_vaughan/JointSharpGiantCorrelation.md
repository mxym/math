# A genuine two-leg signed giant correlation at each even target

Let \(N\) be an individual sufficiently large even integer,
\(J\Subset(0,1)\) a fixed nondegenerate compact interval,
\(L=\log N,\ \ell=\log L\), and
\[
 M=|J|N\mathfrak S(N),\qquad
 R=R_J(N)=\sum_{\substack{x+y=N,\ x\in NJ\\x,y\ {\rm prime}}}
                         (\log x)(\log y).
\]
Here \(\mathfrak S(N)\) is the ordinary binary singular series
of [the original giant reduction](../giant_prime_divisor_remainder/Proof.md).
Fix \(0<a<b<1/2\), let \(\lambda=1/2-b\), and put
\[
                     U=N^\lambda e^{-\ell^3}.
\]
Take any two fixed real smooth profiles \(F,G\) on \([0,\infty)\),
constant on \([0,a]\) and zero on \([b,\infty)\); they may be signed.
For an integer \(n\asymp_J N\) with \(0<n<N\), set
\[
 \begin{split}
 t(d,n)&=\frac{\log(dN/n)}{L},\\
 P_F(n)&=\sum_{\substack{r\mid n,\ r\ {\rm prime}\\ U<r<n}}
            \log r\sum_{d\mid n/r}\mu(d)F(t(d,n)).
 \end{split}                                                       \tag{1}
\]
The prime marks here are literal, with no largest-mark convention,
and \(r<n\) excludes the prime cofactor-one atom.

**Theorem.** For every fixed \(A>0\) and all sufficiently large even
\(N\), without a radical restriction,
\[
 \sum_{\substack{x+y=N,\ x\in NJ\\(x,N)=1}}
                P_F(x)P_G(y)
       =F(0)G(0)(R-M)+O_{A,a,b,F,G,J}(NL^{-A}).                    \tag{2}
\]
The target-unit condition is part of this two-composite-leg
statement. It is not asserted that the discarded nonunit composite
mass is small. Each nonzero summand on the left has both \(x\)
and \(y\) composite. The genuine prime-pair term \(R\) on the
right is unconditioned since its nonunit contribution is negligible.

This is an actual **joint** signed correlation. The genuinely
prime–composite calibrations of a single leg do not evaluate it.
In particular, for \(F(0)=G(0)=1\), a new lower bound for the left
side strictly above \(-(1-\kappa)M\) for fixed \(\kappa>0\) would
give a binary representation. No such lower bound or binary
positivity is asserted.

## 1. The exact finite divisor observable

For either profile set
\[
 A_F(n)=\sum_{d\mid n}\mu(d)F(t(d,n))
            \left(\log(n/d)-
                  \sum_{\substack{k\mid n/d\\k\le U}}\Lambda(k)\right).
                                                                    \tag{3}
\]
On each actual row the bracket is
\(\sum_{k\mid n/d,\ k>U}\Lambda(k)\). Interchanging the finite
summations gives the term \(P_F(n)\) with its signs exactly as
in (1), the genuine prime atom
\[
                    L_F(n)=1_{n\ {\rm prime}}(\log n)F(0),
\]
and proper prime-power marks. Here \(F(t(1,n))=F(0)\)
on both fixed central intervals for sufficiently large \(N\), and
\(n>U\). This atom is present only for genuine prime \(n\).
The marks \(k>U\) which are proper powers are not put in either
prime slot. For any of the one- or two-leg products used below
all exceptional rows together cost
\[
 N^{1+o(1)}
    \sum_{\substack{k>U,\ k\le N\\k\ {\rm a\ proper\ prime\ power}}}
                         \frac1k
     \ll N^{1-\lambda/2+o(1)}.                                  \tag{4}
\]
This follows by counting actual multiples of each such \(k\)
in \(x\) or \(y\), with both product weights bounded by the
fixed divisor-power envelope \(N^{o(1)}\); the powers have
reciprocal tail \(U^{-1/2+o(1)}\). Consequently throughout the
proof \(A_F=L_F+P_F\) may be used in the stated aggregate sense.
If two prime inputs have a common factor with \(N\), then
\(x=y=N/2\) is that prime, with total weight \(O(L^2)\). Thus
\(\sum L_F(x)L_G(y)=F(0)G(0)R+O(L^2)\) even on the target units.

At real central \(n\) the exact coefficients of (3) can be
written
\[
 \begin{split}
 A_F(n)&=\sum_{q\mid n} a_{F,q}(n),\\
 a_{F,q}(n)&=\mu(q)F(t(q,n))\log(n/q)
       -\!\!\sum_{\substack{dk=q\\ k\le U}}
                       \mu(d)F(t(d,n))\Lambda(k).                \tag{5}
 \end{split}
\]
Only \(d\le N^b\) can occur on the real central range.
The mark-product modulus is the genuine \(q=dk\), not the
lcm, even when \(d,k\) share a prime. Hence all \(q\)'s in
(5) are at most \(Q=N^{1/2}e^{-\ell^3}\) for large \(N\);
this also includes the log term's \(q\le N^b\).
On the indicated central intervals the supremum plus total
variation of each coefficient is \(O_{F,J}(L\tau(q))\).
These are weights on real prefixes, not independent degree
or primality masks on the other variable.

## 2. Two different local models, both on their actual unit masks

We first record the analytic simplification of the finite
coefficient sums. For a positive integer \(H\le N^{O(1)}\), the
uniform real-prefix signed \(1/d\) harmonic of \(\mu(d)\) on
\((d,H)=1\) has complete sum zero, and the negative first log
moment is \(H/\varphi(H)\). This is the series
\(\zeta(s)^{-1}\prod_{p\mid H}(1-p^{-s})^{-1}\)
at \(s=1\) and its derivative. For arbitrary-log accuracy
on prefixes with endpoint at least \(N^{a/2}\), the absolute
excluded-prime inverse product at
\(\sigma=1-1/(10\ell)\) is \(\ell^{O(1)}\), uniformly in
\(H\le N^{O(1)}\): use \(\,p^{1-\sigma}=O(1)\,\) below \(L^2\)
and at most \(O(L)\) prime factors above \(L^2\).
Splitting the inverse-mask convolution at the square root
of the endpoint and using ordinary Mertens yields tails
\(O_D(L^{-D})\) for the zeroth and first log harmonic,
including all real strict/inclusive endpoint conventions.
For \(1/\varphi(dk)\) instead, the same uniform masked
argument, with \(1/\varphi(k)\) taken out, is precisely
[the original reduction, §1](../giant_prime_divisor_remainder/Proof.md):
the logarithmic first moment at \(k=1,H=N\) is
\(\mathfrak S(N)\) and the zeroth harmonic is zero for all
\(k\). The \(k\)-dependent local factors at primes dividing
\(k\) account for the actual product totient. At each
central \(n\), multiplying these harmonics by
\(F(t(d,n))\) replaces the limiting weights by \(F(0)\),
with arbitrary-log accuracy by bounded variation and the
flat interval \(0\le t\le a\). Indeed the first possible
changed \(d\)'s have \(d\gg_J N^a\).

With (5) this proves two distinct evaluations:
\[
 \begin{split}
 \sum_{(q,H)=1}\frac{a_{F,q}(n)}q
    &=F(0)\frac{H}{\varphi(H)}+O_D(L^{-D}),\\
 \sum_{(q,N)=1}\frac{a_{F,q}(n)}{\varphi(q)}
    &=F(0)\mathfrak S(N)+O_D(L^{-D}).                            \tag{6}
 \end{split}
\]
The first holds uniformly for all \(H\le N^{3/2}\)
and the real \(n\)-range; the second uses \(H=N\).
Both short \(k\)-parts vanish in the main because their
signed zeroth \(d\)-harmonic does, with \(1/k\) or
\(1/\varphi(k)\) respectively. They cost only a logarithmic
loss in the error since
\(\sum_{k\le U}\Lambda(k)/\varphi(k)\ll L\).
In the log terms the \(\log n\) part has the same zero and
the first negative log moment in \(d\) yields (6).
These evaluations use no prime model on the marked side.

Now use true-prime maximal-prefix Bombieri–Vinogradov
[at the usual square-root level](https://doi.org/10.1112/S0025579300005313).
For the genuine weighted prime \(x\) opposite \(A_G(y)\),
the actual modulus \(q\) divides \(y=N-x\), so it has the
literal residue \(N\bmod q\) on \(x\); units make this
reduced. The prime weight is \(F(0)\log x\), and \(q\le Q\)
has arbitrary fixed log reserve. Group the true coefficients
from (5) at \(q\), apply ordinary partial summation on
the real central intervals, and clip \(\tau(q)\) by a
sufficiently large power of \(L\). The dropped moduli cost
arbitrary logs by the trivial discrepancy \(O(NL^2/q)\)
and fixed divisor moments. Correcting proper prime powers
in the BV replacement may use the same actual divisor
envelope on the \(O(N^{1/2+o(1)})\) power values. The
\(\varphi(q)^{-1}\) model in (6) therefore gives
\[
  \sum_{x+y=N,\ x\in NJ,\ (x,N)=1} L_F(x)A_G(y)
       =F(0)G(0)M+O_D(NL^{-D}).                                \tag{7}
\]
Reversing the prime leg gives the same main
for \(\sum A_F(x)L_G(y)\), with the same real support.

For the both-integer product the calculation is different.
All rows are **restricted to** \((x,N)=1\), hence both
\(q\mid x\) and \(t\mid y\) are target units. Such a pair can
occur only if \((q,t)=1\): a common prime would divide
\(N\). The extra condition \((x,N)=1\) is not free;
it needs an actual unit count on the simultaneous
progressions \(q\mid x,\ t\mid y\).

We apply a finite Bonferroni expansion of this exact unit
indicator, over squarefree labels \(e\mid\operatorname{rad}(N)\)
of degree at most \(R_0=\lceil C_D\ell/\log\ell\rceil\), with
large fixed \(C_D\) chosen after the requested precision.
For any actual integer \(x\), the pointwise omitted-degree
error is bounded by the count of its true divisors
\(e\mid x,\ e\mid\operatorname{rad}(N)\) of degree \(R_0+1\).
The mean square of this count on \(1\le x\le N\) is bounded
by the sum of reciprocal least common multiples of the
two degree-\(R_0+1\) labels. Each prime of their union can
be in the first, the second, or both labels. Since
\(\sum_{p\mid N}1/p=O(1+\log\ell)\), this mean square is at most
\[
    \sum_{j=R_0+1}^{2R_0+2}
             \frac{(3\sum_{p\mid N}1/p)^j}{j!}
                    \ll_D L^{-D}
\]
to arbitrarily large fixed \(D\) after increasing \(C_D\).
Cauchy with actual crossed divisor moments controls the
unit error even with the product weights
\(O(L^2\tau(x)^2\tau(y)^2)\). This is the same true-label
Boolean estimate as in
[WholeGiantSmallFactor.md, §2](WholeGiantSmallFactor.md).

For every retained triple \((q,t,e)\) the moduli are pairwise
coprime: \(e\mid\operatorname{rad}(N)\), while \(qt\) is a
target unit and \(q,t\) were already required coprime.
The three genuine requirements are
\[
                    x\equiv0\bmod q,\quad
                    x\equiv N\bmod t,\quad
                    x\equiv0\bmod e.
\]
There is one CRT class modulo \(qte\), with real interval
density \(1/(qte)\), whatever the size of \(e\).
Partial summation costs
\(O(L^2\tau(q)\tau(t))\) per triple in integer floors.
The number of \(e\)-labels is at most
\(\exp(O_D(\ell^2/\log\ell))\), by \(\omega(N)=O(L)\).
Together with \(\sum_{q\le Q}\tau(q)\ll QL\),
the floor is thus \(O_D(NL^{-D})\), since
\(Q^2=N e^{-2\ell^3}\).
This is why the common mark \(U\) above has a subpower
reserve rather than just a fixed log denominator.

In this CRT main, replacing the finite alternating
\(e\)-harmonic by the true density \(\varphi(N)/N\) is
also permitted: the reciprocal next-degree bound is
\((\sum_{p\mid N}1/p)^{R_0+1}/(R_0+1)!\), which absorbs
the absolute harmonic costs of \(q,t\). There is no
large \(\tau(N)\) factor in either the floor or the
unit-density tail. We obtain
\[
 \begin{split}
 \sum_{\substack{x+y=N,\ x\in NJ\\(x,N)=1}} A_F(x)A_G(y)
  ={}&\frac{\varphi(N)}N
       \int_{NJ}
        \sum_{\substack{q,t\le Q\\(qt,N)=1,\ (q,t)=1}}
         \frac{a_{F,q}(x)a_{G,t}(N-x)}{q t}\,dx
          +O_D(NL^{-D}).                                       \tag{8}
 \end{split}
\]
For every actual \(q\) in the retained model apply the first
line of (6) to \(t\) with \(H=Nq\le N^{3/2}\).
The factor \(Nq/\varphi(Nq)\) combines with the **actual**
unit factor \(\varphi(N)/N\) to give \(q/\varphi(q)\)
since \((q,N)=1\). Thus the outer harmonic becomes the
second line of (6). This proves that (8) equals
\(F(0)G(0)M+O_D(NL^{-D})\), even for signed profiles.
Finally subtract the two contributions (7) from (8),
add \(\sum L_F(x)L_G(y)\), and use (4).
This gives exactly (2).

## 3. A separate comparison with a parity model

Here is one use of the extra joint constraint; it is **not**
an inference that the true counts follow an independent
angular model. Normalize the two-leg comparison in units
of the same \(M\) as (8), i.e. after the fixed target-unit
and singular local factors. For a fixed positive angular
floor \(\eta\), take the ordinary one-leg angle measure
on partitions \(u_i>\eta,\ \sum_i u_i=1\) with rank \(k\)
density \(\nu_\eta^{*k}/k!\) at total angle one, where
\(\nu_\eta(du)=1_{u>\eta}\,du/u\), retaining the individual
angles in each convolution. On this normalized model
a prime has mass one. Target primes above \(N^\eta\)
have total reciprocal mass \(O(L/N^\eta)=o(1)\).
Macroscopic marked factors have local correction
\(1+O(N^{-\eta})\); collisions of shared prime labels
are negligible at fixed rank by reciprocal prime squares.
The angular comparison is made after these local
factors, not in place of the true CRT computation.

The ordinary one-leg **composite** score (1) has limiting
mass zero as \(\eta\downarrow0\), with marks
\(u_r>\lambda\) and the prime atom removed. To verify this,
put
\[
 A_\eta=\exp_*(-\nu_\eta),\quad B_\eta=\exp_*(\nu_\eta),
       \quad J_\lambda(du)=1_{u>\lambda}\,du .
\]
The distinguished mark's logarithm changes \(du/u\)
to \(du\). Opening the selected subset of other factors
with signs gives the full score's density at total angle
one of \((F A_\eta)*J_\lambda*B_\eta\). The factors
\(k!\) and the choice of the distinguished mark/subset
are exactly the ordinary exponential-convolution factors.
Since \(A_\eta*B_\eta=\delta_0\) and \(F=F(0)\) below
\(a\), subtracting \(F(0)A_\eta\) changes this density by
\[
      O\!\left(B_\eta([0,1])\,|A_\eta|([a,1])\right)
       =O\!\left(\eta^{-1}\rho(a/\eta)\right)=o(1).
\]
Here the signed-tail estimate is the Dickman expression
\(A_\eta=\delta_0+\eta^{-1}\rho'(u/\eta)\,du\) proved in
[RoughQuotientWholeAnnulus.md, §3](RoughQuotientWholeAnnulus.md),
and \(B_\eta([0,1])\le1/\eta\) by its positive
convolution expansion. Thus the full score tends to
\(F(0)\), and its single prime atom is exactly \(F(0)\).
The asserted composite normalization follows.

In the independent product of those two ordinary angle
measures the composite–composite score in (2) is therefore
\(o(1)\). Consider the following specific proposed
replacement. Conditional on a prime on one side, double
the even ranks on the other and remove the odd ranks.
Remove the prime–prime corner. Keep the ordinary
both-composite angular measure except for subtracting
a product of two mass-one angular populations supported
on semiprimes with the smaller angle tending to zero
and the larger to one. Such populations can be taken
with bounded nonnegative density dominated by the
ordinary model: the available rank-two mass with
minimum in \((\eta,\delta)\) is
\(\int_\eta^\delta du/(u(1-u))\to\infty\) for
\(\eta\ll\delta\downarrow0\).
This replacement can preserve below-root factorial
tests with fixed positive angular lower bounds while
allowing genuinely occupied fixed-angle even–even cells.

But the modified both-composite model still has score
\(o(1)\) in the new joint test. Indeed on each of its
removed endpoint semiprimes the only \(u_r>\lambda\)
is the giant. Its quotient has one factor of angle
smaller than \(a\), so the inner score is
\(F(0)-F(u)=0\), and likewise with \(G\).
On prime–composite and prime–prime rows the joint
composite score is already identically zero. In
contrast, for \(F(0)=G(0)=1\), a genuinely
prime-free target would have joint value \(-1+o(1)\)
by (2). Thus this particular composite-independent
parity model with solely endpoint compensation does
not meet the actual coupled arithmetic constraint.
This comparison does not rule out other correlations
on true interior composite ranks, or bound their sign.
