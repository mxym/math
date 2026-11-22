# An explicit cutoff for the true whole tiny union of the sextic

Retain the genuine fixed even target \(N\), interval \(J\Subset(1/3,2/3)\),
target units, \(L=\log N\), \(M=|J|N\mathfrak S(N)\), and original
sextic \(F,H,\Pi,R_J\) in [the degree-six proof](Proof.md).
Use only the physical rough compensation
\(Q=[-H]_+1_{P^->N^{.1251}}\), \(G=H+Q\), and set
\[
 b=1/250,\qquad I=1_{P^-\le N^b},\qquad T=IH=IG.
\]
The [ordinary-box improvement](RoughOrdinaryMassBoxes.md) gives
\(R_J\ge .954M+\langle G,G\rangle+o(M)\)
and each ordinary \(Q\) mass is \(<.01701M\).
Its genuine positive receiver multiplier is \(<.852\), unchanged
from [the ordered-mark theorem](OrderedMarkCovariance.md).

**Theorem.** The original, sharp, signed contribution from the entire
actual union where either coordinate has a prime factor at most
\(N^{.004}\) is \(>-.760M+o(M)\). Consequently
\[
 R_J\ge .194M+\langle (1-I)G,(1-I)G\rangle+o(M).
\]
In the remaining genuine rows both least factors exceed \(N^{.004}\)
and all ranks are at most 250. There is no lower bound for this
remaining signed term, no fraction of the conjecture asserted, and
no addition to a separate profile or mark compensation.

## 1. Stop by product and cancel at the actual least prime

Put \(\kappa=9/2,\ c=\kappa b,\ d=c+10^{-6},\ w=6b\), and
\(B(v)=35v^4-84v^5+70v^6-20v^7\) on \(0\le v\le1\), extended as
0 below and 1 above. Use the tapered \(F_*(t)=F(t)B((1/2-t-d)/w)\),
with both original jets at zero, and its true score \(H_*\).
Write \(E=H-H_*\), \(D=(1-I)E\). On a fixed floor \(0<a<b\) use
the actual primes in \(N^a<p\le N^b\). Let \(A\) be \(H_*\) times
the nonempty-hit inclusion--exclusion sum over their literal
subset products of angle at most \(c\); the sign of a nonempty
subset of size \(j\) is \((-1)^{j+1}\). The angle of a product is
its log divided by \(L\). Every term has an actual marked prime
and so has no prime subtraction.

For a row with a hit, write \(p_0\) for the least prime in the bank,
\(u_0=\log p_0/L\), and pair each subset of the other marked primes
with its union with \(p_0\). The signed difference between the hit
indicator and the stopped sum is exactly
\[
 \sum_{\substack{J'\subseteq {\rm bank}(n)\setminus\{p_0\}\\
               c-u_0<\sum_{p\in J'}\log p/L\le c}}
                   (-1)^{|J'|}.                                      \tag{1}
\]
Call each summand's actual pair \((p_0,J')\) a certificate. Let \(V\)
be \(H_*\) times (1), zero without a hit. Thus its absolute value is
bounded by \(|H_*|\) times the number of certificates, not by
independent contributions from all mark sizes. On rows with least
factor above \(N^a\), \(p_0\) is the actual global least prime,
every other certificate label has angle at least \(u_0\), and
the joined \(h=p_0\prod_{p\in J'}p\) has angle \(>c\) and \(\le c+b\).

In all ensuing statements first fix \(a\), apply the true ordinary
and paired compact rank and floor limits, and then take \(a\downarrow0\).
Replacing the bank-hit by \(I\), and excluding cells with a prime
\(\le N^a\) when bounding \(V\), costs an amount tending to zero on
the ordinary and paired normalized scales. Indeed each hit or stop
is bounded in absolute value by \(1+2^{\omega(n)}\); the physical
phase envelope in [the degree-six proof, §1](Proof.md) tolerates
this tilt on each arm since \(2(4/\pi)<4\). Take a strict additional
rank and smallest-factor grace exponent. Each profile here is
\(C^3\) with fourth derivative of bounded variation, so its Fourier
decay of order five pays that tilt. Actual non-squarefree rows
at the fixed floor, angle ties on cell walls, changes between own
and target logs, and actual target-unit removals are handled by
the same genuine square bounds and fixed compact-angle approximation.
There is no removal of physical small rows of nonnegligible score.

## 2. Signed ledger and the two explicit ordinary error bounds

Write \(m(Z)\) for the ordinary \(\mathfrak S(N)\)-weighted mass
of a score \(Z\) divided by \(M\), in its applicable central interval.
For every actual compact angular product source \(Z\), the stopped
sum has
\[
        \langle A,Z\rangle/M=\langle Z,A\rangle/M
                    =c_A m(Z)+o(1).                               \tag{2}
\]
Here the two orientations use their own reflection interval. To
see the level exactly, open each actual subset product \(h\);
the quotient profile is \(\prod_{p\mid h}(1-\mathcal T_{\log p/L}) F_*\).
A true modulus \(h\ell\) is at most \(N^{c+1/2-d}<N^{1/2}\);
multiplicity is divisor-bounded. Use genuine product BV after
fixed rank/angle truncation as in
[the whole tiny compensation, §2](WholeTinyRoughCompensation.md).
The actual reduced masks are \(NhZ_{\rm int}\), with \(Z_{\rm int}\)
the source integer; polynomial target-unit and source-label
omissions have negligible reciprocal mass at fixed floor.
The short signed harmonic gives the first-derivative difference
with prefactor \(1/\varphi(h)\) and real singular series.
Because all selected angles sum to at most \(c\), the exact
derivative used there is \(F'\). Its polynomial degree five kills
orders above five. All orders through four are unrestricted
by the stop. The omitted order five has mass at most \(672 b^5\).
The formula remains valid for \(R=T-A\) and for \(V,D\) by the
same true finite-rank/floor limits of §1. Likewise \(E\) has both
jets zero and the standard tapered short transfer gives
\(\langle E,Z\rangle=\langle Z,E\rangle=o(M)\) and \(m(E)=0\).

The exact ordinary unopposed \(m_T=m(T)\) differs by less than
\(10^{-12}\) from the polynomial \(m(b)\) in the
[whole tiny compensation](WholeTinyRoughCompensation.md),
with no asymptotic-in-\(b\) assumption. One direct check uses the
rough ordinary angular convolutions \(B_b^\pm=\exp_*(\pm1_{t\ge b}dt/t)\).
For \(t>0\), \(b_b^+(t)=\omega(t/b)/b\) and
\(B_b^-=d(1_{t\ge0}\rho(t/b))\); these follow by differentiating
the transforms and using the Buchstab and Dickman recurrences.
The no-hit ordinary divisor mass is
\(\int F(t)B_b^-(dt)b_b^+(1-t)\). On its support \(t\le1/2\),
replace \(\omega((1-t)/b)\) by \(e^{-\gamma_E}\):
the recurrence \(u\omega'(u)=\omega(u-1)-\omega(u)\) bounds
\(\sup_{u\ge k}|\omega'(u)|\) by \(1/k\) times the previous
supremum for \(k\ge3\), starting from \(\sup_{u\ge2}|\omega'|\le1\).
The error here is bounded by the resulting factorial tail at
\(k=125\), including \(b^{-1}\) and the finite absolute mass of
\(B_b^-\). Integrate by parts against \(e^{-\gamma_E}\rho(t/b)/b\).
This probability law has the five compound-Poisson moments
in the whole tiny compensation. Extending the polynomial
\(F'\) past \(1/2\) costs less than \(10^{-12}\), by
\(\rho(v)\le1/\lfloor v\rfloor!\) and the explicit degree-five
coefficient sum. The prime subtraction contributes exactly
the ordinary prime mass 1 on the no-hit arm. In particular
\[
 |m_T|<.300,\quad |c_A|<.301,\quad |m(R)|=|m_T-c_A|<10^{-7}.        \tag{3}
\]

Up to the vanishing physical floor error, \(R=V+E-D\).
By (2), the double tiny term is exactly
\[
 \langle T,T\rangle/M
   =m_T^2-m(R)^2+\langle V-D,V-D\rangle/M+o(1).                   \tag{4}
\]
This pays the two terms linear in the residual by their
actual signed calibration. One need not upper-bound a
single remainder against the entire absolute sextic score.
In the single tiny term,
\[
 \langle T,G\rangle/M=c_A m(Q)+m(R)
                  -\langle R,\Pi\rangle/M+\langle R,Q\rangle/M+o(1).
\]
Replace \(R\) by \(V-D\) in the last two pairings, since \(E\)
annihilates both actual sources. The original genuine \(3.446\)
prime-opponent upper and the \( .852\) rough receiver upper,
applied to \(|V|+|D|\), show that the absolute loss in those terms
is at most \(4.298\,m(|V|+|D|)+o(1)\). These are actual inequalities
for compact product sources and then their physical floor limits,
not full-rank independence.

Put \(e(s)=F(1/2-s)-F_*(1/2-s)\ge0\), supported on \([0,d+w]\).
On the \(b\)-rough arm the actual divisor \(q\) in the defect
and its quotient are both \(b\)-rough; their ordinary positive
harmonic densities are at most \(1/b\) each. Thus
\[
 m(|D|)\le B_D:=b^{-2}\int e(s)\,ds<.015765 .
\]
For every nonnegative true compact product source \(Z\) there is
also the actual conditional upper
\[
        \langle Z,|D|\rangle/M
          \le U_D m(Z)+o(1),\qquad
 U_D=\frac2b\int e(s)\frac{ds}{s}+\frac23 B_D<.017632.             \tag{5}
\]
Indeed open the actual \(q\) of angle \(1/2-s\) and upper-sift
its actual quotient, with product modulus at a fixed strict
sub-root level and the same true reduced source and target units.
The quotient level exponent tends to \(s\). If \(s\le 2b\)
use a linear upper sieve at level parameter 2, sifting only
to exponent \(s/2\); if \(2b<s\le3b\) use \(s/b\);
both give multiplier \(2/s\). For \(s>3b\) the multiplier is
at most \(e^{-\gamma_E}F_{\rm upper}(3)/b=2/(3b)\).
The ordinary harmonic of true \(b\)-rough \(q\) is bounded by
\(ds/b\). Prove the result first for \(s\ge\eta>0\) with strict
level margins, then send \(\eta\downarrow0\); the physical
collar of \(D\) costs \(o_\eta(M)\) by the actual amplitude
and the fourth-order zero Fourier envelope.
The same calculation works in either orientation. It gives
\((B_D+2m(|V|))U_D\) for the total three absolute
\(D,D\), \(V,D\), \(D,V\) terms in (4).

## 3. An effective actual bound on the two stopped remainders

For every actual certificate put \(x_0=u_0/b\) and
\(\beta=x_0^{3/2}\). On each row let
\[
 X=(H_*/L)^2\sum_{\rm certificates}\beta^{-1},\qquad
 Y=\sum_{\rm certificates}\beta.
\]
Both are zero unless there is a certificate. For each actual
ordered certificate pair, weighted AM--GM with the two
\(\beta\)'s gives
\[
 |V(x)V(y)|\le \tfrac12 L^2
                      \bigl(X(x)Y(y)+Y(x)X(y)\bigr).              \tag{6}
\]
This is before summation; every multiplicity is present. For
an actual nonnegative compact product source \(Z\), obtain an
upper on \(LY\) by opening its literal joined modulus \(h\)
and upper-sifting the free quotient at primes \(<p_0\), since
\(p_0\) is the actual global least factor. Fix the floor \(a\)
as in §1. The actual level is \(N^{.499}/h\), and all
\(\log h/L\le c+b\), so the linear upper parameter is \(>3\)
uniformly. Moduli \(h\ell\) keep \(h,\ell\) coprime since all
prime divisors of \(h\) are at least \(p_0\), and the real
source, tag and target units are retained. The conditional density
bound is \( (2/3+o(1))\mathfrak S(N)/(u_0L h)\), using
\(e^{-\gamma_E} F_{\rm upper}(3)=2/3\); polynomial \(h/\varphi(h)\)
corrections are \(1+o_a(1)\). This applies to the genuine
compact source \(Z=LX\) as well, with the same rank and floor
cut before using product BV.

For fixed \(x_0\), the ordinary reciprocal harmonic of the other
names, with scaled angles in \([x_0,1]\), at total \(s\)
has upper density \(\omega(s/x_0)/x_0\) (drop the upper1).
Here \(s/x_0\ge\kappa-1>2\), so \(\omega(s/x_0)\le.6\).
This follows on \([2,3]\) from \((1+\log(v-1))/v\le.6\)
and for larger arguments by integration of the recurrence.
The interval in (1) has width \(x_0\). Thus integrating the
actual named labels with their ordinary unordered harmonics gives
\[
       \langle Z,LY\rangle/M\le
       \frac{(2/3)\,.6}{b}
                    \int_0^1x_0^{-1/2}dx_0\,m(Z)+o(1)
                    =\frac{.8}{b}\,m(Z)+o(1).                  \tag{7}
\]

It remains to bound two **ordinary** integrals, \(m(|V|)\)
and \(m(LX)\), with no paired angular model. Let
\(A_\xi(t)=|1-e^{i\xi t}|\) and \(J_j(u)=\int_0^u A_1(t)^jdt/t\)
for \(j=1,2\). At scaled frequency \(\tau=b|\xi|\), let
\(C_j(\tau)\) be the positive harmonic of actual certificate
angles scaled by \(b\), with each named angle weighted by
\(A_\tau(t)^j\), and for \(j=2\) multiply additionally by
\(x_0^{-3/2}\). The other angles are unordered. For the free
complement in the ordinary angular measure, the nonnegative
convolution with label weight \(A_\xi(t)^j\) has density
at total \(v>0\) at most \(2^j e^{J_j(|\xi|)}/v\).
This is the recurrence obtained by differentiating the
convolution exponential; it includes the possible singleton
contribution. Drop its least-factor restriction for this upper.
Here \(v\ge v_0=1-c-b>0\). With Fourier transform
\(\widehat F_*(\xi)=\int F_*(t)e^{-i\xi t}dt\), a common real
left extension being allowed,
\[
 \begin{split}
 B_V&=\frac2{\pi v_0}\int_0^\infty
           |\widehat F_*(\xi)|e^{J_1(\xi)}C_1(b\xi)\,d\xi
                                \ \ge m(|V|),\\
 B_X&=\frac2{\pi\sqrt{v_0}}\int_0^\infty
           |\widehat F_*(\xi)|e^{J_2(\xi)/2}\sqrt{C_2(b\xi)}\,d\xi
                                \ \ge \sqrt{m(LX)} .
 \end{split}                                                     \tag{8}
\]
The second follows by Minkowski on the single ordinary positive
measure of a row and its named certificate: square the product
of phases on that **same** integer, then integrate its square
root in the Fourier variable. It assumes neither parity
balance nor independent completed factors on the true pairing.
In particular (6)--(8) bound the literal paired stopped
remainder by \((.8/b) B_X^2 M+o(M)\).

## 4. Reproducible outward certificate

The [rational driver](check_explicit_tiny_stop.py) compiles the
[integer convolution](check_explicit_tiny_stop.cpp), and checks
\(B_V<.01982,\ B_X<.04193\) in (8). Here are its enclosing
choices. At \(\tau\le.3\), the certificate has at least five
labels; \(A_\tau(x)\le\tau x\) gives
\(C_1\le1.35\tau^5/120\) and
\(\sqrt{C_2}\le.075\tau^5\).
At \(\tau\ge40\) the same positive renewal recurrence at
\(s\ge\kappa-1\) and the literal width \(x_0\) give
\[
 C_1(\tau)\le 4e^{J_1(\tau)}/(\kappa-1),\qquad
 C_2(\tau)\le32e^{J_2(\tau)}\sqrt{\tau}/(\kappa-1).
\]
The second uses \(\int_0^1 A_\tau(x)^2 x^{-3/2}dx\le8\sqrt\tau\),
by splitting at \(2/\tau\).
Use \(e^{J_1(u)}\le6\max(1,u^{9/7})\): below \(2\pi\) the
sine Taylor gives \(J_1(u)\le u-u^3/72+u^5/9600\);
above \(2\pi\), the bounded primitive of
\(|1-e^{iu}|-4/\pi\) gives an upper excess at most \(1/(2\pi)\)
by integration by parts. Use \(e^{J_2(u)/2}\le2u\) for
\(u\ge20\), from \(\gamma_E+\log u-\operatorname{Ci}(u)\) and
\(|\operatorname{Ci}(u)|\le2/u\); below 20 use the elementary
bounds in the driver. For \(\xi\ge40/b\) the finite list of
polynomial endpoint jumps gives an exact \(\xi^{-5}\)
upper coefficient. At bounded frequencies use the lesser of
the \(L^1\) and derivative bounds at each allowed order,
separately for the sharp profile and its tapered difference.
They use rational polynomial midpoint integration with a
Bernstein bound on the derivative.

In the middle range the angular bins have length \(1/256\).
For each least bin \(i\), enlarge the other label set to all
bins \(\ge i\); each integrated label weight is bounded by
the bin supremum from \(A_\tau(x)\le\min(\tau x,2)\) at the
upper frequency. The lower bin indexes of \(k\) other labels
sum to at most \(256\kappa\), and at least
\(256\kappa-i-1-k\) for a true certificate. For \(k\le40\)
widen by the maximum possible \(k\); for \(k>40\) use its
complete exponential majorant divided by \(41!\) with
the usual power of the total label mass. The convolution
is the actual positive exponential series in the discrete
index; its factorial and all multiplications are rounded
up in fixed integer scale before any use. The one zero-index
bin contributes its ordinary exponential. Integrate the
distinguished \(x_0^{-3/2}\) weight at bin zero before
majorizing; its \(\min(\tau x_0,2)^2\) factor keeps it
integrable. All denominator and endpoint roundings
are specified in the attached checker.

Finally, since \(G\) has tiny part \(T\), the true union is
\(\langle T,G\rangle+\langle G,T\rangle-\langle T,T\rangle\).
By (3)--(8), its debit divided by \(M\) is bounded by
\[
 2(.301)(.01701)+(.300)^2
   +2(4.298)(B_D+B_V)+(B_D+2B_V)U_D
   +(.8/b)B_X^2+10^{-4}<.760 .
\]
The explicit final reserve includes both signed ordinary
errors in (3); all analytic remainders are \(o(M)\) in the
stated order of physical limits. No artificial sieve model
has replaced the remaining sharp, reflected signed scores.
