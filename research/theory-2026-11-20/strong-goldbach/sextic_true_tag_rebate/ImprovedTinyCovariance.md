# A smaller signed debit for the same .003 sextic cutoff

Keep **exactly** the sharp sextic \(H\), \(Q\), \(G=H+Q\), target
units, spatial interval and \(M\) of the [.003 tradeoff](ExplicitTinyStopTradeoff.md).
In particular \(b=.003\), \(I=1_{P^-\le N^b}\), \(T=IG=IH\).
Keep the original stopped part \(A\), the actual least-certificate
remainder \(V\), and the taper defect \(D\) of
[the explicit proof](ExplicitTinyStop.md) at the .003 parameters
\[
       c=.0135,\qquad d=.013501,\qquad w_{\rm taper}=.018 .
\]
The actual tapered profile \(F_*\) is supported up to \(.486499\)
and agrees with the original polynomial near zero. None of these
terms or the compensated score is redefined.

**Theorem.** On the same true union where either coordinate has a
factor at most \(N^{.003}\), the signed debit is \(<.1332M+o(M)\)
in place of the preceding \(.278M+o(M)\). Accordingly
\[
             R_J\ge .8208M+
                 \langle(1-I)G,(1-I)G\rangle+o(M).
\]
This replaces .676 by .8208 for the **identical** retained score.
Any subsequent comparison obtained from that .676 by unchanged
estimates and unchanged disjoint physical chambers gains .1448
in its coefficient. This is not a new chamber and does not bound
the final exterior covariance.

## 1. A surrogate which only scales literal \(V\) values

As in the original proof, fix \(0<a<b\) first, use the actual
bank \(\mathcal P=(N^a,N^b]\) of primes, and take \(a\downarrow0\)
after the fixed-cutoff estimates. For the moment \(V_a\) is
the bank-version of \(V\), without imposing global \(a\)-roughness.
Write \(u_p=\log p/L\) and
\[
                B(n)=\sum_{\substack{p\in\mathcal P\\p\mid n}}u_p .
\]
The subset cancellation in the original identity (1) works for
**any** distinguished actual \(p_0\in\mathcal P\) dividing \(n\):
pair each subset of the other labels with its union with \(p_0\).
The resulting difference from the stopped sum is independent of
which \(p_0\) was distinguished. Thus, by multiplying each of
these equal versions by its \(u_{p_0}\) and summing, \(B(n)V_a(n)\)
equals \(H_*(n)\) times the true signed sum of the named certificates
\[
 c-u_{p_0}<\sum_{p\in J'}u_p\le c,\qquad
 h=p_0\prod_{p\in J'}p\mid n,\qquad
 p_0\notin J',
\]
weighted by \(u_{p_0}(-1)^{|J'|}\). There is **no** least-factor
restriction in this new expansion. Every \(h\) is squarefree,
has at least five distinct bank primes, and has angle in
\((c,c+b]\). On the nonzero support of \(V_a\) necessarily
\(c<B(n)\le1\).

Put \(w=.070\) (not the taper width), and use the Chebyshev polynomial
\[
 T_5(z)=16z^5-20z^3+5z,\quad
 z(B)=\frac{w+c-2B}{w-c},\quad T_0=T_5(z(0)),\quad
 K(B)=1-\frac{1+T_5(z(B))}{1+T_0}.
\]
As \(K(0)=0\), \(P(B)=K(B)/B\) is a polynomial of degree at most four.
For \(c\le B\le w\),
\[
               \lambda=\frac{T_0-1}{T_0+1}\le K(B)\le1 .
                                                                    \tag{1}
\]
Let \(V_{P,a}=K(B)V_a\), a literal rowwise scaling.
Open \(P(B)\) in the preceding signed expression for \(BV_a\).
Each monomial opens at most four extra true bank labels, allowing
repetition, and restricts \(n\) by the product of the **distinct**
labels in the union. The true opened \(h\)-product is therefore at most
\(N^{c+b+4b}=N^{.0285}\); repeated labels only affect the coefficient.
Because all marks are actual divisors and lie far below \(n\),
on their support \(H_*\) has no prime subtraction.

## 2. The actual symmetric calibration of the surrogate

Open squarefreeness on both physical arms by
\(\mu^2(n)=\sum_{s^2\mid n}\mu(s)\). At fixed \(a\) use
\(s\le N^{\epsilon_s}\) with
\(\epsilon_s=\min(a/4,10^{-7})\). The omitted actual square multiples
have total weight \(O(N^{1-\epsilon_s+o(1)})\) by the true divisor
envelope and \(\sum_{s>N^{\epsilon_s}}(N/s^2+1)\) up to \(\sqrt N\).
The joined modulus \(q=[h,j,s^2]\), for \(j\) the actual profile
divisor, satisfies
\[
                       q\le N^{.5149992}.
\]
The same holds on the other side. Group all opened coefficients by
these literal moduli. Their multiplicities and weights are bounded
by fixed divisor powers (and log powers). This grouping includes
coincidence of a profile divisor prime with a named label and
coincidence of two of the extra names.

For the physical sum use smooth log-fine spatial cells to freeze
only the denominators of the log-angle profiles in \(x,y\).
The original fixed sharp endpoints, real own logs, and model
restoration are justified by the elementary crossed divisor moments,
as in [the native tagged calibration, §2](../divisor_hyperbola/TaggedNativeSecondMoment.md).
Open the true target units via \(u\mid(x,N)\), cutting at
\(u\le N^{10^{-7}}\) by the same physical floor and reciprocal
tail. At \(X=N/u\) the grouped compatible progression gives
the usual coprime reciprocal Poisson phase. Applying the
[actual Bettin--Chandee comparison](../nearfull_high_vaughan/JointGiantActualMarkBlock.md)
with the two **grouped** coefficient sequences gives a power saving:
for the modulus dyads let \(g=\log_X(QR)\),
\(m_0=\log_X\max(Q,R)\). When \(g<.99\) simple floors suffice;
otherwise \(g<1.030000\), \(m_0<.515000\). The two exponent bounds
for \(g\ge1\) are
\[
      .7g+.25m_0-.85\le-.00025,\qquad
      .875g+.125m_0-1\le-.034375 .
\]
For \(.99\le g<1\) the bounds
\(.5-.65g+.25m_0\) and \(.5-.625g+.125m_0\) also have strict room.
One may first cut the nonzero frequencies at
\(X^\rho(1+QR/X)\) with a sufficiently small fixed \(\rho>0\),
then separate the smooth factor by Mellin on each signed frequency
dyad. Extra losses can be chosen below the displayed power margins.
No count of the mark or square labels is added to those exponents.

Here is the exact zero-mode analysis. At fixed literal disjoint
named products \(h,h'\), with \((hh',N)=1\), write a profile divisor
as \(f j\), \(f\mid h\), \((j,h)=1\), and analogously on the other
arm. Since \(s<N^a\), its primes do not meet \(h\). The source-side
opened modulus is \(h[j,s^2]\), independent of \(f\). Summing \(f\)
replaces the profile by the finite difference
\[
          G_h(t;x)=\sum_{f\mid h}\mu(f)
                         F_*(t+\log f/\log x).
\]
All compatibility conditions in the free quotient model are
retained: \(j,s\) and the corresponding other pair are units
at \(B_0=Nhh'\), and the two free moduli are coprime.
The square labels may now be completed to infinity at power saving,
using the absolute \(\tau(s)L/s^2\) harmonic. The exact Dirichlet
series of the free **bilateral** model has at \(p\nmid B_0\)
the factor
\[
         1-2p^{-2}-(p^{-1}-p^{-2})(p^{-z}+p^{-z'}),
\]
and at \(p\mid B_0\) the factor 1. In particular division by
\(\zeta(1+z)^{-1}\zeta(1+z')^{-1}\) leaves an Euler product
\(\mathcal K_{B_0}(z,z')\) whose two-variable absolute coefficient
norm at \(\Re z=\Re z'=-1/\log L\) is \(O((\log L)^C)\).
Indeed the unrestricted local factors differ from 1 by
\(O(p^{-2+2/\log L})\); split the missing factors at \(L^2\)
and use \(\omega(B_0)=O(L)\). Convolution with the two
\(\mu(j)/j\) harmonics, Rankin truncation at
\(\exp((\log L)^4)\), and ordinary signed Mertens in each coordinate
give the first-derivative product
\[
 \frac{\varphi(N)}N\,
          G_h'(0;x)G_{h'}'(0;y)\mathcal K_{B_0}(0,0)
\]
after the two outer logs. One can truncate the two signed variables
successively; the other absolute harmonic costs only log powers.
The constants vanish by the two signed zeroth moments, and the
mixed Taylor error is \(O_a((\log L)^C/L)\). All weighted outer
label harmonics are \(O_a(1)\), since their primes lie in a fixed
positive-floor bank and their total angles are bounded.
The restored target factors satisfy
\[
 \frac{\varphi(N)}N\mathcal K_{B_0}(0,0)
      =\mathfrak S(N)\prod_{p\mid hh'}(1-2/p)^{-1}
      =(1+o_a(1))\mathfrak S(N).
\]
One can extend the principal to independent named products with
\(o_a(M)\) error, because overlapping actual bank primes acquire
a squared reciprocal harmonic. This does not remove any
physical coprimality requirement in the true sum.

All shifts in \(G_h\) at zero are in the unchanged polynomial
part of \(F_*\); \(F_*'\) has degree five there. Thus any named
set with more than five distinct labels gives a zero derivative.
A surviving named set has exactly five original certificate
labels and all extra labels must repeat those original labels.
Consequently their aggregate factor is **exactly**
\(P(\sum_{p\mid h}u_p)\) times the signed sum of \(u_{p_0}\)
over the eligible choices in the set. Its absolute value is
at most \(K(\sum_{p\mid h}u_p)\le1\) by (1):
its angle lies in \((c,c+b]\subset[c,w]\).
The fifth difference of \(F_*'\) has absolute value
\(80640\prod_{p\mid h}\log p/\log n\).
The true unordered prime harmonic, with these five angle
weights, bounds each surviving one-arm principal by
\(80640 b^5/5!+o_a(1)=672b^5+o_a(1)\).
It follows that
\[
             |\langle V_{P,a}, V_{P,a}\rangle|
                    \le (672b^5)^2 M+o_a(M).                     \tag{2}
\]
The bank floor can be removed in the prescribed order. In
particular, discarding rows with a prime at most \(N^a\) when
using the least-certificate version costs \(o_{a\downarrow0}(M)\)
after the large-target limit, by the original physical phase
envelopes. Multiplication by \(K(B)\), bounded on \([0,1]\)
independently of \(a,N\), does not change that limit.

## 3. A true paired cost for the large-\(B\) exception

Retain \(X,Y\) and the actual global least certificates of the
[original absolute bound, §3](ExplicitTinyStop.md#3-an-effective-actual-bound-on-the-two-stopped-remainders)
after the preceding floor limit. Thus
\[
 X=(H_*/L)^2\sum_{\rm cert}\beta^{-1},\qquad
 Y=\sum_{\rm cert}\beta,\qquad
 U_0=.8/b,\qquad
        m(LX)\le B_X^2,\quad B_X<.017667 .
\]
The true receiver \(LY\) has upper \(U_0m(Z)\) against every
applicable nonnegative compact product source \(Z\).
No independence is assumed for the two integer coordinates.

For \(B\ge w\) there is a monotone upper
\[
 |K(B)|\le C_0(B/w)^5,\qquad
 C_0=1+\frac{(4w/(w-c))^5+1}{1+T_0}.
\]
Indeed \(|z(B)|\le2B/(w-c)\), and for \(|z|\ge1\),
\(|T_5(z)|\le(2|z|)^5\).
Put \(G_0=1+C_0^2\) and \(\mathcal L(B)=G_0(B/w)^{10}1_{B>w}\).
For a pair outside the good square \(B(x),B(y)\in[c,w]\),
assign the error to a larger \(B\) coordinate:
\(|1-K(B(x))K(B(y))|\) is at most
\(\mathcal L(B(x))+\mathcal L(B(y))\) on the nonzero \(V\)-pair.
On the good square, it is at most \(1-\lambda^2\).
These are pointwise bounds for both signs of the true product.

The needed extension of the ordinary and receiver upper uses
**actual extra small factors**, as follows. Set \(k=14\),
\(R_0=(w-c-b)/b=107/6\), \(v_0=1-c-b\), \(v_1=v_0-kb\),
and let \((R_0)_k=\prod_{j=0}^{k-1}(R_0-j)\).
At any particular original certificate \(h\), remove its names
from the bank factors of \(n\). Their remaining normalized
angles \(u_p/b\) are in \([0,1]\) and have sum
\(R\ge(B-c-b)/b\). For any numbers in \([0,1]\) of sum \(R>k-1\),
the unordered \(k\)-fold elementary symmetric sum is at least
\((R)_k/k!\): in each successive ordered choice, at most one
unit of mass was removed at each earlier choice. For \(B>w\)
each factor \(R-j\) is at least \((R_0-j)(B/w)\);
since \(k\ge10\), this gives the exact pointwise upper
\[
 \mathcal L(B)
 \le \frac{G_0 k!}{(R_0)_k}
    \sum_{\substack{J''\subset(\mathcal P\cap\{p:p\mid n\})\setminus h\\
                    |J''|=k}}\ \prod_{p\in J''}\frac{u_p}{b}.       \tag{3}
\]
On the good region the left side of (3) is simply zero.
All extra labels are genuine distinct primes; their product with
the first certificate has angle at most \(c+b+kb=.0585\).
The original least \(p_0\) remains the true least, with all extra
named primes at least \(p_0\).

In the true \(LY\mathcal L\) receiver, expand (3) in each named
certificate, then use the original least-factor upper proof with
the **whole** named product. The remaining level exponent is at
least \(.499-.0585=.4405>3b\); the actual coprime small sieve and
all original source/target unit factors are retained. The extra
prime harmonic with weights \(u_p/b\) costs at most \(1/k!+o_a(1)\)
by the true log-prime harmonic and the unordered distinct labels
(dropping the exclusion of previous names only in the upper).
Thus the new genuine receiver upper is
\[
           U_{\rm hi}=U_0\,G_0/(R_0)_k .
\]
In the **ordinary** \(LX\mathcal L\) bound use the same positive
squared-phase measure and Minkowski as in the original \(B_X\)
estimate. Each of the extra labels contributes one \(u_p/b\) and
one \(A_\xi(u_p)^2\le4\), so their true reciprocal harmonic costs
at most \(4^k/k!\). The free complement density uses
\(v\ge v_1\) instead of \(v\ge v_0\). All old certificate weights,
including the least \(\beta^{-1}\), are unchanged. Thus
\[
         m(LX\mathcal L)
           \le B_X^2\,\frac{G_0 4^k}{(R_0)_k}\frac{v_0}{v_1}.
\]
These are genuine bounds after the original compact floor
limits; (3) introduces only fixed extra multiplicity, and its
angle weights and the squared-phase bound make the same
positive integral converge. The actual high weight
\(\mathcal L(B)\) itself is bounded by a fixed constant on
\([0,1]\). Applying the original pairwise AM--GM certificate
inequality to the two high orientations shows
\[
 \begin{split}
  \langle V,V\rangle/M
   &\le (672b^5)^2+
      [1-\lambda^2+\rho_{\rm hi}]\, U_0 B_X^2+o(1),\\
  \rho_{\rm hi}
   &=\frac{G_0}{(R_0)_k}
                  \left(1+4^k\frac{v_0}{v_1}\right).
 \end{split}                                                       \tag{4}
\]
Indeed each orientation contributes at most
\((U_0m(LX\mathcal L)+U_{\rm hi}m(LX))/2\); these two halves
give exactly the single displayed factor \(\rho_{\rm hi}\).
The old actual signed configurations outside the good part
have been charged, not assumed to have the surrogate's sign.

## 4. Replacement in the identical signed ledger

The signed formula for the true tiny union has \(+\langle T,T\rangle\)
in its **debit**, and its identity (4) in the original proof leaves
\(\langle V,V\rangle\) plus the three defect terms bounded there.
Use (4) above in place of \((.8/b)B_X^2\).
There is also a one-sided improvement on the two single-tiny
terms; do **not** charge the full absolute score there.

Indeed, keep the original \(R=T-A=V+E-D\), and set \(Z=V-D\).
In the original single-tiny identity, the two true \(E\) crosses
with \(\Pi,Q\) are \(o(M)\), and \(m(E)=0\). Thus the term which
can increase the debit in a single orientation is
\[
        \langle Z,\Pi\rangle-\langle Z,Q\rangle
        \le \langle Z_+,\Pi\rangle+\langle Z_-,Q\rangle ,
\]
using the actual \(\Pi,Q\ge0\). The genuine \(3.446\) and
\(.852\) receivers from the original proof apply respectively
to the two nonnegative sources \(Z_+\) and \(Z_-\) on the
same compact angle and rank limits. Write \(Z_-=[-Z]_+\).
Since \(m(Z)=m(R)\), \(|m(R)|<10^{-7}\), and
\(m(|Z|)\le B_V+B_D\), the exact one-arm identities
\(2m(Z_\pm)=m(|Z|)\pm m(R)\) give the upper
\[
       \frac{4.298(B_V+B_D)+2.594\cdot 10^{-7}}{2}
\]
at scale \(M\) in each orientation. This relies on the actual
signed ordinary mass, not a claimed balance of prime-adjacent
parities. The physical signs of the prime and rough crosses
have not been interchanged.

All other bounds remain unchanged:
\(|c_A|<.228,\ |m_T|<.227\),
\(B_D<.006657,\ U_D<.007445,\ B_V<.009042\),
and the same original ordinary \(Q\) upper \(m(Q)<.01701\).
The new strict full debit coefficient is therefore bounded by
\[
 \begin{split}
   2(.228)(.01701)+(.227)^2
   +4.298(B_D+B_V)+2.594\cdot 10^{-7}
   +(B_D+2B_V)U_D+10^{-4}\\
   {}+(672 b^5)^2+[1-\lambda^2+\rho_{\rm hi}](.8/b)B_X^2 .
 \end{split}
\]
The [rational check](check_improved_tiny_covariance_v2.py) gives an
upper \(<.133141<.1332\). It uses the already-certified original
.003 constants and no new angular numerical integration.
The .954 starting comparison and every subsequent unchanged
outside-chamber term keep their original physical meanings.
