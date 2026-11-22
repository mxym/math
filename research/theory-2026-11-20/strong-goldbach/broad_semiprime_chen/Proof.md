# A central semiprime source with a Chen-type partner

Let \(N\) be a prescribed sufficiently large even integer, \(L=\log N\),
and \(I=NI_0\) for a fixed nondegenerate interval \(I_0\subset[1/3,2/3]\).
Use the ordinary ordered Goldbach singular series \(\mathfrak S(N)\)
and put \(X_N=|I|\mathfrak S(N)/L^2\).
The source consists of genuine, distinct prime factors
\[
          y=uv\in I,\qquad N^{.27}\le u<v,\qquad (y,N)=1.
\]
Here and below all finite decimal exponents are exact rationals.
Let \(0\le w(u)\le1\) be any mask on the actual smaller primes, and
define
\[
 M_N(w)=\frac{L}{|I|}\sum_{y=uv\ {\rm in\ source}}w(u).
\]
Let \(R_N(w)\) be the sum of the same weights over source rows whose
actual partner \(m=N-y\) is squarefree, has all prime factors at least
\(N^{.1}\), and has at most two prime factors. In particular the source
has **exactly** two prime factors, whereas the partner is allowed to be
prime or a product of two distinct primes.

**Theorem.** Write \(\theta=.479\), \(\theta'=.499\), and
\[
 \begin{split}
 I_*&=\int_{1/10}^{1/3}\frac{\log(2-3t)}{t(1-t)}\,dt,\quad
 c_{\rm sw}=I_*/\theta',\\
 c_{\rm dir}
 &=10e^{-\gamma} f(10\theta)
       -5e^{-\gamma}\int_{1/10}^{1/3}
               F(10(\theta-t))\,\frac{dt}{t},
 \end{split}                                                         \tag{1}
\]
where \(f,F\) are the usual lower and upper dimension-one sieve
functions. Uniformly in the prescribed target and the mask,
\[
 \frac{R_N(w)}{X_N}
          \ge c_{\rm dir} M_N(w)-c_{\rm sw}-o(1).                      \tag{2}
\]
We have \(M_N(1)=\log(.73/.27)+o(1)\). The accompanying rational
calculation shows \(M_N(1)>.994+o(1)\),
\(0<c_{\rm sw}<1\), and \(c_{\rm dir}-c_{\rm sw}>.0335\).
Consequently \(R_N(1)>.027\,X_N\) for all sufficiently large
even \(N\). Further, let \(\mathcal U_N\) be the set of actual
smaller source primes that admit at least one such true partner.
Then
\[
     M_N(1_{\mathcal U_N})\ge
       \log(.73/.27)-c_{\rm sw}/c_{\rm dir}-o(1)>.027                 \tag{3}
\]
for large \(N\). In particular a positive proportion of genuine
source mass, measured on the smaller-prime labels, admits such a
partner; no assertion is made for every individual label.

This yields an all-target central alternative: either a prime plus
one of the specified \(N^{.27}\)-rough semiprimes, or a pair of actual
squarefree semiprimes, one in that same specified source. If the
first alternative is absent, the lower bound applies to the second.
Absence of binary Goldbach does **not** imply absence of the first
alternative, and neither a prime-partner lower bound nor two-prime
Goldbach follows here.

## 1. Actual source and its short-modulus distribution

Put \(a_w(y)=w(u)\) on the indicated source and zero otherwise,
and let \(T_w=\sum_y a_w(y)\). For every fixed \(A>0\), uniformly
over the allowed \(w\), we have
\[
 \sum_{\substack{b\le N^{.499}\\(b,N)=1}}
 \left|\sum_{y\equiv N\, (b)}a_w(y)
     -\frac1{\varphi(b)}\sum_{(y,b)=1}a_w(y)\right|
          \ll_{A,I_0} N L^{-A}.                                      \tag{4}
\]
Here \(u\) and \(v\) are actual primes. In (4) \(v\) is an independent
Siegel–Walfisz slot after a log-fine dissection.

Indeed split \(u,v\) into relative boxes of ratio \(1+L^{-B}\),
retaining interior boxes with the product in \(I\) and \(u<v\).
On each retained box the scales are \(M,T\) with \(MT\asymp N\),
\(T\gg\sqrt N\) and \(T\ll N^{.73}\). Target prime exclusions
are applied separately by each independent coefficient. Product
endpoint strips contain \(O(N L^{-B})\) ambiguous output integers.
For the ordering seam \(u,v\) must be \(\asymp\sqrt N\) and
within a factor \(1+O(L^{-B})\) of each other, giving
\(O(NL^{-B}+\sqrt N)\) pairs by integer counting. Each source
integer has at most one displayed ordering. The summed actual
modulus discrepancy on all seam rows is bounded by the sum of
\(\tau(N-y)\) over those rows, and the summed principal costs
at most \(O(L)\) per row. Cauchy with the ordinary second divisor
moment bound therefore makes the seam cost arbitrarily log-small
for sufficiently large \(B\). The number of boxes is only a
fixed power of \(L\).

In a retained box write \(\alpha(u)=w(u)1_{u\ {\rm prime}}\)
and \(\beta(v)=1_{v\ {\rm prime}}\), with the exact independent
interval and unit cuts. Apply character orthogonality, subtracting
the actual reduced-class principal. The longer true prime always
exceeds a modulus \(b\le N^{.499}\). The shorter prime can divide
\(b\), but \(b\) has at most one prime divisor at least \(N^{.27}\).
Thus for any induced nonprincipal character, replacing both
transforms by their primitive-conductor versions produces no
change in the long transform and changes the short transform
by at most one. Under character averaging this costs
\[
 \frac1{\varphi(b)}\sum_{\chi\bmod b}|\widehat\beta_b(\chi)|
       \ll T/\sqrt b+\sqrt T:
\]
the square mean counts pairs in the same reduced class, of which
there are \(O(T(1+T/b))\) even for all integers in the interval.
Summing to \(N^{.499}\), the total restoration cost per box is
\(O(TN^{.2495}+\sqrt T N^{.499})\ll N^{.9795}\) up to fixed
multiplicative constants. This is a power saving, not an assertion
that induced characters agree at shortened source primes dividing a
modulus.

For primitive conductors \(k\) induction costs at most
\(\sum_{b:\,k\mid b}1/\varphi(b)\ll L/\varphi(k)\), since
\(\varphi(ks)\ge\varphi(k)\varphi(s)\).
For \(1<k\le L^{C_1}\) use Siegel–Walfisz on the longer actual
prime slot with arbitrary log accuracy, uniformly on its interval
and with the prime divisors of \(N\) omitted. For dyadic \(k\asymp K\)
above that cutoff, Cauchy and the multiplicative large sieve give,
apart from fixed log powers,
\[
 \frac{\sqrt{MT}}K\sqrt{(M+K^2)(T+K^2)}
 \ll \frac{MT}K+\sqrt{M\cdot MT}+\sqrt{T\cdot MT}+K\sqrt{MT}.
\]
All terms other than the first save a fixed power, since \(K\le
N^{.499}\) and \(M,T\ll N^{.73}\). The first saves arbitrary logs
with the choice of \(C_1\). This proves (4). Fixed divisor-power
multiplicities can be inserted by Cauchy with a stronger log saving
in (4), the trivial individual discrepancy \(O(NL/b)\), and the
reciprocal divisor moments.

For \(w=1\), ordinary prime counting on \(I/u\) gives the source
mass, with \(|I|/(u(1-t)L)\) for \(t=\log u/L\).
Prime Mertens supplies \(\int_{.27}^{.5}dt/[t(1-t)]\).
For a rigorous endpoint passage, first take \(t\le .5-\epsilon\),
where \(v>u\) is automatic; the omitted absolute count is
\(O((\epsilon+o(1))|I|/L)\) by the same uniform PNT upper with
the ordering dropped. Let \(\epsilon\downarrow0\).
The excluded prime factors of \(N\) cost a power, and the
finite prime-square diagonal is omitted. This proves
\(M_N(1)=\log(.73/.27)+o(1)\) and in particular \(M_N(w)=O(1)\)
uniformly.

## 2. Direct lower/upper counts

Use \(Z=N^{1/10}\), \(Y=N^{1/3}\), \(D=N^\theta\).
Let \(T_0\) be the \(a_w\)-weighted \(Z\)-rough partner count.
Let \(T_1\) be its count weighted further by the number of distinct
prime factors \(u_1\in[Z,Y)\) of \(m\). Let \(T_2\) count the
actual triples
\[
       m=u_1u_2u_3,\qquad Z\le u_1<Y\le u_2<u_3
\]
on the original source, with the same \(a_w\). The classical
[Chen three-term switch](https://www.sciengine.com/doi/pdf/8663c8f4bb65481c80325a4101d215ac)
now gives the pointwise counting inequality
\[
       R_N(w)\ge T_0-\tfrac12T_1-\tfrac12T_2-o(X_N).                 \tag{5}
\]
To see it directly, first discard squareful \(Z\)-rough \(m\),
costing \(O(N/Z+\sqrt N)\) integers times at most a fixed divisor
power. For a squarefree \(m\) of rank at least three, \(m<N=Y^3\)
forces at least one prime below \(Y\). Two such factors remove
the row with the half-mark charges. If exactly one is below \(Y\)
then exactly two others are at least \(Y\), since three such
others already have product at least \(N\); \(T_2/2\) supplies
the second half-charge. On low rank the weight is at most one,
including exact endpoint equalities in the large factors.
This proves (5) for the weighted, already composite source
without modifying its multiplicity.

Apply lower linear sieve at \(D\) to \(T_0\). For \(T_1\), fix the
marked genuine \(u_1\), use upper linear sieve at \(D/u_1\), and
sum. The physical moduli are \(d\) or \(u_1d\), at most \(D\),
with \(d\) squarefree supported on primes below \(Z\). Here \(u_1\)
does not share any prime with \(d\). Target primes cannot divide
\(m\) on the unit source; omit them. The ordinary density for all
other primes is \(1/(p-1)\). For any given source \(y\), a model
exclusion \((y,b)>1\) is supported on \(b\) divisible by one of
its two primes at least \(N^{.27}\). Its summed absolute harmonic
cost even with the marked-modulus multiplicity is
\(O(L^C N^{-.27})\) per source. Thus the reduced model of (4)
can be replaced by the full source mass in these linear sieve sums.
The remainder is arbitrary-log small by (4) with the divisor
multiplicity, since a \(b\) has at most \(\tau(b)\) possible
marked choices.

The dimension-one product is
\[
 V_N(Z)=\prod_{\substack{p<Z\\p\nmid N}}
            (1-1/(p-1))
       =(1+o(1))\frac{e^{-\gamma}\mathfrak S(N)}{\log Z}.
\]
It follows by Mertens; the target-prime tail beyond \(Z\) contributes
\(O(L/Z)\) relatively. Omitting target primes preserves the
uniform upper dimension bound. The standard [linear sieve](https://doi.org/10.1090/coll/057)
applies uniformly at the fixed compact range of its \(s\) values
here. For the marked integral, prime Mertens gives \(dt/t\)
in \(t=\log u_1/L\); target-prime removals contribute \(O(L/Z)\).
Consequently
\[
 \frac{T_0}{X_N}\ge (10e^{-\gamma} f(10\theta)-o(1))M_N(w)-o(1),\qquad
 \frac{T_1}{2X_N}\le
    \left(5e^{-\gamma}\int_{.1}^{1/3}
           F(10(\theta-t))\,\frac{dt}{t}+o(1)\right) M_N(w)+o(1),          \tag{6}
\]
with additive \(o(1)\) allowed uniformly even for arbitrarily
small masks.

## 3. Switched triple upper count

After switching, retain the true prime-product \(m=u_1u_2u_3\)
inside \(N-I\), with the specified order and \((m,N)=1\).
An original \(y=N-m\) was an actual \(N^{.27}\)-rough semiprime,
with \(a_w(y)\le1\). Therefore it is allowed to **drop the entire
source condition and its mask in this upper bound** and retain
only the roughness \(P^-(y)\ge N^{.249}\). This implication uses
the actual least prime in \(y\) and carries no logarithmic
prime weight and no source-mass ratio. Once \(y\) is fixed the
original ordered source representation was unique.

For this true ordered triple source use
[Motohashi, Theorem 2](https://doi.org/10.3792/pja/1195518296)
for factor-log boxes (property (C), absolute maximal-prefix
Bombieri–Vinogradov to \(\sqrt N/L^{B_0}\)).
To apply it with the sharp absolute exponent cuts and \(m\in N-I\),
split the physical product into relative bins of width \(L^{-B}\)
and each factor's own-product-log exponent into bins of width
\(L^{-B-2}\). Within every retained cell these variables respect
the original endpoints and order up to \(1+O(L^{-B})\) factors.
The positive rough count permits taking a union of the retained
cells. The three roles are sorted; half-open bins and sorted
bin multisets count a source once even if two bins coincide.
A repeated prime is removed or costs \(O(N^{.9+o(1)})\), because
all prime factors exceed \(N^{.1}\). Boundary enlargement in
the ordinary triple main tends to zero by the PNT volume
calculation below. There are only a fixed power of \(L\) cells,
so choose the initial log accuracy in the cited result larger.
Target-prime divisibility may be removed by a power-saving
integer bound (each of the three factors has size at least
\(N^{.1}\)); if needed, its summed modulus cost is bounded by
a divisor power on the remaining integers. This keeps the
actual residue \(N\) reduced in the progression estimate.

Use the upper sieve on \(y=N-m\) at \(D'=N^{.499}\) and
\(Z'=N^{.249}\). The same local factors \(1/(p-1)\) apply for
\(p\nmid N\). Omitting \((m,d)>1\) from the reduced principal
changes the signed sieve sum by at most \(O(L^C N^{-.1})\) per
source, because each of the three source factors is polynomially
large. In particular one must not drop such restrictions
termwise inside a sum of signed sieve coefficients. All remaining
distribution errors are \(O_A(NL^{-A})\), since \(D'\) is strictly
subroot and the source boxes have the preceding property (C).
The ordinary sieve factor is
\[
 \left(\frac{2}{.499}+o(1)\right)
                         \frac{\mathfrak S(N)}{L},
\]
using \(F(s)=2e^\gamma/s\) for \(s=.499/.249<3\).
It multiplies the **triple-source count**, not the original
semiprime-source mass.

For that count the upper volume is \((I_*+o(1))|I|/L\). For a
fixed \(u_1,u_2\), the third prime is in \((N-I)/(u_1u_2)\);
dropping the order within this interval only improves the upper
count. The order has already forced
\(u_2\le\sqrt{(\sup(N-I))/(u_1)}\). The third-prime PNT on the
interval of fixed relative width is uniform; its log is
\((1-t-v+O(1/L))L\) where \(v=\log u_2/L\).
Consequently the angular domain is
\(.1\le t\le 1/3,\ 1/3\le v\le(1-t)/2\) up to vanishing
endpoint changes. Prime Mertens on this compact domain gives the
coefficient
\[
 \int_{.1}^{1/3}\frac{dt}{t}
       \int_{1/3}^{(1-t)/2}\frac{dv}{v(1-t-v)}
    =\int_{.1}^{1/3}\frac{\log(2-3t)}{t(1-t)}\,dt=I_*.
\]
In particular this ordered triple contains no extra factorial
or logarithmic normalization. Combining the last two estimates,
\[
                     \frac{T_2}{2X_N}\le I_*/.499+o(1).             \tag{7}
\]
Together (5)–(7) prove (2).

Finally, \(w=1\) gives
\[
 c_{\rm dir}M_N(1)-c_{\rm sw}
 = (c_{\rm dir}-c_{\rm sw})M_N(1)
         -c_{\rm sw}(1-M_N(1))
 \ge .0335\cdot .994-.006-o(1)>.027.
\]
The target-dependent mask \(w=1_{\mathcal U_N^c}\) is admissible
in (4) and has \(R_N(w)=0\). This gives
\(M_N(\mathcal U_N^c)\le c_{\rm sw}/c_{\rm dir}+o(1)\)
and proves (3) (indeed the lower margin is \(>.027\) as
\(c_{\rm sw}<1\) and \(c_{\rm dir}-c_{\rm sw}>.0335\)).

## 4. Numerical and literature scope

For the exact check, \(s_0=10\theta=4.79\).
The standard linear-sieve delay equations give
\[
 e^{-\gamma}F(v)=\frac2v\left(1+1_{v>3}
                        \int_2^{v-1}\frac{\log(w-1)}w\,dw\right)
 \quad(0<v\le4),
\]
and
\[
 e^{-\gamma}f(s_0)=\frac2{s_0}\left(\log(s_0-1)
        +\int_3^{s_0-1}\frac{dv}{v}\int_2^{v-1}
                         \frac{\log(w-1)}w\,dw\right).
\]
Substitute them in (1) and exchange the fixed finite integrals:
\[
 c_{\rm dir}
 =\frac{\log((s_0-1)(3\theta-1))}{\theta}
   -\frac1\theta\int_2^{s_0-2}
       \frac{\log(v-1)}v
       \log\frac{(v+1)(s_0-v-1)}{s_0-1}\,dv .
\]
For example the elementary marked integral is
\(\int_{.1}^{1/3}dt/[t(\theta-t)]\); for the remaining marked integral
at fixed inner \(v\) its range in \(t\) ends at
\(\theta-(v+1)/10\). This yields the displayed combination after
subtracting the double integral for \(f\).
The companion uses only directed rational logarithm enclosures
and one-sided rectangular sums; it runs unchanged with Python
optimizations.

This is a Chen upper switch with a different actual source,
not a new claim for the ordinary unforced \(P_2+P_2\) statement
following from \(p+P_2\). See also [Pintz's survey, §9](https://www.renyi.hu/~pintz/pjapr.pdf)
and [Goldston–Graham–Pintz–Yıldırım](https://arxiv.org/abs/math/0609615)
for exact products of two primes in bounded-gap problems; those
results are not used as pointed estimates at a prescribed sum.
The above-root very narrow semiprime source of the separate
signed giant comparison is not used here; this proof uses the
mass of the broad source and discards its shape only for the
independently upper-sieved triple in (7). No priority claim or
unproved prime-correlation hypothesis is required.
