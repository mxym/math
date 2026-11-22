# A signed rank balance against genuine two-tag rows of the wide no-high score

Use the original wide affine score of
[WideLowNoHighRemainder](WideLowNoHighRemainder.md) and
[WideNoHighTaggedPositive](WideNoHighTaggedPositive.md).
Thus \(N\) is an individual even target, \(L=\log N\),
\(J\Subset(0,1)\) is a fixed interval of positive length,
\(x+y=N\), \(x\in NJ\), and every pair keeps the actual
unit condition \((x,N)=1\). Write \(M=|J|N\mathfrak S(N)\)
and \(\langle V,W\rangle=\sum_{x\in NJ,(x,N)=1}V(x)W(y)\).
The same parameters are
\[
 \lambda=.006,\quad k=(1-\lambda)^{-1},\quad
 b=.490,\quad v=.498,\quad w=.499,\quad \rho=.518 .
\]
The fixed \(F(t)=(1+kt)C(t)\) is affine through \(.486\)
and zero from \(b\) onwards; \(0\le C\le1\).
In the physical score \(T=\mathcal L-B\), \(\mathcal L\)
uses the original true marks \(N^\lambda<r\le N^\rho\)
on \(\sum_{d\mid n/r}\mu(d)F(\log(dN/n)/L)\), with
weight \(\log r\). Its subscore \(B\) first restricts
\(r\le N^v\), then multiplies the term by
\(\chi(\log(rd)/L)\). The fixed smooth cap \(\chi\) is
one through \(.4985\), zero from \(w\) onwards, and
takes values in \([0,1]\). Neither \(F\) nor this
product cap is changed here. Define
\[
 H_\chi=.4985+\int_{.4985}^{.499}\chi(s)\,ds,\qquad
 \beta_\chi=1-k(H_\chi-v)>.9989 .
\]

On the first arm keep the actual integers \(x=q m\) with
\(q\) prime, \(\alpha=\log q/L\in I=[.5022,.5086]\),
and \(m\) squarefree with every prime factor exceeding \(N^a\),
where \(a=.014\). Put \(T_{\ge j}(x)=T(x)\) on this
chart with \(\omega(x)\ge j\) and zero otherwise.
Define \(T_3,T_4\) with the same chart and exactly that rank.
The genuine \(q\) is unique, \(q\) and \(m\) are coprime,
and all ranks of \(m\) in this chart are at most \(35\).
On the second arm let \(W(y)=\nu_1(y)\nu_2(y)\),
where \(\nu_i\) counts distinct true prime factors whose
target-log angles lie in the actual banks
\[
 I_1=[.00105,.00120],\qquad I_2=[.00140,.00160],
 \qquad V_i=\int_{I_i}\frac{dt}{t}=\log(8/7).
\]
In particular these two banks are disjoint from
every first-arm prime factor.

**Theorem.** Put \(s=1-\alpha,\ u=s/a\) in the integrals below,
and let \(\rho_{\rm D}\) be the Dickman function, normalized as
\(1\) on \([0,1]\) and \(u\rho_{\rm D}'(u)=-\rho_{\rm D}(u-1)\)
for \(u>1\). At every sufficiently large even \(N\),
\[
\begin{split}
 \frac{\langle T_{\ge3},WT\rangle}{M}
   &=\beta_\chi V_1V_2
       \int_I (1+ks)\frac{\rho_{\rm D}(u-1)-1}{s}\,d\alpha+o(1)
       <-.00032,\\
 \frac{\langle T_{\ge4},WT\rangle}{M}
   &=\beta_\chi V_1V_2
       \int_I (1+ks)\frac{\rho_{\rm D}(u-1)-1+\log(u-1)}s
                   \,d\alpha+o(1)
       >.00083,\\
 \frac{\langle T_3,WT\rangle}{M}
   &=-\beta_\chi V_1V_2
          \int_I(1+ks)\frac{\log(u-1)}s\,d\alpha+o(1)
       <-.00117 .
\end{split}                                                     \tag{1}
\]
Moreover \(\langle T_{\ge5},WT\rangle<-.00035M\).
These statements concern the same complete second-arm score with
its actual signs. The first line is the sum of the next two,
not another disjoint debit or reserve. The contribution from
ranks at least \(5\) is included in both of the first two lines.

If the banks are made sufficiently narrow around fixed interior
points of \(I_1,I_2\) before \(N\to\infty\), all four strict
signs persist, with possibly smaller constants, upon replacing
\(W(y)\) by the unweighted indicator of at least one prime in
each bank. These are true sectors of the original correlation:
\(T\) vanishes when a physical integer has a prime factor
\(>N^\rho\), and the first-arm chart cannot have the two small
tags. Thus they are disjoint in this orientation from the
two-arm tagged block. No bound on the complement or on
\(\langle T,T\rangle\) is asserted.

## 1. Exact score across all first-arm ranks

Every true mark other than \(q\) is at most \(m\le N^{.4978}\).
If a divisor in its score contains \(q\), the \(F\)-factor
vanishes. Otherwise its whole product \(rd\) divides \(m\)
and the cap equals one. Thus only \(q\) contributes to \(T(x)\).
For a proper divisor \(d\mid m\), its profile argument is
\[
        1-\alpha-\log(m/d)/L\le 1-.5022-.014=.4838 .
\]
This is in the affine part of \(F\), whereas the full divisor
\(d=m\) has argument \(1-\alpha\ge.4914>b\).
The full affine divisor sum is \(-k\Lambda(m)/L\)
for \(m>1\), by the elementary logarithmic Möbius identity.
When \(m\) is squarefree composite, it vanishes. Thus on
every chart row with \(\omega(x)\ge3\) the exact value is
\[
             T(x)=-L\alpha (1+k(1-\alpha))\mu(m).                \tag{2}
\]
There are no unpriced transition divisors on this chart and
no fixed-rank truncation beyond the actual roughness bound.
For any of the four rank selections in (1), its coefficient
in \(x=qm\) separates literally: the \(q\)-slot has a bounded
smooth multiple of \(\log q\) on its actual prime interval
and the \(m\)-slot has a bounded arithmetic coefficient.
The common spatial restriction is still \(x\in NJ\).

## 2. True tagged distribution, including the small over-root interval

Let \(Z\) be any one of \(T_{\ge3},T_{\ge4},T_{\ge5},T_3,T_4\).
Open the actual tags \(h=p_1p_2\mid y\) from the two
banks. They are disjoint from \(x\) and are target units
on every contributing row. If either selected prime has
valuation at least two in \(y\), pay those rows by the
actual multiples of squares of primes \(>N^{.00105}\).
That number is \(N^{1-.00105+o(1)}\); all original and
expanded row coefficients are bounded by fixed divisor
powers times log powers. No such square row affects the
claimed scale. On the tagged rows \(\Pi(y)=E(y)=0\) exactly.
Writing \(A=A_F\) for the genuine short log-minus-mark
weight of [the original decomposition](WideLowNoHighRemainder.md),
we therefore use \(T(y)=A(y)-B(y)\) up to its actual
proper prime-power exceptional support, also power-small.

On the remaining count write \(y=h n\) and each old divisor
\(d=c d'\) with \(c\mid h\), \((d',h)=1\).
For \(A\), the tags \(p_i<N^\lambda\) contribute nothing
to the braces after removal: each retained once-occurring
tag's free log is exactly canceled by its short mark.
The exact \(d'\)-profile is
\[
        F_h(t)=\sum_{c\mid h}\mu(c) F(t+\log c/L).
\]
The short prime-power labels \(j\le N^\lambda\) now
exclude \((j,h)>1\). Hence the true moduli are \(h d'\)
or \(h d'j\), all \(\le N^{.0028+.490+.006}=N^{.4988}\).
For \(B\), the original genuine mark \(r>N^\lambda\)
is different from the two tags, and the term with \(c\mid h\)
has
\[
   \mu(c) \mu(d')(\log r) F(t_{d'}(y)+\log c/L)
                             \chi(\log(rd')/L+\log c/L).
\]
Its actual modulus is \(h r d'\), at most \(N^{.5018}\).
The divisor \(c\) is a subset of the already present
tag modulus, not an additional multiplicative factor.
As usual extend these formulas to the paid square rows
with the displayed short-label masks retained; the same
positive divisor envelope pays the extension there.

We use the actual reduced product distribution of
[WholeMarkPrimeTransfer, §1](WholeMarkPrimeTransfer.md)
up to \(N^{.4996}\) for the source \(Z(x)\) in (2).
For the remaining interval \(N^{.4996}\) to \(N^{.5018}\)
use the literal Fouvry–Radziwiłł product discrepancy as in
[AsymmetricGiantMarkDispersion, §1](AsymmetricGiantMarkDispersion.md).
Indeed the longer slot is the true prime \(q\) with
its normalized smooth log weight; it has the auxiliary-mask
Siegel–Walfisz property of that proof, on every real
prefix in its polynomial dyad. The short coefficient
from \(m\) is bounded and need not satisfy such a property.
On all retained modulus dyads the strict rail margins are
\[
       (56\cdot.5086-17)/23=.4992<.4996,
       \qquad .5018<.5022 .
\]
The scale of \(q m\) is \(\asymp_J N\), the residue is
the literal \(N\), and all moduli used are coprime to \(N\).
The fixed aspect-ratio allowance for this residue is that
proved for the primary theorem in the cited transfer.
No small or varying representative of the class is used.
These inequalities leave a fixed power margin for its
two distributions throughout their respective ranges.

For clarity, these comparisons are used with the globally
summed actual moduli, rather than repeating an error bound
for every tag or mark. Each modulus has at most a fixed
divisor power of decompositions into the true factors
\(h,d',r\) or \(h,d',j\). Freeze real spatial arguments and
the independent product intervals by the log-fine meshes
of the cited proof. Crossed divisor moments for the
actual congruence \(q m+ y=N\), hence with these same
moduli dividing the actual \(y\), pay all the thin spatial
collars and approximation errors. The reduced model has
only the extra reciprocal totient harmonic. The modulus
divisor powers are absorbed by interpolation between an
arbitrary-log absolute discrepancy and the usual
\(NL^{O(1)}\) true-and-reduced divisor moment bound.
Thus we can use the genuine reduced principal with
\((q m,h d'j)=1\) or \((q m,h r d')=1\) exactly.
The later harmonic sum retains the actual mask \(Nx h\);
it does not treat the prime factors of \(x\) as an
independent sample from a progression.

## 3. Short harmonic with the actual cap derivative

Fix the actual \(x,y=N-x,h\) in the reduced model.
There is an outside \(1/\varphi(h)\).
The \(A\)-model is negligible: with
\(S=\exp((\log L)^4)\), the entire shifted \(F_h\)
is identically zero for \(d'\le S\), since there are
two affine shifts. Complete the signed \(d'\)-tails
against \(1/\varphi(d')\) at the actual polynomial
unit mask, by the uniform Mertens harmonic in the
cited one-mark transfer. Partial summation pays
its real spatial and free-log factors. If the short
prime power \(j=p^\ell\) shares a prime with \(d'\),
then relative to \(1/(\varphi(d')\varphi(j))\) the
correction is \(-1_{p\mid d'}/p\).
For \(p\le\sqrt S\), split \(d'=p d''\) and the
remaining signed tail starts at least at \(\sqrt S\).
For \(p>\sqrt S\) the extra reciprocal \(p\) gives
arbitrary-log absolute saving after the \(j\)-harmonic.
This verifies \(A\)'s tail with its actual
\(d'j\) modulus, not only the coprime one.

For the \(B\)-model, \(r\mid d'\) costs an extra
reciprocal prime power since \(r>N^\lambda\), so is
power-small in that model. The genuine \(r\mid Nx h\)
exclusions likewise cost a power at this scale.
We use the uniform zeroth and first log moments
\(0\) and \(-\mathfrak S(Nx h r)\) of
\(\mu(d')/\varphi(d')\) on the remaining mask, with
the true spatial factor kept before expansion.
At each fixed \(z=\log r/L\), \(v_c=\log c/L\),
the first-log coefficient on a \(B\) term is \(1/L\) times
\[
      k\chi(z+v_c)+(1+k v_c)\chi'(z+v_c)+O_J(1/L).
\]
Uniform completion at \(S\), then the same higher
short moment bounds as in the cited tag calculation,
makes the errors \(o(1)\) after the \(r\)-log harmonic.
Indeed the profiles and their shifts are fixed smooth,
with all seminorms bounded over the indicated compact
tag intervals. The local factor \(c(r)=1+O(1/r)\)
may be dropped after \(r>N^\lambda\).
The genuine prime log harmonic integrates \(z\)
on \((\lambda,v]\). For \(c=1\) its integrated
coefficient is \(k(v-\lambda)\). For every nonempty
shift, \(v_c>.001\), \(v+v_c>.499\),
and \(\lambda+v_c<.4985\); hence it is
\[
                 k(H_\chi-\lambda-v_c)-(1+k v_c).
\]
This is affine in \(v_c\), so the true second
difference, including the \(c=1\) term, is
\(k(v-\lambda)-[k(H_\chi-\lambda)-1]=\beta_\chi\).
The signed first log moment introduces a minus
on \(B\), so the surviving \(A-B\) principal
has the **positive** coefficient \(\beta_\chi\).

Each true tag \(p\mid h\) then contributes
\((p-2)^{-1}\): since \(p\nmid Nx\),
its factor in \(\mathfrak S(Nx h)\) relative to
\(\mathfrak S(Nx)\) is \((p-1)/(p-2)\), and the
outside totient contributes \(1/(p-1)\).
All first-arm factors are polynomially large in fixed
number, so \(\mathfrak S(Nx)=\mathfrak S(N)(1+o(1))\)
on actual units. The tag exclusions for \(p\mid N\)
are power-small in their reciprocal harmonic;
the factor \(p-2\) can be replaced by \(p\) with
power-small cost as well. Summing the two true
tag harmonics by PNT proves the exact signed transfer
\[
                 \langle Z,WT\rangle
     =\beta_\chi V_1 V_2\,\mathfrak S(N)
                  \sum_{\substack{x\in NJ\\(x,N)=1}} Z(x)+o(M).
                                                                    \tag{3}
\]
This is an estimate for all the actual rows of
the chosen \(Z\) and the true tag-weighted opponent, not
a signed independence assumption for two composite ranks.

## 4. The complete finite-rank signed angular sum

For \(u\ge1\) define \(I_1(u)=1/u\); for \(j\ge2\) use
\[
 I_j(u)=\frac1{j!}
     \int_{\substack{t_1,\ldots,t_j\ge1\\t_1+\cdots+t_j=u}}
       \frac{dt_1\cdots dt_{j-1}}{t_1\cdots t_j}.
\]
It is zero for \(u<j\), and \(I_1\) is zero for \(u<1\).
The measure is in the displayed coordinates with
\(t_j=u-t_1-\cdots-t_{j-1}\), not surface measure.
This is the ordinary density for unordered true prime
factors on the cofactor \(m\). Precisely, fixing
\(\omega(m)=j\ge2\), (2) has limiting unconditioned
normalized sum
\[
  \frac{\sum_{x\in NJ,(x,N)=1}T(x)1_{\rm chart,\ \omega(m)=j}}
              {|J|N}
  \ \longrightarrow\
     (-1)^{j+1}\int_I (1+ks)\frac{I_j(s/a)}a\,d\alpha .            \tag{4}
\]
One may obtain (4) by ordinary PNT in the last true prime
of \(m\), followed by prime reciprocal harmonics in the
other \(j-1\) primes and the actual \(q\).
The \(q\)-harmonic \(d\alpha/\alpha\) cancels the
factor \(\alpha\) in (2). Fixed angular boxes and
Jordan approximation of the ordered walls suffice.
All prime coordinates are bounded below by \(a\);
target primes and square/repeated labels have power-small
weights. The true log of \(x\) differs from \(L\) by
\(O_J(1)\), so angular walls can be enclosed by fixed
outward collars, shrinking them after the large-\(N\)
limit. The finite \(1/j!\) normalization instead of
an ordered region is valid by determinant-one
coordinate permutations. Finally, scaling all \(m\)
coordinates by \(a\) leaves the factor \(1/a\) in (4).

Symmetry and multiplication by \(u=\sum t_i\) give,
for \(j\ge2\),
\[
 u I_j(u)=\frac1{(j-1)!}
   \int_{\substack{t_i\ge1\ (i<j)\\\sum_{i<j}t_i\le u-1}}
                         \prod_{i<j}\frac{dt_i}{t_i}.
\]
Differentiate in \(u\) to get \((u I_j)'=I_{j-1}(u-1)\).
Thus \(D(u)=\sum_{j\ge1}(-1)^j I_j(u)\) is
\(\rho_{\rm D}'(u)\): integrate
\((uD)'=-D(u-1)\) from \(u=1\), using \(uD(1+)=-1\).
The sum is finite in the present fixed interval.
Also \(u I_2(u)=\log(u-1)\) for \(u\ge2\).
It follows that the \(j\ge2\) sum in (4) has
integrand \((1+ks)(\rho_{\rm D}(u-1)-1)/s\).
Deleting \(j=2\) adds \((1+ks)\log(u-1)/s\).
This proves the coefficients in (1), including all
the permitted real ranks of \(m\).

For strict numerical signs no approximation to the
Dickman function is needed. From
\(t\rho_{\rm D}(t)=\int_{t-1}^t\rho_{\rm D}(v)\,dv\)
one has \(0<\rho_{\rm D}(t)\le1/t\) for \(t\ge1\);
positivity follows by this integral identity and the
initial positive interval. Here
\(34.1\le u-1<34.56\),
so \(3.5<\log(u-1)<3.56\) and
\(0<\rho_{\rm D}(u-1)<.03\).
For the fourth-rank source, direct integration of the
three coordinates gives
\[
       u I_3(u)=\int_{1/u}^{1/3}
                \frac{\log((1-2z)/z)}{z(1-z)}\,dz .
\]
Restrict to \(z\le1/8\), use \(1-2z\ge3/4\)
and \((1-z)^{-1}\ge1\), and obtain
\[
     u I_3(u)\ge
       \tfrac12\{(\log(3u/4))^2-(\log 6)^2\}
       >\tfrac12(3.25^2-1.80^2)>3.66.
\]
Subtracting this \(j=3\) contribution from the
\(j\ge3\) sum for \(m\) leaves the ranks \(x\ge5\);
the resulting numerator is below \(3.56-.97-3.66=-1.07\).
In all bounds \(1+ks>1.49\), \(1/s>2\),
\(|I|=.0064\), \(V_i>.133\), \(\beta_\chi>.9989\).
The [rational check](check_wide_rank_tagged_cross.py)
verifies these strict bounds and all four final margins.
They absorb the \(o(M)\) errors.

## 5. Narrow actual banks without multiplicity

For the indicator version keep fixed distinct interior
bank centers and let \(V_i\) be sufficiently small fixed
positive reciprocal widths. The proof above and (3) still
hold, with \(V_i\) the actual bank integrals; the size
margins and the cap derivative computation do not change.
For nonnegative integers \(\nu_i\),
\[
 0\le \nu_1\nu_2-1_{\nu_1,\nu_2\ge1}
       \le \binom{\nu_1}{2}\nu_2+\nu_1\binom{\nu_2}{2}.
\]
This uses three actual distinct tags on the second arm.
For any such \(h=p_1p_2p_3\) and a fixed actual \(m\)
on the source chart, impose the real progression
\(q=q_0+h t\), \(q_0m\equiv N\bmod h\).
Then \(y/h=(N-mq_0)/h-mt\) and \(q_0+ht\)
are primitive affine forms with determinant of absolute
value \(N\). Enlarge only this positive bound to the full spatial
interval \(x\in NJ\). Its parameter length is then
\(\asymp_J N/(m h)\), at least a fixed power of \(N\), since
\(m\le N^{.4978}\) and the three tags have total
exponent below \(.0048\). On the first form use the
\(N^{.01}\)-rough upper for the true prime \(q\).
On the second use the smooth-cap Fourier envelope of
[WideNoHighPrimeRankPressure, §3](WideNoHighPrimeRankPressure.md).
The corrected Henriot estimate there is valid with these
coefficients: the root at 2 is single, target primes
have their nonunit roots excluded, and a prime of
\(mh\) changes two distinct roots to a single one.
At a tag, extract its actual weight once at all
valuations and use \(w_t(p)\le3\). All extra local
factors are uniformly bounded since \(m,h\) have
fixed numbers of polynomial prime factors.
Restoring the Fourier moments bounds the genuine
weighted sum at fixed \(m,h\) by
\(O_{F,\chi,J,a}(M/(m h))\); its two genuine exterior
log weights cancel the two sieve logarithms.
Sum \(1/m\) over the actual source products, bounded
in terms of \(a\) since each factor is \(>N^a\)
and there are at most \(35\).
The total absolute excess is
\(O_{F,\chi,J,a}(V_1V_2(V_1+V_2)M)+o(M)\)
by the actual three-tag harmonic. Take the widths
small enough compared with the nonzero fixed signed
coefficients per \(V_1V_2\) in (1) and the
rank-at-least-five bound, and thereafter take \(N\)
large. This proves all the stated signs for the
literal unweighted cohorts, without deleting an
unpriced signed part of those cohorts.
