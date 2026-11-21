# Near-half rank-seven compensation with a genuine divisor-neck bound

This upgrades the matched physical comparison in
[FullFavorableRankSixAbsorption.md](FullFavorableRankSixAbsorption.md).
A different actual \(q\)-profile, now of rank seven, allows the
favorable rank-six true rows to be opened at an arbitrarily
near-half cutoff, instead of the low cutoff .199. All
polynomially rough squarefree even \(q\)-ranks in their
unmatched rows then lie in a narrow, genuinely priced divisor
neck; rank three has the favorable sign. Odd ranks at least
five outside the common profile remain unbounded.
This does not give aggregate positivity.

Use \(N=2x,L=\log x,n=sq\in(x/2,x]\) and \(m=N-n\) on their
actual unit support. As before \(F(m)=C^\dagger(m)\) is the
original subpower half-switch coefficient of
[ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md), and
\(W_s(q)=(1-t)(1-2t)^2,\ t=\log s/\log n\).
Fix \(0<\tau\le10^{-4}\), set \(\eta=.001\tau,\ \rho=\eta/10^5\),
and give every label an exponent band of radius \(\rho\).

## 1. The actual exponent profile and whole exchanges

Use the eight true independent prime labels
\[
 Q:\quad n=s_1s_2s_3s_4 R_1R_2R_3R_4
\]
whose center vector is \(v(\tau)=(1-\tau)v^0+\tau v^1\), with
\[
\begin{split}
 v^0&=(.139,.139,.139,.139,.0135,.0525,.1000,.2780),\\
 v^1&=(.139,.1347,.1381,.1385,.0220,.0591,.1015,.2671).
\end{split}
\]
All center sums are exactly 1. The four \(s_i\) are legitimate
true short markers with disjoint bands for every fixed
\(\tau>0\); the other four bands are also pairwise disjoint and
disjoint from them. The coincidences at \(v^0\) are only
formal endpoint data, not labels on a physical row.
On \(Q\) write \(q_i=n/s_i\) and \(W_i=W_{s_i}(q_i)\).
Since \(s_2,s_3,s_4<s_1\), we have \(W_i\ge W_1>0\).

The initial true rows are:
* \(T_2\), with \(s\) in band 1, \(q\) prime, and \(m=p h\)
  with genuine primes \(p,h\) and \(p\) centered at \(.4305-\eta\).
* \(T_{6,i}\), \(i=2,3,4\), with \(s\) in band \(i\), \(q\)
  prime, and \(m=pG,\ G=A_1 A_2 A_3 D E\) entirely of true primes,
  with \(p\) in the same fixed band and the five labels of \(G\)
  centered at \((.0335,.034,.0345,.073,.3945+\eta)\).

These are disjoint **original** rows, all with their original
weights \(W_s(q)F(m)\). No marker from another row is required
to occur in the original true \(q\). On \(T_2\) use the old
balanced \(q\) exchange from
[BalancedSemiprimeEvenRankNeck.md](BalancedSemiprimeEvenRankNeck.md):
\(c_s=(1-\log_xs)/2\), \(U_q=x^{c_s-4\eta}\),
\(V_q=x^\eta,\ B_q=x^{c_s+5\eta},\ Z=q/B_q\).
The balanced \(p\) admission has positive margin since
\(1.5\rho<\eta/1000\). This whole actual exchange is valid
before putting \(n\in Q\).

On the three whole rank-six rows use the simpler smooth
centering
\[
 C_{f_\tau}(q)=\Lambda(q)/\log q-
       \sum_{d\mid q}\mu(d)f_\tau(\log d/L)
\]
of [FavorableRankSixLeastPrimeDeletion.md](FavorableRankSixLeastPrimeDeletion.md).
Take \(f_\tau\) nonincreasing on the nonnegative axis, equal
to 1 through \(u_-=.4305-.0018\tau\) and 0 from
\(u_+=.4305-.0015\tau\), extended smoothly with compact support
on the negative axis. This is a fixed smooth function for each
chosen \(\tau>0\). The needed actual progression is
\(m\equiv N\bmod s a\) with \(a\le x^{u_+}\).
In [Lichtman Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5)
the independent short SW source is the actual \(p\),
the other source the independent product \(G\),
and modulus slots \((a,s,1)\).
The two tight rails have actual margins
\(\log_xp-u_+\ge .0005\tau-\rho\) and
\(1-2\log_xp-\log_xs\ge .002\tau-3\rho\).
The other two left sides are \(<1.775\) and \(<1.69\)
by the same earlier formulas; the residue is still \(N=2x\).
The grouped coefficient is 1-bounded by disjoint prime bands.
The exact principal \(1/\phi(sa)\) has the same \(Nsm\) mask
and negligible overlap \(s\mid a\). Each smooth cutoff layer
in \(a\) has log-small masked \(\mu/\phi\) mean, giving the
whole \(T_{6,i}\) exchange with \(O_{A,\tau}(xL^{-A})\) error.
The positivity formula for the original \(F\) weight is not
needed for this first harmonic transfer, but is checked below.
As in the earlier proofs, smooth physical log weights and the
central product use fine independent dyadic boxes; prime powers
in the initial \(\Lambda/\log\) are power-small.

## 2. Exact common-profile coefficients and the literal h expansion

Choose the common \(Q\) only **after** the above whole exchanges.
For its balanced \(T_2\) cutoff the two exponent thresholds
are \(.4305-.005\tau\) and \(.4305-.004\tau\)
up to \(O(\rho+1/L)\).
For the three compensating cuts their thresholds are
\(u_-\), \(u_+\) exactly. In all four rows no subset sum of
the seven \(q_i\) labels lies between the corresponding two
cutoffs, and the lower signed sums give coefficients
\[
              (-1,+2,+2,+2)
 \tag{1}
\]
in the four respective rows. The [exact rational checker](check_near_half_rank_seven.py)
enumerates only \(4\cdot2^7\) subset sums: at \(\tau=1\)
all signed comparisons have at least \(.0006\) endpoint
margin, and at \(\tau=0\) every side comparison has the
same weak sign relative to .4305. Affine interpolation
therefore gives at least \(.0006\tau\) reserve, which easily
absorbs the true label widths and central \(O(1/L)\).
This proves the profile assertion uniformly in its allowed
fixed-width boxes, not only at chosen formal centers.
For \(T_2\) the exact coefficient is minus the masked short
Möbius sum by (4) of
[FullFavorableRankSixAbsorption.md](FullFavorableRankSixAbsorption.md).
For the other three \(C_{f_\tau}\) it is also minus that
sum, since the smooth function is exactly 0 or 1 on
all those divisors. Here each \(q_i\) is composite
and all seven labels are distinct.

With the original \(F(m)=-2\log p\) on true \(T_2\), (1)
gives weight \(2 W_1(\log p)\Lambda(h)/\log h\) on its \(Q\)-part
after inserting \(\Lambda(h)/\log h\) for the true prime \(h\).
Proper \(h\)-powers have negligible mass.
Use the literal \(h\)-Vaughan cutoffs \(U_h=x^{.150},V_h=x^{.0003}\).
The actual two short terms are evaluated by the same true
rank-product Type I input as in the previous favorable-rank-six
note, but applied to the new eight independent labels above.
For completeness, write a digit 0/1/2 for the assigned
\(N/L/M\) slot in [Jain Proposition 3](https://arxiv.org/html/2611.21136v1#S3).
The source lengths are the specified grouped products;
their centers at \(\tau=0\) are in the middle column:
\[
\begin{array}{c|c|c}
\text{label assignment}&(u,\ell,b)\text{ at }\tau=0&\log_x(p e)\\\hline
(0,1,1,2,0,2,1,2)&(.1525,.378,.4695)&[.4990,.5301]\\
(0,1,1,1,2,2,2,2)&(.139,.417,.444)&[.5294,.5556]\\
(0,1,1,2,2,0,1,2)&(.1915,.378,.4305)&[.5360,.5691]\\
(0,1,1,2,1,0,1,2)&(.1915,.3915,.417)&[.5630,.5826]
\end{array}
\]
The checker verifies all (3.1) rails at both actual
\(\tau\)-endpoints and both modulus endpoints; the margins
are \(>.00035\), and positivity for their full intervals is
by affinity. Boxes and \(O(1/L)\) dyadic changes are absorbed.
Usual full-scale convolution BV joins below .4995, and
\(\log_x(p U_hV_h)<.581\). All grouped coefficients are
independent and 1-bounded by the disjoint label bands,
and low conductor characters are removed by SW in one
actual prime label. Thus their signed short harmonic center
is the literal principal (6) in
[SameEquationRankCompensation.md](SameEquationRankCompensation.md)
with factor 2 rather than 12, while the second short mean is zero.
This evaluation uses only actual central product progressions.

On the physical adverse chamber \(m=pG=N-n\), \(n\in Q\),
\(z=A_1A_2A_3D\) has exponent .175 and largest proper divisor
exponent .1415, so the high \(h\)-Vaughan term is
\({\cal H}(G)=+\log E\). At \(k=E\), the only \(d>U_h\)
is \(z\), of positive Möbius sign. At \(k\mid z\) the
remaining \(d\)'s are exactly \(E d'\), \(d'\mid z/k\),
and their Möbius sum vanishes.
On each of the **original** true rank-six rows,
\[
 F(pG)=4\bigl( (\log G-\log p)/2-\log(A_1A_2A_3)\bigr)
                         <-.121L.
\]
This is the genuine close-half divisor identity of
[FullFavorableRankSixAbsorption.md](FullFavorableRankSixAbsorption.md);
the largest tiny pair .0685 is below \(.0695+\eta\),
the tiny triple .102 and \(D=.073\) are above it,
and all cut and prime-power corrections vanish here.
On the **same physical equation** we may therefore combine
the high \(T_2\) contribution and the three opened rank-six
terms from their own initially disjoint true rows:
\[
 2 W_1\frac{\log p\log E}{\log G}
       +2F(pG)(W_2+W_3+W_4)
                           <-.125 L W_1.
 \tag{2}
\]
Indeed the first term is \(<.600L W_1\) and the
magnitude of the second is \(>.726L W_1\).
This is again full *local* absorption against true rows
whose original contribution is nonpositive. The two
disjoint actual prime-product families \(Q\) and \(pG\)
each have \(\gg_\tau X/\log X\) integers in the fixed
relative intervals in §4 of the first compensation note,
by ordinary PNT for the final prime and harmonic summation
for the others. Their prime bands are mutually disjoint.
Consequently (2) has genuine reference-scale mass at some
even target in each sufficiently large fixed-ratio interval,
by the same bounded-average singular-series argument.

## 3. The actual, unmatched near-half rows

For any composite squarefree \(q\) of even rank, the
complete Möbius sum below its half is exactly zero:
complement preserves the Möbius sign and the
complete sum is zero. Since in these three \(s\)-rows
\(u_+<\log_x(q)/2\) for all sufficiently large fixed \(\tau\)
(\(q\asymp x/s\)), the smooth coefficient therefore satisfies
\[
 |C_{f_\tau}(q)|
    \le \sum_{\substack{d\mid q\\u_-<\log_xd<\log_x(q)/2}}1 .
 \tag{3}
\]
Its actual divisor interval lies in a fixed exponent interval
of width at most \(.00396\tau\) for large \(x\), because the
largest marker deviation from .139 is \(.0043\tau\).
On \(P^-(q)>x^\delta\), every such pair \((d,q/d)\) is
eligible for the literal weighted hyperbola upper count in
[FavorableRankSixHyperbolaNeck.md](FavorableRankSixHyperbolaNeck.md).
Its proof counts all **splittings**, so it directly bounds
(3), with no extra divisor multiplicity.
The source profile of \(G\) has not changed, and all new
\(s\)-bands still satisfy \(\log_xs\le.139+\rho\);
the same uniform Weil reserve and local factors apply.
For every fixed \(\delta>0\) this costs
\(O_{\delta}((\tau+L^{-1})\mathfrak S(N)x/L)\) on the
actual even-rank rough complement, with a constant that
can be taken uniform in \(\tau\) in the stated range.
The squareful rough exceptions are power-small as in the
hyperbola note.

If \(q\) is squarefree of rank three with ordered prime
exponents \(a\le b\le c\), the short Möbius sum is
\[
 D_{f_\tau}(q)=1-f_\tau(a)-f_\tau(b)-f_\tau(c)+f_\tau(a+b)\le0 .
\]
The only possible short pair is \(a+b\), because the other
pairs are at or above the true half; the least factor has
\(f_\tau(a)=1\), and \(f_\tau(a+b)\le f_\tau(b)\).
Thus these terms are favorable against \(F(m)<0\).
True primes \(q\) have \(C_{f_\tau}=0\).
For the actual small-factor sector,
[FavorableRankSixMultiscaleCoreDeletion.md](FavorableRankSixMultiscaleCoreDeletion.md)
gives \(O_{\tau}(\delta\,\mathfrak S(N)x/L)+O_{A,\tau}(xL^{-A})\)
for each small \(\delta>0\), because each \(f_\tau\)
is a permitted fixed high smooth cutoff.

These statements do **not** give a bound uniform in a
joint limit \(\tau,\delta\to0\): the neck upper constant
depends on the roughness threshold, and the small-factor
constant depends on the smooth cutoff. They also do not
bound the polynomially rough odd ranks \(\ge5\) outside
\(Q\), the rest of the opened \(T_2\), or any other original
reflected profiles. The proven facts are the exact full
local match and the true geometric classification with a
uniform in \(N\) neck estimate, not an overall improvement
in the Goldbach threshold.

**Dated comparison.** [Arneth XII, September 28, 2026](https://zenodo.org/records/23016346) treats a different same-target compensation in a prime filter, while [Jain, November 16 v1](https://arxiv.org/abs/2611.21136) supplies the existing triple dispersion used here. This combined rank-seven shape and actual even-divisor-window bound use their stated scopes only; the rough odd signed terms are still open.
