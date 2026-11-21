# Complete near-half orientation rigidity on the actual reflected rank-six rows

This addresses the full set of physical short-prime orientations
in the unmatched rows of
[NearHalfRankSevenCompensation.md](NearHalfRankSevenCompensation.md),
rather than a different prime-detection identity. Swapping an
actual short marker can change a near-half center only on a
physical divisor neck. There are explicitly populated rank-five
quotient families on which **every** eligible original orientation
reinforces the adverse sign.

Put \(N=2x,L=\log x\), \(n=sq\in(x/2,x]\), \(m=N-n=pG\)
on the actual favorable rank-six reflected profile above, with
\((n,N)=1\), \(F(m)=C^\dagger(m)<0\), and the exact
\(W_s(q)=(1-t)(1-2t)^2\), \(t=\log s/\log n\).
Let \(J(n)\) be the set of all allowed true prime factors \(s\mid n\)
for the given union of short-marker bands. Assume these
bands lie in a log-exponent interval of span \(\omega\)
and in the length conditions of
[FavorableRankSixHyperbolaNeck.md](FavorableRankSixHyperbolaNeck.md).
In particular this applies to the three original favorable rows
\(T_{6,2},T_{6,3},T_{6,4}\) of the above near-half result.
On each of those opened rows keep its own allowed smooth
center \(C_{f_s}(q_s)=\Lambda(q_s)/\log q_s-D_{f_s}(q_s)\),
where \(q_s=n/s\) and \(D_{f_s}(q_s)=\sum_{d\mid q_s}
\mu(d)f_s(\log d/L)\). It suffices below that \(0\le f_s\le1\)
on the nonnegative line and its possible distance from
the exact half indicator is localized:
\[
 f_s(t)=1\quad(t<\log_x(q_s)/2-\kappa),\qquad
 f_s(t)=0\quad(t>\log_x(q_s)/2+\kappa).
 \tag{1}
\]
The original \(f_\tau\) of those three rows satisfies this
for \(\kappa\ll\tau+1/L\).
The result is about these already transferred rows; it does
not introduce a \(q\)-factorization restriction before their
original whole exchanges.

## 1. Exact bijection and uniform physical neck error

Fix a squarefree physical \(n\), with at least two distinct
allowed markers \(s,t\), and write \(n=s t u\).
There is a genuine bijection
\[
 d=e t^\varepsilon\ \longmapsto\ d'=e s^\varepsilon,
 \qquad e\mid u,\quad\varepsilon\in\{0,1\},
\]
between the divisors of \(q_s=t u\) and those of \(q_t=s u\).
It preserves the Möbius signs. More exactly its relative
displacement from the two own halves is
\[
 \log(d'/\sqrt{q_t})-\log(d/\sqrt{q_s})
        =(\varepsilon-\tfrac12)\log(s/t) .
 \tag{2}
\]
Thus \(|\log(d'/\sqrt{q_t})-\log(d/\sqrt{q_s})|
\le\omega L/2\). If \(d\) is outside the band of width
\(\kappa+\omega/2\) on either side of its own half, both
coefficients in (1) coincide with the same 0 or 1.
No rank hypothesis is needed for this displacement formula.

For any canonical choice \(s_*(n)\in J(n)\), define the canonical
half sum
\[
               S_*(n)=\sum_{d\mid q_{s_*},\ d<\sqrt{q_{s_*}}}\mu(d).
\]
Use the divisor bijection independently from each \(s\) to
\(s_*\); the **canonical exact indicator** need not have any
smoothing. On the composite squarefree \(q_s\)-support,
\(\Lambda(q_s)=0\). Therefore
\[
 \sum_{s\in J(n)}W_s(q_s)C_{f_s}(q_s)
  =-S_*(n)\sum_{s\in J(n)}W_s(q_s)+{\cal E}(n),
 \tag{3}
\]
where
\[
 |{\cal E}(n)|\le
 \sum_{s\in J(n)} W_s(q_s)
       \#\{d\mid q_s:
            |\log_x d-\log_x(q_s)/2|\le\kappa+\omega/2\}.
 \tag{4}
\]
This bound continues to count no term when just one marker
is present and its smoothing is exact on the actual divisors.
In particular, when the displayed neck is empty,
the orientations have the same exact coefficient, regardless
of how they choose their individual smooth transitions.
The normalized half moves only by \(O(1/L)\) inside a central
dyad, and the span of the marker band is \(\omega\).

On the polynomially rough portion \(P^-(q_s)>x^\delta\)
for fixed \(\delta>0\), the bound in (4) has actual weighted sum
\[
 \sum_{\text{actual } n,m}|F(m)|\,|{\cal E}(n)|
   \ll_{\delta}(\kappa+\omega+1/L)\,\mathfrak S(N)x/L.
 \tag{5}
\]
Indeed the proof of the literal hyperbola estimate counts all
proper divisor splittings, not just the existence of one.
Apply it to each term of (4) with its true \(s\) and the
divisor-size interval around the corresponding half.
The eligible divisor intervals have a common hull of width
\(O(\kappa+\omega+1/L)\), since
\(\log_x q_s=1-\log_x s+O(1/L)\). The proof there is uniform in the present \(\tau\): all its power margins hold on this range and its outer reciprocal-prime sums may be majorized by fixed exponent windows containing the allowed bands.
On these near-half ranges the divisors are proper
for sufficiently small \(\kappa+\omega\). The coefficient
\(W_s(-F(m))\) is the same positive actual weight as in
that estimate. The full rough squareful \(n\)-exception is
log-negligible with arbitrary reserve: a repeated base
in \(q_s\) costs \(O((x/s)x^{-\delta})\) candidates at
fixed \(s\), and \(s\mid q_s\) costs \(O(x/s^2+1)\)
per prime \(s\), before divisor moments.
The polynomial-small factor deletion in
[FavorableRankSixMultiscaleCoreDeletion.md](FavorableRankSixMultiscaleCoreDeletion.md)
can be applied separately to each fixed \(f_s\) in the actual
finite set of opened rows if desired. No joint limit making
its constant uniform in a steep transition is asserted.

## 2. All signs at rank five and a surviving actual family

For a squarefree \(q\) of rank five define
\(S(q)=\sum_{d\mid q,d<\sqrt q}\mu(d)\).
If the largest prime factor exceeds \(\sqrt q\), then the
short divisors are all divisors of the complementary
nontrivial product, and \(S(q)=0\).
Otherwise all five singletons are short; if \(j\) is the
number of pairs above \(\sqrt q\), there are \(10-j\)
short pairs and \(j\) short triples by complement.
There are no short four-fold products. Since \(q\)
is squarefree there is no divisor tie at its true half.
Consequently
\[
                              S(q)=6-2j .
 \tag{6}
\]
Two long pairs cannot be disjoint, since their product
would then exceed \(q\). An intersecting edge family on
five vertices of size at least four is a star
(if three of the edges form a triangle, no fourth
edge can meet all of them). Hence \(j\le4\), and
the negative value \(-2\) occurs exactly when the
four star edges centered at the largest prime are long.

For complete rank-six \(n\) orientations this also gives
a precise constraint on the negative marker set. Write
\(P=P^+(n)\) and \(B=\log n-2\log P\); \(P\) is not an
eligible short marker on these profiles.
Let \(a_s=\log s\) and \(b_s=\log P^-(n/s)\). Applying
the giant and star tests to the actual \(q_s=n/s\)
gives the exact equivalence
\[
              S(q_s)=-2
          \quad\Longleftrightarrow\quad
                         a_s<B<a_s+2b_s .
 \tag{7}
\]
Except for the possible removal of the single least
prime of \(n\), \(b_s\) is independent of \(s\).
Thus all other negative canonical markers form the
intersection of the permitted marker set with one
interval in the actual logarithms. This conclusion
does not rely on equality or smoothing of their weights.

### Complete weighted sign, even over the full original marker band

For all sufficiently large \(x\), the largest of the six prime factors is above \(x^{.14}\), since \(n>x/2\). Allow **any subset** of the
true marker primes of \(n\) at exponents in \([.10,.14]\),
not necessarily the tight bands used for (5).
At the exact canonical half the following is pointwise:
\[
 \text{if some allowed }s\text{ has }S(q_s)>0,\qquad
                     \sum_{s\in J(n)}W_s(q_s)S(q_s)>0 .
 \tag{8}
\]
Moreover, if \(S(q_s)=6\) or \(4\) then no opposite
negative marker can occur anywhere in the same allowed set.
If \(S(q_s)=2\) there is at most one opposite negative
marker, and it is larger than \(s\).

To prove this write \(T=\log n\), \(P_0=\log P\) and
use \(a_s=\log s\). Suppose \(S(q_s)>0\), so the number
\(j_s\) of long pairs in \(q_s\) is at most 2.
Every negative orientation \(t\) has a four-edge star at
\(P\) in \(q_t\). It must have \(a_t>a_s\): otherwise its
half is larger, and the three common star edges already
give at least three long pairs in \(q_s\). Also its edge
\((P,s)\) in \(q_t\) is strictly long, so
\[
 P_0+a_t-(T-a_s)/2
  =P_0+a_s-(T-a_t)/2+(a_t-a_s)/2>0 .
\]
That is, \((P,t)\) is a long pair in \(q_s\).
Hence the number of negative markers cannot exceed \(j_s\).

If \(j_s=1\) and \(t\) were negative, the three other
pairs at \(P\) in \(q_s\) would all be short.
Writing \(H_s=T-a_s\) and summing the four non-\(P\)
label exponents of \(q_s\) yields
\(H_s\le P_0+a_t+3(H_s/2-P_0)\), hence
\(2P_0\le a_t+H_s/2\).
The negative star at \(t\) has
\(2P_0>T-a_t-2a_s\).
Combining yields \(T<4a_t+3a_s\le.98L\), contradicting
\(T\ge L-\log2\) for large \(x\).
The case \(j_s=0\) was already excluded.

If \(j_s=2\) and two negative markers \(t_1,t_2\) occurred,
the two known long pairs \((P,t_1),(P,t_2)\) would exhaust
all long pairs in \(q_s\). The two other pairs at \(P\)
are short, so \(H_s\le P_0+a_{t_1}+a_{t_2}
   +2(H_s/2-P_0)\) gives \(P_0\le a_{t_1}+a_{t_2}\le.28L\).
But either negative star has
\(P_0>(T-a_{t_i})/2-a_s\ge.29L-O(1)\), a contradiction.
Thus at most one negative marker occurs. Its weight is
strictly smaller than \(W_s\) since \(t>s\) and the exact
original cubic is strictly decreasing in its normalized exponent
argument: its derivative at \(u\) is \(-(1-2u)(5-6u)<0\) for \(0<u<1/2\). If this marker exists, the sum in (8) is at
least \(2(W_s-W_t)>0\).
If none exists, the positive orientation alone proves (8).
When all orientations have \(S\le0\), their weighted sum
is of course nonpositive, strictly negative if any
is negative. This completely classifies the sign of the
canonical all-marker sum in terms of which individual
signs occur, without hypotheses on factor spacings.

The statement for exact canonical halves is independent
of whether this entire wide marker band admits a single
whole-row smooth exchange of the desired strength.
For the actual narrow transferred rows of §1 the canonical
conclusion is applicable up to the literal neck error (5).
In particular (8) rules out a purely local repair using
all canonical original orientations in **any** adverse
rank-five case with \(S>0\), not
just in the specific example below.

Here is a genuine unavoidable same-sign sector, even
when all three original near-half marker bands are present.
Take \(n=s_2 s_3 s_4 B_1 B_2 B_3\) and retain the
three actual marker bands of
[NearHalfRankSevenCompensation.md](NearHalfRankSevenCompensation.md).
Center the three \(B_i\) in distinct nearby exponent bands about
\[
          \beta=\frac{1-\gamma_2-\gamma_3-\gamma_4}{3}
                                 =.1943\ldots+O(\tau),
\]
where \(\gamma_i\) are the actual marker centers there.
For example use center offsets \(-.001,0,+.001\);
any sufficiently small fixed positive widths are allowed.
Then exactly these three short markers are eligible.
For every removal \(s_i\), all five prime labels of
\(q_i=n/s_i\) are well below the half, all their pairs
are below .392 and all their triples above .465,
for all sufficiently large \(x\). Thus \(j=0\),
\(S(q_i)=6\), and all \(C_{f_\tau}(q_i)=-6\) exactly
on this chamber. The conclusion is robust to any
near-half modifications within those gaps.
The whole true favorable rank-six input has \(F(m)<0\);
hence after opening the three physical orientations on
these pairs contribute **positive**
\(6(-F(m))(W_2+W_3+W_4)\), not compensating signs.
This chamber is disjoint from the matched \(Q\),
which has eight true labels instead of six.

Its physical occupancy is not just a formal exponent
possibility: ordinary PNT in a fixed relative interval
for the last factor, and harmonic summation over the
other factors, give \(\gg_\tau X/\log X\) true distinct
\(n\)'s in \([.70X,.73X]\) and \(\gg_\tau X/\log X\)
true reflected \(m\)'s in \([1.20X,1.24X]\), at their
stated exponent bands. For this count use exponent base \(X\) and a fixed strict subbox around each center: sum over the first five primes in subboxes narrow enough that the sixth lies within its band whenever the full product lies in the specified fixed relative interval. The prime number theorem applies to that last interval of polynomial length. For every target arising, \(x=N/2\asymp X\), so the exponent change from base \(X\) to base \(x\) is \(O(1/\log X)\) and the strict box margins absorb it. The prime bands of the two
products are disjoint. Their pairs give the literal
even targets \(N=n+m\) with the correct units and
central support. Weighted positive mass over these
targets is \(\gg_\tau X^2/\log X\); using the bounded
mean \(\sum_{N\le 2X}\mathfrak S(N)\ll X\), it is
\(\gg_\tau\mathfrak S(N)x/L\) at some even target per
sufficiently large such interval. This averaged argument
does not imply a simultaneous lower at each fixed target.

Thus the actual new near-half rows are rigid, except
for explicitly priced physical necks. In particular
adding the complete set of near-half orientations
cannot give a *pointwise* compensation of the surviving
rank-five chamber by another short marker of the same
\(n\). This does not preclude a signed estimate matching
it to a different physical \(n\), an altered detector
outside the near-half regime, or genuine equation-sensitive
arithmetic cancellation.

## Comparison

The balanced five-factor sign itself is not new; see [Arneth, PIHR-Goldbach-XII, September 2026 v1](https://zenodo.org/records/23016346), which treats even repeated factors with exact complementary-prime conditions and studies changes of divisor state. Here the scope is different: all allowed marker deletions of a single integer in a specified **already opened** rank-six row are compared simultaneously, with an actual fixed-target bound on the divisor neck. Compare also the distinct rough-pair benchmark in [Pham, October 2026 v1, Appendix D](https://www.preprints.org/manuscript/202610.3061) and the first-exit divisor policies of the [November 2026 weighted Chen preprint, Appendix F](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf). No claimed stronger distribution from those works is used here.
