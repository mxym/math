# Genuine tagged rough prime axes rule out the calibrated angular toy

Written research note, 2026-11-24. This is a true same-target constraint on the prime-companion measure, not a new payment or a proof against actual no-pair targets. It distinguishes a genuine factor-tag histogram from the least-factor cumulative histogram used by the [earlier calibrated prime-axis model](CQPrimeAxisAngularCountermodel.md). The latter improves the prime-only caricature without producing arithmetic rows.

Use the original even \(N\), central compact \(J\), rows \(x+y=N\) with \((x,N)=1\), \(L=\log N\), \(M_N=|J|N\mathfrak S(N)\), and prime score \(\Pi\). A compact row score \(Z(n)\) below has ordinary mass \(m(Z)\) in the original log-weighted angular measure \(\mu\). Orientations are treated separately; no symmetric \(J\) is needed.

## Genuine compact tagged rough moment

Fix a positive floor \(\eta\), and finitely many disjoint fixed angular bands \((a_i,b_i]\) with \(\eta<a_i<b_i<1\). Suppose \(\sum_i b_i+10\eta<1/2\). In a literal integer argument put
\[
 Z(n)=L\,1_{\{\text{squarefree},\ P^-(n)>N^\eta\}}
       \prod_i\left(\sum_{\substack{q\mid n,\ q\ {\rm prime}\\N^{a_i}<q\le N^{b_i}}}1\right),
 \qquad \Lambda=\prod_i\log(b_i/a_i).
\]
For any nonempty band list this compact score vanishes on primes in the actual central region; it is a bounded angular count because all the bands are polynomial. In either prime orientation \(u_N(Z)=\langle Z,\Pi\rangle/M_N\) or its reflection satisfies
\[
 \frac{\underline c}{\eta}\Lambda+o(1)
 \ \le u_N(Z)\le\
 \frac{\overline c}{\eta}\Lambda+o(1),\qquad
 |u_N(Z)-m(Z)|\le
 \frac{\overline c-\underline c}{\eta}\Lambda+o(1),
\]
where the [already checked ratio-10 constants](CQTrueSignedRoughTailEnvelope.md) are
\(\underline c=.5614584359419\), \(\overline c=.5614605206538\), \(\overline c-\underline c<.000002085\).

To see the true arithmetic estimate, open one genuine named prime from each band. The quotient is sieved at cutoff \(N^\eta\) with level \(N^{10\eta}\) and ratio 10. It is tested on the actual prime source through progression moduli \(q_1\cdots q_k d\) in the stated level \(<N^{1/2}\), residue \(N\), with \(d\) composed of primes at most \(N^\eta\). The named prime product and the sieve divisor are coprime and no prime appears in two named bands. In the physical modulus, the chosen tags are recoverable uniquely by the disjoint bands; the remainder therefore uses only the standard divisor-power weights of the ordinary linear sieve and the genuine ordinary prime Bombieri–Vinogradov theorem. The fixed \(J\)-endpoint subtraction or reflection is the same as in the already used untagged rough tests. Target divisors are omitted with exactly the same local weights (any lost named prime reciprocals are \(O(N^{-\min a_i}\log N)\)). Since every named prime exceeds the quotient cutoff, the local density factor is the same as in the original rank-one rough test, times \(\prod_i(q_i-1)^{-1}\). Harmonic sums for independent disjoint named true primes give \(\Lambda+o(1)\). Multiplication by \(L\) cancels the \(1/L\) from the rough factor, and its \(e^{-\gamma}\mathfrak S(N)\) plus the already checked ratio-10 envelope give the displayed constants times \(1/\eta\). This applies to the true semiprime or higher companion, without knowing its rank. Dropping squareful companions after sifting is a power-small error because every remaining prime divisor is \(>N^\eta\), and the normalized counts and multiplicities of chosen tags are bounded. The log-normalization and target/own-log angular collars are the usual fixed positive-floor ones.

The center \(m(Z)\) lies in the same interval by the genuinely averaged prime–product wedge of the earlier dyadic ordinary normalization. In this wedge the constant rank-one prime score has ordinary mass one, and common prime factors in the two arms are negligible by their fixed positive floor. The literal no-pair hypothesis is unnecessary for the sieve and centering. When testing a proposed no-pair angular measure, however, the prime rows have only composite companions and \(u_N(Z)\) is simply its integral of the genuine angular tag count.

## Application to the specific calibrated toy

The original prime-axis countermodel uses the ordinary angular \(\mu\) as base, adds one count unit by its normalized copy on rank-two \(\mathcal A=\{.39<t<.5\}\), and adds a signed same-least-fiber rank-three to rank-two reshuffle on \(.13<t<.15,\ .15<v<.18\). Its other rank-three width is in \((.67,.72)\), and the corresponding rank-two larger width is in \((.85,.87)\).

Take one tag band \((.395,.495]\) and \(\eta=\beta=.0002\). Its true physical tested moduli are \(\le N^{.497}\). The unconditional actual allowable distance from center is strictly below \(.00264+o(1)\), since
\[
 \frac{.000002085}{.0002}\log(99/79)
 \le \frac{.000002085}{.0002}\frac{20}{79}<.00264 .
\]
The reshuffle changes this angular test by exactly zero, since no width on either side of the reshuffle lies in the tag band. The two additional transfers used to define the old family $\nu_\epsilon$ also leave it unchanged: their actual rank-five patch has all widths below $.29$, their actual rank-three patch has widths in $(.09,.10)$, $(.29,.30)$ and $(.60,.62)$, and their rank-two images have one width below $.10$ and one above $.90$. The wider band tested below is unaffected by those extra transfers as well. The rank-two insertion adds
\[
 \frac{\int_{.395}^{.495} dt/[t(1-t)]}{\log(61/39)} > .8 .
\]
Indeed \(1/[t(1-t)]\ge4\), the interval length is .1, and \(\log(61/39)<.5\) follows from \(2(.22)/(1-(.22)^2)<.5\) by the atanh series. On \(\mathcal A\) the larger width is at least .5 so the only counted tag in that band is the smaller width. Thus this specific toy misses a real arithmetic interval by more than .797. Its prior compatibility with a family of genuine least-factor counts did not test this genuine factor-tag statistic. This objection does not require any composite–composite extension of the toy.

A more general localization of this particular obstruction: take instead \((.39,.4969]\) at the same floor. The actual allowed deviation still is \(<.0029+o(1)\). Suppose a proposed angular prime law changes only the old rank-two region \(\mathcal A\) plus a region on which this tag score is zero (as for the old low reshuffle), and respects the old true domination \(d\nu/d\mu\le3.446\). Then its net increase of ordinary count mass on \(\mathcal A\) is \(<.034\), not one unit. In the tested part of \(\mathcal A\), the tag count coincides exactly with its count measure, so its net change is bounded by the actual tolerance. In the remaining tail \(t\in(.4969,.5)\), its change is at most
\[
 (3.446-1)\int_{.4969}^{.5}\frac{dt}{t(1-t)}
 \le 2.446\frac{.0031}{.4969\cdot.5031}<.0304 .
\]
The total is \(<.0333+o(1)\), giving the conservative .034. A true law with extra balanced-semiprime mass instead needs a compensating actual tagged deficit in other composite angular types; the profile's least-factor tests alone cannot see that offset. More generally any +.8 supercenter in the original insertion region, measured by the first tag test, needs >.797 compensation in the remaining genuine angular types bearing that same tag. Real no-pair compatibility with such offsets is not decided by this single test. In particular there is no new sign on \(B_N(Y,K_+)\) or total CQ exterior payment.