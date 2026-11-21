# A strict signed budget for the actual cubic rank ledger

This strengthens [CubicRankFourAndMarkedOccupancy](CubicRankFourAndMarkedOccupancy.md) and uses [CubicEvenTailUpper](CubicEvenTailUpper.md). All terms herein use their **literal cubic** weights, with the new \(6J M_N\) calibration. The result is a genuine uniformly negative total composite correction, not a Goldbach bound, nor an improvement of the usual direct sieve upper for \(Z_N\).

Use the same true \(N=2x,s,q,m,W_s\), unit and central supports, rough guards, \(M_N=\mathfrak S(N)x/(2\log x)\) and \(J=\log(7/5)-.1408\). The cubic \(R(m)\) is the exact mathematical-half score. Write \(H_N^*,D_{6,N},E_{\ge8,N}\) for the favorable actual prime-quotient ranks \(2,3,4\), the adverse actual prime-quotient rank 6, and the transferred higher even term from those two notes. Thus
\[
 Z_N=6J M_N-H_N^*+D_{6,N}+E_{\ge8,N}+o(M_N).
\]
For all sufficiently large even targets, uniformly,
\[
 H_N^*>.0679 M_N,\qquad D_{6,N}<.0375 M_N,\qquad
         -H_N^*+D_{6,N}+E_{\ge8,N}<-.023 M_N.                       \tag{1}
\]
The last constant uses the tighter rational lower before rounding the first displayed number. Earlier independent reserves are not added. The [single-cell budget target](JointShortDivisorProjection.md#1-statement-and-literal-endpoints) for this cubic correction remains below \((.010-5J)M_N\), approximately \(-.96836M_N\), far below the uniform upper in (1).

## 1. Majorize the actual Richert weight by the cubic score

Use a genuine least reflected prime mark \(\ell\) in one of three fixed disjoint bands. The table gives \((A,B)\) for \(x^A<\ell<x^B\), the cofactor rough threshold \(x^u\), penalty endpoint \(x^w\), and a positive constant \(c\).
\[
\begin{array}{cc|ccc}
 A&B&u&w&c\\
 .005&.020&.123&.360&.017\\
 .020&.050&.114&.349&.073\\
 .050&.100&.105&.330&.179
\end{array}
\]
For each band let \(D=.499-B\) and \(\eta=4-(1-A+.001)/w\). As in the previous marked estimate the actual \(\ell d\) and \(\ell p d\) moduli stay within \(x^{.499}\), with both genuine prime \(s,q\) source slots. All marks satisfy \(\ell<x^{.10}<s\), and \(u>B\), so \(\ell\) is the unique smallest prime on every retained rough cofactor row, even across different bands. The exact local density at \(\ell\) includes the real square modulus \(\ell^2\), and primes dividing \(N\) have density zero. The source size divided by \(\phi(\ell)\), dimension-one product, power-small unit-loss at source prime \(s\), and arbitrary log-discrepancy reserve summed over all \((\ell,d)\) and \((\ell,p,d)\) labels are exactly those of the previous proof. Squareful cofactors remain power-small by opening a repeated prime \(h\ge x^u\); the floor exponent is at most \(.14+.10+(1-.005)/2<.74\), and the reciprocal sum saves \(x^{-u}\). No nonsquarefree distinct-prime penalty is substituted for a multiplicity count.

On a squarefree \(x^u\)-rough cofactor \(v=m/\ell\), set
\[
 V(v)=1-\eta^{-1}\sum_{p\mid v}\left(1-\frac{\log p}{w\log x}\right)_+ .
\]
It is \(\le0\) for every \(\Omega(v)\ge4\), since its penalty is at least \(\Omega(v)-\log v/(w\log x)\) and \(v\le1.5x^{1-A}\). Therefore it suffices to check
\[
                  R(\ell v)\ge c V(v)\qquad (1\le\Omega(v)\le3),    \tag{2}
\]
and here \(V(v)\) need not be replaced by a crudely unweighted indicator. The exact certificate below proves (2) with the stated \(c\)'s. It is based on the following continuous elementary comparison, independent of distributions. If \(a=\log\ell/\log m\), let \(b_i=\log p_i/\log m\) for the true cofactor factors, ordered increasingly. For all sufficiently large \(x\) the physical domain lies in
\[
 A-.0005\le a\le B+.0005,\quad b_i\ge u-.0005,\quad a+\sum b_i=1.
\]
Since \((\log m)/\log x\le w/(w-.001)\) eventually, the literal \(V(v)\) is at most
\[
           V_0(b)=1-\eta^{-1}\sum_i(1-b_i/(w-.001))_+ .
\]
For rank two use \(R=1-(1-2a)^3\). For rank three use the exact \(R=24 a b_1 b_2\). For rank four the exact even complementary cubic spline is
\[
 R=1-\sum_{t\in\{a,b_1,b_2,b_3\}}|1-2t|^3
       +\sum_{i=1}^3|1-2(a+b_i)|^3.
\]
This follows directly by grouping all half-score terms in complementary pairs, including proper ties of zero weight. No assumption that the largest prime is below the half cutoff is necessary.

For reproducibility, [check_cubic_richert_signed_budget.py](check_cubic_richert_signed_budget.py) covers the ordered angular domains by rational midpoint interval boxes. In rank three it takes the product of individual lower coordinates and the penalty at their individual upper coordinates. In rank four it bounds \(R-cV_0\) by its exact affine terms at a box center. The positive spline terms and the positive penalty ramps are convex and bounded below by their center tangents. For a negative spline term with center argument \(t\) and half-width \(\delta\) in that affine argument, subtract the valid remainder \(12(|1-2t|+2\delta)\delta^2\), since the second derivative of \(|1-2t|^3\) is \(24|1-2t|\). The largest cofactor coordinate is eliminated exactly as \(1-a-b_1-b_2\); infeasible boxes are detected only by necessary ordered-coordinate inequalities. An unresolved box is bisected in its longest direction, and every box is certified before the hard depth limit. The checker uses exact rational arithmetic even under Python `-O`.

## 2. Summed physical lower and adverse upper

The same real linear sieve as in CubicRankFourAndMarkedOccupancy applies to \(V(v)\). For all three bands \(2<D/u<4\), and \(0<(D-t)/u<3\) for \(u\le t\le w\); thus the actual lower and upper sieve functions are the same explicit \(f,F\) used there (Matomäki--Zuniga-Alterman, [Lemma 2.5](https://doi.org/10.1017/S0305004125000258)). The full signed sum of \(V\), with true \(W_s(q)\log m\), is at least
\[
 (2J M_N+o(M_N))\log(B/A)
 \left\{
 \frac{\log(D/u-1)}D-
 \frac{1}{\eta}\left[\frac{\log(w/u)}D+
   \left(\frac1D-\frac1w\right)\log\frac{D-u}{D-w}\right]\right\}.
\]
The same normalization follows from the actual \(s,q\) center and the additional \(\ell\)-prime harmonic. For the penalty, use the actual \(p\)-harmonic and drop \(p\mid N\) exclusions only in the upper. The order of the parameters is fixed. By (2) the actual \(H_N^*\) dominates each band's lower times its \(c\): outside the three favorable ranks the weights \(V\) are already nonpositive, and none of the other actual \(H_N^*\) terms is negative. Summing the exact three disjoint bands gives
\[
             \liminf_{N\to\infty,\;2\mid N}H_N^*/M_N>.0679775 .
\]

For the adverse rank six, \(R\le0\) on every shape by the full cubic sign argument. Apply the fixed-rank prime-quotient upper of CubicEvenTailUpper to \(-R\) at rank six and remove tiny reflected factors using that note's fixed-target upper before taking \(\kappa\downarrow0\). Its normalized angular integral is
\[
 |A_6|=\frac3\pi \frac{2^6}{6!}\int_0^\infty
                    \frac{(\arctan t)^6}{t^4}\,dt.
\]
Thus the actual pointwise limsup is at most \(4.8J|A_6|\). The same certificate encloses the integral by monotone right Riemann bounds on 64 subintervals per dyadic interval in \([1/4,128]\); outside it use \(\arctan t\le t\) and \(\arctan t\le\pi/2\). Alternating arctangent series, after the elementary argument reductions, give rational endpoints. This proves \(4.8J|A_6|<.037481\). Combining the exact computed allowances with \(\limsup E_{\ge8,N}/M_N<.0073\) from the previous note leaves more than .02319 of genuine fixed-target negative reserve, proving (1) with strict margin.

## 3. The required rank balance is compatible with the actual dyadic mean

The weighted dyadic mean of \((H_N^*-D_{6,N})/M_N\), where normalization is by \(\sum M_N\) over even targets in \([2Y,4Y]\), is exactly
\[
          \left(5-\sum_{k\ge8\;\mathrm{even}}A_k\right)J,           \tag{3}
\]
with \(A_k\) the cubic signed angular coefficients. For each fixed rank \(2,3,4,6\), first keep all prime exponents in a fixed compact interior of its angular simplex. The same two independent terminal-prime PNT count as in OddPolynomialHalfProjection gives the exact coefficient with anchor \(J\); equality surfaces between opposing primes cost zero measure, and the mean singular normalization is the same. The Fourier tiny-prime estimate in CubicEvenTailUpper controls the actual removed support uniformly by \(O(\sqrt\kappa M_N)\), so this is an equality of actual dyadic means, not merely a heuristic angular assertion. The underlying angular weights are integrable: for rank 2 the score is \(O(\min_i a_i)\); rank 3 is an exact product; for ranks 4 and 6 use the absolute Fourier integral. Let the fixed interior exhaust the simplex. The rank-three coefficient is 2 and the sum of all even coefficients is 3 by OddPolynomialHalfProjection, proving (3).

Since \(|A_{k+2}|/|A_k|\le\pi^2/((k+1)(k+2))\) and the even signs alternate starting positive at 8, the tail sum is between \(A_8(1-\pi^2/90)\) and \(A_8\). The checker encloses \(A_8\) by the same rational monotone integration and gives
\[
 .9778264<\lim_{Y\to\infty}\frac{\sum_{N\in[2Y,4Y],\;2\mid N}(H_N^*-D_{6,N})}
                                {\sum_{N\in[2Y,4Y],\;2\mid N} M_N}
          <.9779012.
\]
The uniform single-cell requirement \(5J-.0027\approx.9756612\) is **below** this mean. Thus this cell target is not obstructed by its mean, but it needs an almost asymptotic uniform lower in a true shifted prime-product statistic, far beyond (1). The displayed strict signed reserve does not itself solve Goldbach.
