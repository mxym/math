# A cubic hybrid of the whole low-marker criterion

This changes the **whole** [CenteredMarkerHighRows](CenteredMarkerHighRows.md) low residual, not just the one unbalanced semiprime cell. It preserves its high marker and extraction exactly, removes the old high-rank no-eligible giant sector, and prices the entire all-small sector below .00341 of the Goldbach scale, before arbitrarily small errors. The actual mixed-eligible family and genuine low ranks two–four with no eligible factor remain unbounded at the needed signed scale. This is a competing representation, not additive credit with [PolynomialLogConservationMarker](PolynomialLogConservationMarker.md), where the all-small sector was exactly zero.

## 1. Exact aggregate criterion

Retain the actual even \(N=2x\), \(I=(x/2,x]\), \(L=\log x\), \(\mathfrak S(N),M_N=\mathfrak S(N)x/(2L)\), and actual/rough-reference weights of [SinglePrimeRoughRowCriterion](SinglePrimeRoughRowCriterion.md):
\[
 a(n)=\log(N-n)\,1_{N-n\ {\rm prime}},\quad
 b(n)=V_0^{-1}1_{P^-(N-n)\ge Z},\quad
 w=a-b,\quad Z=e^{L^{1/4}},\quad V_0=\prod_{p<Z}(1-1/p).
\]
Set \(\alpha=.155\). Keep the high-marker parameters of CenteredMarkerHighRows, in particular \(D=x^{1/2-\delta}\), \(\delta=(s+2)e^{-s/2}\), \(z=x^{1/3-2e^{-s/2}}\), for large fixed \(s\). An eligible prime is in \([x^\alpha,D]\). Let \(F(n)=\sum_{d\mid n,\ d\le D,\ P^-(d)\ge x^\alpha}\mu(d)\) be the original marker, with \(P^-(1)=\infty\).

Let \(f_\delta(t)\) agree with \((1-2t)^3\) for \(0\le t\le1/2-3\delta\), and decrease smoothly to zero at \(t=1/2-2\delta\) by multiplying by a fixed smooth cutoff dilated by \(\delta\). Use value exactly 1 at zero, a smooth compact extension on the left, and zero thereafter on the right. For central \(n\), any nonzero \(f_\delta(\log d/\log n)\) automatically has \(d\le D\). Define the actual hybrid
\[
 \mathcal K_\delta(n)=F(n)+
       \sum_{\substack{d\mid n\\P^-(d)<x^\alpha}}\mu(d)f_\delta(\log d/\log n).
                                                                    \tag{1}
\]
Write \(\mathcal A(n)=\{p\mid n:\ p\ {\rm prime},\ x^\alpha\le p\le D\}\). For a small fixed \(\tau>0\) (chosen **after** \(\delta\)), use the following two disjoint true squarefree low families:
\[
 \begin{split}
 \mathcal M_\tau &=
 \{n\in I:\ x^\tau\le P^-(n)<x^\alpha,\ \mu^2(n)=1,\ \mathcal A(n)\ne\varnothing\},\\
 \mathcal L_\tau &=
 \{n\in I:\ x^\tau\le P^-(n)<x^\alpha,\ \mu^2(n)=1,\ \mathcal A(n)=\varnothing,\
              P^+(n)>\sqrt n,\ 2\le\Omega(n)\le4\}.
 \end{split}
\]
The latter score can be taken to be the literal smooth-independent cubic
\[
 R(n)=\sum_{d\mid n,\ d<\sqrt n}\mu(d)(1-2\log d/\log n)^3 .
\]
For any fixed tolerance \(\eta>0\), first choose \(s\) sufficiently large (so \(\delta\) small) and then \(\tau\) sufficiently small. Uniformly for all sufficiently large even targets after those choices, the **whole** alternative low residual satisfies
\[
 \sum_{\substack{n\in I\\P^-(n)<x^\alpha}}w(n)\mathcal K_\delta(n)
 \le \sum_{\mathcal M_\tau}w(n)\mathcal K_\delta(n)
       +\sum_{\mathcal L_\tau}w(n)R(n)+(.00341+\eta)M_N.              \tag{2}
\]
In particular a uniform upper for the two actual sums on the right below \(.00659M_N\), with fixed strict margin and at sufficiently small fixed parameter errors, would stay within the original \(.010M_N\) **whole-low** allowance. Neither of those sums is bounded here. On \(\mathcal L_\tau\), if \(n=r v\) with the unique \(r>\sqrt n\) prime, the score is the full degree-three signed moment on \(v\), including if it has one, two, or three prime factors. Respectively, in normalized cofactor factor logs \(a,b,c\) it is \(1-(1-2a)^3\), \(24ab(1-a-b)\), or \(48abc\), all nonnegative.

To verify this is the original common extraction, on \(P^-(n)\ge x^\alpha\) we have the pointwise **exact** equality \(\mathcal K_\delta=F\). In particular \(H_z\mathcal K_\delta=H_z F\). Summing (1) against \(w\) on the whole \(I\), with **no** \(H_y\) factor, gives \(O_A(xL^{-A})\) by ordinary Type I, since every modulus is \(d\le D\), the coefficient is bounded, and the dependence on \(n\) is smooth with bounded variation. The Type I estimate (3) of SinglePrimeRoughRowCriterion works uniformly in a prefix of \(I\): ordinary maximal BV for \(a\) and the same Bonferroni CRT counts for \(b\), with the identical prefix length in their main term. Apply partial summation for the \(f_\delta\)-weight. This proves a direct signed total null, rather than multiplying two independently centered sums. Subtracting \(P^-<z\) yields the actual high-plus-low decomposition of the original \(H_z F\) extraction. Its high estimate, reference prime mass, and narrow positive high-semiprime error are unchanged. In particular the \(.983M_N\) high cap and the error allowance less than \(.005M_N\) hold with the same order of sufficiently large fixed \(s\) and then growing \(x\). The whole alternative low bound \(.010M_N\) would therefore still imply eventual positivity of prime pairs; a bound for one low cell does not do so.

## 2. Removing all tiny factors in the true signed low ledger

Put \(R_\delta(n)=\sum_{d\mid n}\mu(d)f_\delta(\log d/\log n)\), and let \(R_{\delta,{\rm elig}}\) restrict that sum to divisors supported on eligible primes, with the \(d=1\) term. We have the exact identity
\[
                     \mathcal K_\delta=R_\delta+F-R_{\delta,{\rm elig}}.     \tag{3}
\]
The latter \(F-R_{\delta,{\rm elig}}\) uses only eligible moduli. Its total against \(w\) with no rough guard is arbitrary-log-small by Type I. Against \(H_{x^\tau}w\) use the same dimension-one upper/lower enclosures for the two original **nonnegative** sequences \(a,b\), separately in each eligible divisor progression, with level \(x^{\delta/2}\) and cutoff \(x^\tau\). The physical moduli, including ancillary sieve labels, are at most \(x^{.5-\delta/2}\), and all small labels are coprime to the eligible divisor. Its summed absolute harmonic is \(O_\alpha(1)\), even with the two smooth terms and their prefix partial summation. Thus the inferior and superior enclosures differ by
\[
  \ll_\alpha \left(\tau^{-1}e^{-\delta/(2\tau)}+o_{\delta,\tau}(1)\right)M_N,
\]
with the same full reference local factors as CenteredMarkerHighRows. Choose \(\tau<\alpha\). Applying the two estimates and subtracting proves the signed bound on \(P^-<x^\tau\) for this eligible part of (3). Only this part has been treated by a signed Type I argument; no such cancellation has been claimed for an arbitrary mixed-low profile.

The actual \(R_\delta\) part on \(P^-<x^\tau\) is \(O(\sqrt\tau M_N)\) **in absolute sum against both \(a,b\)**, uniformly in small \(\delta\). Here are the needed Fourier details. The cubic cutoff and its smooth variants have a common compact extension, with
\[
 |\widehat{f_\delta}(\xi)|\ll(1+|\xi|)^{-4},\qquad
 |\widehat{f_\delta-f_{\rm cub}}(\xi)|\ll
                         \min(\delta^4,(1+|\xi|)^{-4}),             \tag{4}
\]
where \(f_{\rm cub}(t)=(1-2t)_+^3\) for \(t\ge0\). Indeed the new difference has height \(O(\delta^3)\) and width \(O(\delta)\), and the third derivatives have uniformly bounded total variation (including the jump of the exact cubic). Fixing a smooth common left extension keeps the difference zero there. As in CubicEvenTailUpper, the divisor sum factors under Fourier inversion over the **distinct** primes of \(n\), with each bit bounded by \(a_\xi(p)=\min(2,2|\xi|\log p/L)\) since \(n>x/2\). The \(a_\xi\) multiplicative weight at every prime power is bounded by 2, independently of \(\xi,x,\delta\), and its Euler envelope is \(O((2+|\xi|)^2)\), by splitting the prime harmonic at \(\exp(L/(2|\xi|))\). Hence its corrected-Henriot class constants are uniform in these parameters.

For the prime sequence \(a\), majorize the actual reflected prime by the \(x^{.4}\)-rough indicator and multiply by \(O(L)\). For \(b\), use its **literal** \(Z\)-rough indicator and \(V_0^{-1}\asymp\log Z\). Its extra positive Euler weight is \(O(L/\log Z)\) by prime Mertens, exactly offset by the normalizing \(\log Z\) relative to the log weight in \(a\). In both cases the two-form product is \(O(\mathfrak S(N)L^{-2})\) before these weights, as in CubicEvenTailUpper. At primes dividing \(N\) keep the two unit masks, so the repeated-root discriminant terms have zero positive-power weights. Their normalized root ratios, including 2, are the usual binary factors. Nonunit \(b\) rows can be discarded: any common prime must divide \(N\) and be \(\ge Z\); their support costs \(O(xL/Z+L)\), and Cauchy with fixed divisor moments and the log-weight bound yields arbitrary-log saving. For \(a\) the only possible nonunit true prime in this central window is \(n=N-n=x\), costing \(O(L)\).

If a genuine \(p\le x^\tau\) divides \(n\), open one such prime for a positive upper and set \(n=p v\). The forms are \(v,N-p v\), primitive on the real support, determinant \(N\), length \(Y\asymp x/p\), and coefficient heights polynomial with fixed exponents. At the slope prime \(p\nmid N\) the extra ratio is at most \((p-1)/(p-2)\) for an odd \(p\), uniformly bounded; \(p=2\) is excluded by units. Factor out \(a_\xi(p)\) **once**, replacing the local weight on \(v\) at \(p\) by 1 so this is valid even if \(p\mid v\). The tagged prime harmonic is bounded by \(\min(C\tau|\xi|,C\log(2+|\xi|))\). Its geometric mean times the common Fourier envelope in (4) is integrable with a bound \(O(\sqrt\tau)\). These are exactly actual same-target counts with all prime/reflection masks, not an angular reference. This proves the tiny part \(O(\sqrt\tau M_N)\) for \(R_\delta\). The same argument without a prime tag, applied to the second Fourier bound of (4), gives the global estimate
\[
                         \sum_{n\in I}(a+b)|R_\delta(n)-R(n)|\ll\delta M_N,           \tag{5}
\]
since \(\int\min(\delta^4,(1+|\xi|)^{-4})(2+|\xi|)^2d\xi=O(\delta)\). In particular fixing \(s\) first and then \(\tau\) does not introduce a hidden \(\delta^{-1}\) in the tiny charge.

For the retained \(x^\tau\)-rough low part, squareful rows cost \(o_{\delta,\tau}(M_N)\) by the power-small repeated-square support and fixed divisor moments. Its rank is bounded by \(1/\tau\), with parameters fixed. Near-half true prime labels \(D<p\le\sqrt x\) cost \(O(\delta M_N)\) against \(|R|\) on the no-eligible part: open one such genuine prime as above, with \(\sum_{D<p\le\sqrt x}1/p=O(\delta)+o_\delta(1)\) and \(a_\xi(p)\le2\). The free length \(x/p\gg x^{1/2}\) maintains all affine-height reserves.

On the no-eligible part we have \(F=R_{\delta,{\rm elig}}=1\), hence \(\mathcal K_\delta=R_\delta\). If the largest prime exceeds \(\sqrt n\), the remaining cofactor has all divisors strictly below the mathematical half, and the full signed cubic moment is exactly zero when \(\Omega(v)\ge4\). Otherwise either a true prime lies in \((D,\sqrt x]\) as just paid or every prime is \(<x^\alpha\). This exhausts the genuine no-eligible class, not just the old semiprime band. It leaves \(\mathcal L_\tau\) and the all-small class.

## 3. Certified all-small charge in the same low ledger

For distinct primes in the all-small part, let \(a_i=\log p_i/\log n\), so \(a_i\le\alpha+o(1)\). Rank at least seven is forced. Every odd rank above three has \(R=0\) exactly. In the angular integrals with all \(a_i\le\alpha\) let \(B_k^{\rm sm}\) be the integral of \(|R|\) with the unordered measure \(da/(k!\prod a_i)\). The fixed-\(\tau\) cutoff can be imposed first on these integrals; it can only decrease the positive upper. The actual \(\sum a R_+\) upper on each finite rank is the established factor-4 whole-product sieve from CenteredMarkerHighRows, equation (35), and \(\sum b R\) is its exact reference, by applying that result separately to the nonnegative scores. Those results apply with \(\tau>0\) in place of \(\alpha\) in their prime product source (the ranks are fixed after \(\tau\)); exponent ties and narrow angular endpoint bands have arbitrarily small limiting measure. Therefore this actual signed sector is at most \(3\sum B_k^{\rm sm} M_N+o_{\tau,\delta}(M_N)\), since \(3R_++[-R]_+\le3|R|\).

At rank eight, remove one smallest coordinate \(a\le1/8\) by its exact bit difference. For any \(j\)-factor subset of the remaining seven, its exponent sum is at least \(1-a-(7-j)\alpha\). The derivative of the positive cubic at log argument \(t\) has absolute value \(6(1-2t)_+^2\), so \(|R|/a\le185.865\), summing the corresponding bounds over \(j\) (if the lower sum bound is negative use \(t\ge0\)). Every remaining \(b_i\ge\max(a,.070-a)\ge.035\), and their sum \(\ge.875\). With cap \(\alpha=.155\), the product is at least \(.035\cdot.065\cdot.155^5\): minimize a product with fixed sum and lower/upper coordinate bounds by pushing pairs to the endpoints, then take the smallest possible total sum. The unweighted volume of the cap simplex is at most \((8\alpha-1)^7/7!\), by omitting the individual upper bounds on the deficits \(\alpha-a_i\). Thus \(B^{\rm sm}_8<.00020611\).

At rank ten, remove the three smallest bit differences, valid because the third derivative of the positive cubic is bounded by 48. This bounds \(|R|\) divided by the product of these three logs by \(48\cdot2^7\). Let \(S\le.3\) be their sum; each remaining log \(b_i\ge h(S):=\max(S/3,.070-S)\) by ordering and the other six-coordinate cap. Their deficit sum is \(.085+S\). For \(S\le.0525\) the extreme product is \(h(S)\alpha^6\). Above that point \(h(S)=S/3\); at fixed number \(j\) of fully used deficits \(\alpha-h(S)\), the minimum product of the seven logs is
\[
            h(S)^j\big[\alpha-(.085+S-j(\alpha-h(S)))\big]\alpha^{6-j}.
\]
The logarithm is concave between consecutive deficit breakpoints \(S_j=(j\alpha-.085)/(1+j/3)\), so its minimum is attained at an endpoint. Those simple rational endpoint checks give product at least \(10^{-7}\). The full cap volume is at most \((10\alpha-1)^9/9!\). Hence \(B^{\rm sm}_{10}<.00021488\).

For all even ranks at least 12, discard the angle cap and use the same absolutely convergent Fourier--Laplace upper (4) of CubicEvenTailUpper. Starting the even exponential tail at \(j=12\), the same rational monotone integration gives a summed absolute angular upper \(<.000715\). [check_hybrid_smooth_cone.py](check_hybrid_smooth_cone.py) certifies the three contributions and that three times their sum is \(<.00341\). Equations (3)--(5), the squareful estimates, and the actual no-eligible profile give (2) with the stated order of parameters. In particular the mixed family in (2) still uses the **exact** hybrid \(\mathcal K_\delta\), not a heuristic extension of cubic parity to its eligible correction. There is no signed bound claimed on that family or on the remaining no-eligible genuine low ranks.
