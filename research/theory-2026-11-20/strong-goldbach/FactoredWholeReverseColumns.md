# Whole true reverse columns at exponents .545 and .550

Retain all notation, weights and true cuts of [WholeReverseColumns.md](WholeReverseColumns.md), in particular \(N=2x\), \(s\sim x^\alpha\) an actual prime, \(.10\le\alpha\le.14\), the reflected high coefficient \(C_m^{\rm hi}(m)\) with \(U=x^{.454},V=x^{.004},Q=x^{.466}\), and the true quotient cutoffs \(U_q=x^{.070},V_q=x^{.010}\). The row to be bounded is still the literal sum (2) of that note, with \(\Lambda(k)\), \(\mu(r)\), and \(1/\log(r k j)\). Restrict the actual quotient divisor \(r\) to the following canonical subfamilies:
\[
 r=pv,\qquad p\ {\rm prime},\qquad
 |\log_x p-p_0|,\ |\log_x v-v_0|,\ |\log_x k-k_0|\le 10^{-5}.
\tag{1}
\]
Here \(k\) is the actual prime-power variable with coefficient \(\Lambda(k)\) and \(v\) is an ordinary integer with its genuine \(\mu(v)\), not a new surrogate. The choices of logarithmic center are
\[
\begin{array}{c|c|c|c|c}
 A=s r k\ {\rm exponent}&\alpha\ {\rm interval}&p_0&k_0&v_0\\ \hline
 .545 & [.100,.140]&.146&.210-.675(\alpha-.100)&.545-\alpha-p_0-k_0\\
 .550 & [.125,.140]&.145&.189&.216-\alpha .
\end{array}
\tag{2}
\]
For each of them the exact signed sum (2) of [WholeReverseColumns.md](WholeReverseColumns.md) is \(O_B(x(\log x)^{-B})\), for every fixed \(B>0\), **with the entire reflected range \(d\ell>Q\)**, including arbitrarily large \(d\ell\) occurring centrally. The new quotient families are genuinely above .510, and within them the reflected short-divisor reassembly itself now uses the *supercritical* reciprocal seam. This is not cancellation over all moduli at these levels.

## 1. Actual factorization and the correct chronological reassembly

In both profiles \(p_0>v_0+2\cdot10^{-5}\) and \(v_0\) is bounded away from 0. Hence \(v<p\), so \(p\nmid v\), and \(p\) is uniquely the largest prime divisor of \(r\), with multiplicity one. The condition defining membership in (1) is thus an exact condition on the original quotient divisor \(r\), with no overcount from marking. Moreover
\(\mu(r)=-\mu(v)\) even if \(v\) is nonsquarefree (both sides are then zero). No extra squarefreeness restriction on the resulting modulus \(A=s p v k\) is imposed. Every nonzero term is on the genuine high reverse branch: \(r>U_q,\ k>V_q\) and \(A=s e>x^{.544}\), so \(e>E_D\) for every reflected \(d\)-dyad of the original reverse proof. The latter follows from \(s E_D\le D^{.495}\ll x^{.495}\). It is essential to reassemble the full reflected high coefficient **before** discarding its original under-hyperbola/seam masks; after removing the whole columns here, those preceding estimates can be intersected with the complementary columns.

Accordingly the exact identity
\[
 C_m^{\rm hi}(m)=\Lambda(m)-(\mu_{\le U}*\log)(m)
       +(\mu_{\le U}*\Lambda_{\le V}*1)(m)
       -\!\!\sum_{\substack{d>U,\ \ell>V\\d\ell\mid m,\ d\ell\le Q}}
                   \mu(d)\Lambda(\ell)
\tag{3}
\]
is used **at each physical \(m\)**. The last three terms have literal short divisor \(a\le Q=x^{.466}\) (for the first of these \(a=d\le U\)). The separated \(s\)-weight and smooth product test \(G(m/x)\) are obtained by the same exact \(K_{P_3}\) separation and finite logarithmic expansion of \(1/\log((N-m)/s)\) proved in [WholeReverseColumns.md](WholeReverseColumns.md). Errors cost \(O_B(xL^{-B})\): the pointwise physical weight is bounded by \(L^C\tau_2(m)\tau_2(N-m)\), since the \(s\)-labels are true primes in a macro-band and the number of eligible divisors at a fixed \(N-m\) is bounded by a divisor power with fixed exponent. Endpoint smoothing costs arbitrarily small log powers by the same divisor moments. The extra representation (1) costs no new multiplicity by uniqueness.

All modulus profiles are \((A,N)=1\) on physical unit support. If \(a\mid m\) and \(m\equiv N\bmod A\), then any common prime of \(a,A\) divides \(N\), impossible; \((a,N)=1\) is also forced. Conversely, given \((a,A)=1\) and \((a A,N)=1\), the additional target-unit mask is exactly \((h,N)=1\) with \(m=a h\). Thus the inclusion for \((h,N)=1\) is **not** replaced by \((h,A)=1\).

## 2. The reflected short-divisor center genuinely crosses the seam

Take \(a\sim M\), \(A\sim P\) in their own dyads. For \(MP\le x^{1-.0001}\) (constant factors from dyadization are harmless) the CRT argument in the whole-columns note applies. Otherwise use the reciprocal estimate of [DoubleVaughanReciprocalSeam.md](DoubleVaughanReciprocalSeam.md), with its exact target-unit treatment: expand \(\sum_{f\mid(h,N)}\mu(f)\), truncate \(f\le\exp(L^{3/4})\) by the **physical** \(m,n\) divisor moments, and Poisson in \(h/f\) at residue \((N/f)\bar a\bmod A\). The grouped short-\(a\) coefficient of either convolution with \(\Lambda(\ell)\) is bounded in modulus by \(\log a\). For the first short piece \((\mu_{\le U}*\log)(m)\), retain
\[
                       \log(m/a)=\log m-\log a
\]
exactly: \(\log m\) is a smooth physical product weight and \(\log a\) is a factor of the short-\(a\) coefficient. Each nonzero phase is the true \(e_A(\nu(N/f)\bar a)\); the three independent coefficients have norms as in Bettin–Chandee Theorem 1, and no estimate for the sign of a new surrogate weight is assumed.

Let \(b=\log_x M,c=\log_x P,g=b+c\). Here \(c>b\), \(b\le .466+o(1)\), \(c\le .55004\) for large \(x\). In the supercritical case the two normalized Bettin–Chandee exponents, before a sufficiently small Fourier/analytic reserve, are bounded by
\[
 .7(1.01604)+.25(.55004)-.85=-.001262,\qquad
 .875(1.01604)+.125(.55004)-1=-.042210.
\]
In the near-subcritical case \(g\ge1-.0001-o(1)\), the corresponding exponents in (11) of the seam note are at most
\(.5-.65(1-.0001)+.25(.55004)<-.012\) and
\(.5-.625(1-.0001)+.125(.55004)<-.056\).
Pick Fourier truncation and analytic epsilon smaller than these positive gaps in the appropriate bounds. The true \(N/f\) factor is paid at the actual natural frequency \(f MP/x\). Thus all nonzero modes of all three short pieces are \(O_B(xL^{-B})\), even in this supercritical part.

The zero term has the same conventional CRT principal density as in (5) of the whole-columns note, \(\phi(N)/(NaA)\) times the test integral. For small \(f\), its factor \(1/f\) sums to \(\phi(N)/N\) with arbitrary log reserve by the harmonic divisor tail; this must be included before the uniform \(a,A\) harmonic summation. For the first short piece, \(\mu(a)\log(m/a)/a\) evaluated by coprime Mertens (6) of the whole-columns note has principal value \((AN)/\phi(AN)\) in the \(a\)-sum. Since \((A,N)=1\), it becomes **exactly** \(1/\phi(A)\) once the Poisson/CRT target density is included. The other two short means are arbitrarily log small by summing the actual \(\mu(d)/d\) for fixed \(\ell\) over \(d\le U\) or \(U<d\le Q/\ell\), with the reduced \((d,AN)=1\) mask; all nonempty active endpoints are polynomially long. The remaining \(\ell,A\) sums are harmonic. This leaves the ordinary centered **prime** progression discrepancy against the original quotient weights.

## 3. Four independent actual modulus factors, three theorem slots

Use [Lichtman, arXiv:2309.08522v1, Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5) with its actual residue \(N=2x\) and \(\theta=7/32\). The proof and SW/clipping details of [WholeReverseColumns.md](WholeReverseColumns.md) apply to the prime input without modification once the four original modulus factors have been placed into its three independent slots. In particular the \(s\)-coefficient depends on \(s\) alone after the finite expansion above; the separate modulus coefficients are proportional to
\[
           \kappa_s,\quad 1_{p\ \mathrm{prime}},\quad -\mu(v),\quad\Lambda(k).
\]
Each is also intersected with its exact \((\cdot,N)=1\) mask and its individual literal dyadic bounds. The restriction to the actual \(r=pv\) factor family causes no coupling past these bounds. If multiple original factors are merged in a slot, their grouped coefficient is still bounded by fixed log powers: the actual \(s,p\) and prime base of \(k\) are bounded below by polynomial powers except possibly the base of a proper prime power \(k\); for fixed such integer \(k\mid A\) there are at most \(O(L)\) prime-power divisors of \(A\) from all sufficiently small bases per allowed macroscopic exponent band. More directly, for each prime dividing the grouped integer only \(O(L/\log p')\) powers of that prime can occur, so the number of prime-power divisors is \(O(L)\) for integers of polynomial size. The actual large primes \(s,p\) have only \(O(1)\) choices, and \(v\) is determined once the other factors in that slot are fixed. Products of composed factors lie in a bounded union of dyads; truncate their grouped supports there. Empty slots consist of the literal singleton \(1\).

For clarity, the Heath–Brown grouping thresholds needed when \(A\le x^{.55004}\) are:
1. A free factor \(\ge x^{.552}\) is handled by the source's Lemma 3.4 with fixed margin.
2. Two free factors of product scale \(\ge x^{.850}\) are handled by its Proposition 3.2, since \((2/3)\cdot .850>.55004\). If neither is in case 1, both individual factors are of polynomial size.
3. Otherwise choose a grouped exponent \(\beta\in[.145,.335]\). The same order-10 identity/greedy argument applies: if there is no individual factor in that band, any large factor \(>.335\) is free, and there are at most two. With at most one such factor the small complement has exponent \(\ge1-.552-o(1)>.145\); with two and too little small mass, the large pair has exponent \(\ge1-.145-o(1)>.850\), which is case 2. Greedy first crossing of .145 among smaller factors is below .290. The source's \(z_0\)-rough support, endpoint meshes, and divisor clipping with retained SW are handled as in §§2.1 and 2.3 of the whole-columns note, with Lemma 4.1 still having a fixed margin at modulus exponent .55004. Only after the clipping are the grouped coefficients divided by fixed log powers to be genuinely 1-bounded.

The exact calculation for all case-3 exponents is in [check_factored_reverse_columns.py](check_factored_reverse_columns.py). It partitions the full \(\alpha\) interval of each row in (2) into cells of length \(10^{-5}\) and tests all \(3^4=81\) assignments of the four original factors to the theorem slots. Each possible slot exponent sum is affine in \(\alpha\); the upper bounds take its maximum at the two cell endpoints, then add \(10^{-5}\) per constituent for the actual factor-width error. The source inequalities are monotone in the three slot exponents after expansion, including its last one with coefficients \(5-2\theta,2+2\theta>0\). For fixed slot upper exponents \(v_1,v_2,v_3\), their exact permitted open \(\beta\)-interval is
\[
 \beta\in\left(v_1+\varepsilon,\
  \min\left\{
   \frac{1-8\varepsilon-v_2-2v_3}{2},\
   2-15\varepsilon-\theta-v_1-5v_2-2v_3,\
   \frac{2-15\varepsilon-v_1-(5-2\theta)v_2-(2+2\theta)v_3}
        {1+2\theta}
  \right\}\right)
\]
with certificate reserve \(\varepsilon=1/50000\). The checker takes the union of these open intervals and requires strict coverage of the whole closed \([.145,.335]\), including both endpoints. Positive strict overlap leaves room for all fixed-factor \(2\)'s and exponent \(o(1)\) errors after taking a smaller analytic \(\varepsilon\) if necessary. This is an exact rational finite calculation, with no floating-point digit used in the proof. The grouping selection depends only on the dyadic scales, not on arithmetic values within assignments; all original factors and their signs remain exactly accounted for.

Thus the actual weighted \(\Lambda(m)\) discrepancy on residue \(N\bmod A\) vanishes to arbitrary log precision in both families (2). Its reduced principal mean matches the short-divisor principal term of §2 by ordinary PNT. Power-size moduli satisfy \(A<x\); hence nonunit ordinary primes cannot distort that principal at the central scale, and proper prime powers cost only \(x^{1/2+o(1)}\) in the summed physical progression rows by the divisor bound on \(A\mid N-m\).

For comparison, [Chan's November 2026 *Theorem (1+1.75)*, §3 and Appendices A–E](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) also uses an exact three-slot convolution before quoting distribution estimates, on structured coefficient families from its sieve construction. [Pham's October uniformity preprint, Appendix B](https://www.preprints.org/manuscript/202610.3061) compares genuine reflected primes with rough terms using ordinary weighted prime dispersion for its Type I range. The profiles here apply to the original signed reverse-Vaughan divisor with its unique (r=pv) split and must also control the supercritical short-divisor reassembly on the reflected side. Neither comparison is used as a proof of the full conjecture.

These are extensions of the actual reverse/Vaughan profile via the same source theorem of Lichtman and the earlier Pan/Bettin–Chandee centered mechanism, not new general distribution theorems. Removing these whole columns leaves other actual reverse coefficients, including unstructured \(r,k\) and much larger \(A\). No required one-sided remainder bound or Goldbach result follows here.
