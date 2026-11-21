# Whole smooth-quotient reverse slabs by canonical exact grouping

Keep the actual row, notation, cutoffs and weights from [WholeReverseColumns.md](WholeReverseColumns.md) and [FactoredWholeReverseColumns.md](FactoredWholeReverseColumns.md). Thus \(N=2x\), \(s\sim x^\alpha\) is prime with \(.10\le\alpha\le.14\), \(k\) has its actual \(\Lambda(k)\) weight, and the original quotient divisor \(r\) has its genuine \(\mu(r)\) weight. The progression modulus is \(A=s r k\), \(q=rkj\), \(m=N-sq\), and the entire high coefficient on \(m\) uses \(U=x^{.454},V=x^{.004},Q=x^{.466}\).

Uniformly in this whole original \(s\)-band, the signed row (2) of [WholeReverseColumns.md](WholeReverseColumns.md) is \(O_D(x(\log x)^{-D})\) for every fixed \(D>0\), on either region
\[
\begin{array}{c|c|c}
 &\log_x A& k\text{ range}\\ \hline
 (i)&[.521,.548]& V_q<k\le x^{.180}\\
 (ii)&[.500,.548]& V_q<k\le x^{.155}
\end{array}
\qquad\qquad P^+(r)\le x^{.018}.
\tag{1}
\]
Here \(U_q=x^{.070},V_q=x^{.010}\) and the true quotient \(r k\)-cut \(E_D\) may be taken as before. In (1) these cutoffs are automatic except \(k>V_q\): \(\log_x r\ge .201-o(1)\) in (i) and \(\ge .205-o(1)\) in (ii), and \(A\ge x^{.5}\) gives \(r k>E_D\) on every reflected \(d\)-dyad, since \(s E_D\le D^{.495}\). Arbitrary additional ordinary intervals on \(r,k,A\) can be imposed. The \(r\)-smooth restriction is real, not replaced by a hypothetical collection of independent moduli. No selection of an \(r\)-prime near a prescribed polynomial exponent is needed. These are whole signed moduli slabs on this smooth sector, not a distribution theorem on the nonsmooth complement.

## 1. Reassemble first, as in the actual factored-column proof

For fixed \(A\), use the exact high reflected \(C_m^{\rm hi}\) reassembly (3) of [FactoredWholeReverseColumns.md](FactoredWholeReverseColumns.md) at each physical \(m\), before imposing any \(d\ell A\) mask. The three reflected short pieces require no factorability for their cancellation against their central means: their proof in §2 there only uses \(a\le x^{.466}\), \(A\le x^{.55004}\), the literal target-unit mask, and independent \(a,A\) coefficients after the finite physical-test separation. For (1), the original modulus weight has divisor-log bound because it is a sum over \(s,r,k\) factoring \(A\). All conditions in (1) are on those outer labels alone. The two supercritical reciprocal exponents at the worst corner \((.466,.548)\) are at most \(-.0032,-.04425\); the near-subcritical and ordinary CRT regions have the same margins as the earlier proof. The zero modes, with the \(N\)-unit density included, leave the matched \(1/\phi(A)\) mean exactly as before.

The task is therefore solely the centered true \(\Lambda(m)\) progression discrepancy on \(N\bmod A\), with the genuine outer weights of (1). We use [Lichtman Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5); the target \(N=2x\) is allowed by its explicit residue parameter, not treated as a fixed small residue. The HB decomposition of this \(\Lambda(m)\) part is the same as in §3 of [FactoredWholeReverseColumns.md](FactoredWholeReverseColumns.md) with maximum \(A\) now only \(x^{.548}\). In particular a single very long free factor or a sufficiently long pair can be disposed of by its cited Lemma 3.4 or Proposition 3.2. The remaining HB term has an independent short grouped factor of dyad exponent \(\beta\in[.145,.335]\) with the required \(z_0\)-rough/Siegel--Walfisz support, and a complementary grouped factor. Its selection, uniform SW (including auxiliary coprimality), sharp product cut separation and divisor clipping are identical to that earlier proof; they do not depend on the present \(r\) or \(A\). What changes is how each original \(r\) is placed in the three modulus slots **at this HB dyad**. The construction below depends on the scale \(\beta\), not the value of an HB variable. It introduces no Fourier twist on the sequence on which SW is required.

## 2. A canonical two-cut factorization with strict margins

It suffices to consider squarefree \(r\), since otherwise \(\mu(r)=0\). List its prime factors in increasing order. Write \(c=\log_x A,\ k_0=\log_x k,\ s_0=\log_x s\), and let the three target exponents be
\[
      v_1^*=\beta-.001,\qquad v_2^*=\max(k_0,.140),
      \qquad v_3^*=c-v_1^*-v_2^*.
\]
Throughout (1), \(v_1^*>s_0\) for all sufficiently large \(x\), and \(v_3^*\ge .007\) in (i), \(\ge .011\) in (ii). In particular the two following cuts are well-defined and nested.

* Let \(r_1\) be the shortest initial prime product for which \(k r_1\ge x^{.140}\). It is \(1\) if \(k\ge x^{.140}\).
* Let \(r_1 r_2\) be the shortest initial prime product whose remaining product \(r_3=r/(r_1r_2)\) satisfies \(s r_3\le x^{\beta-.001}\).

Indeed in logarithms the first cut crosses exponent \(\max(0,.140-k_0)\) of the prefix, and the second crosses exponent \(c-k_0-v_1^*\), greater by \(v_3^*>0\). The first cut thus cannot occur later than the second; they may coincide exactly when a single prime step crosses both thresholds. The second cut is nonempty since \(s r=A/k\ge x^{.341}\) or \(x^{.345}\), whereas \(\beta-.001\le .334\). Each crossing overshoots its target by at most \(\rho=.018\), including zero. Put the three actual modulus slots in this order:
\[
              (Q_1,Q_2,Q_3)\text{ variables } (s r_3,\ k r_1,\ r_2).
\]
Their exponents \(v_i\) satisfy
\[
 v_1=v_1^*-\rho_2,\qquad
 v_2=v_2^*+\rho_1,\qquad
 v_3=v_3^*+\rho_2-\rho_1,\quad 0\le\rho_1,\rho_2\le .018.
\tag{2}
\]
When \(r_1=1\), take \(\rho_1=0\), \(v_2^*=k_0\). If \(r_2=1\), (2) simply gives \(v_3=0\).

For \(\theta=7/32\), the left exponents of Lichtman's four inequalities have the literal upper bounds
\[
\begin{split}
 v_1-\beta&\le-.001,\\
 2\beta+v_2+2v_3
     &=2c+.002-v_2^*+2\rho_2-\rho_1
       \le .994,\\
 \theta+\beta+v_1+5v_2+2v_3
     &=\theta+2c+.001+3v_2^*+3\rho_1+\rho_2
       \le 1.92775,\\
 (1+2\theta)\beta+v_1+(5-2\theta)v_2+(2+2\theta)v_3
     &=(2+2\theta)c+(1+2\theta).001+(3-4\theta)v_2^*
        +(3-4\theta)\rho_1+(1+2\theta)\rho_2
       \le 1.7838125 .
\end{split}
\tag{3}
\]
Thus a small fixed \(\epsilon>0\) satisfies all the required reserves, also after dyadizing each grouped modulus variable. To see this explicitly, discard dyad tuples that cannot contain a canonical tuple, and compare the slot upper sizes to one actual tuple in each remaining dyad: passing to the dyadic upper edges changes each exponent by \(O(1/\log x)\). The expanded source inequalities are monotone in the three slot upper sizes. The strict \(.001,.006\) smaller margins in (3) absorb both this change and the fixed factor in the residue \(2x\).

## 3. Canonical predicates separate at logarithmic cost

The slots in §2 are not presumed independent until the exact canonical constraints are reinstated. Split into the finitely many choices of which \(r_i\) are \(1\). Each \(r_i>1\) is an integer all of whose prime divisors are at most \(x^{.018}\), squarefree, with its own \(\mu(r_i)\) factor. For every pair of consecutive **nonempty** groups in the order \(r_1,r_2,r_3\) impose
\[
        P^+(\text{earlier group}) < P^-(\text{later group}).
\tag{4}
\]
With empties skipped, (4) ensures the three groups are actually consecutive subsets in the increasing list and no shared prime can be introduced. Thus \(\mu(r)=\mu(r_1)\mu(r_2)\mu(r_3)\) exactly. Imposing (4) and the following relations is conversely sufficient for a tuple of independent labels to be the unique canonical one:

1. If \(r_1=1\), require \(k\ge x^{.140}\); otherwise require both \(k r_1\ge x^{.140}\) and \(k r_1/P^+(r_1)<x^{.140}\). Removing the last prime from the prefix thus fails its threshold.
2. Let \(p_*\) be \(P^+(r_2)\) when \(r_2>1\) and \(P^+(r_1)\) otherwise. The \(r_1r_2=1\) pattern is excluded by the lower bound on \(s r\) above. Require both \(s r_3\le x^{\beta-.001}\) and \(s r_3 p_*>x^{\beta-.001}\). Restoring the last removed prime would thus fail the suffix threshold. This includes \(r_2=1\) and \(r_3=1\) without any change.

All these comparisons, the overall \(A\) interval and any additional original \(r\)-interval, separate as a bounded number of Perron integrals. Here are explicit details about the sharp boundaries. A comparison of an integer product to a fixed real threshold is first replaced by the equivalent strict comparison to the appropriate half-integer, so equality is never reached. For (4) compare the earlier group's integer prime \(p\) with \(p'-1/2\), where \(p'\) is the later group's prime; the perturbed quantity depends only on that later group. At every such comparison we thus have a ratio \(u\) of products of positive functions of individual labels, with \(|\log u|\gg x^{-C}\) and \(|\log u|\ll L=\log x\), for an absolute \(C\) large enough. Taking \(\sigma=1/L\) and \(T=x^{C'}\), truncated Perron writes \(1_{u>1}\) as
\[
        \frac{1}{2\pi i}\int_{\sigma-iT}^{\sigma+iT}
                     u^w\,\frac{dw}{w}
            + O(x^{-D_0}),
\tag{5}
\]
with arbitrary fixed \(D_0\) on taking \(C'\) larger. The uniform error follows from the usual \(\ll u^\sigma/(T|\log u|)\) truncated kernel away from the step; here \(u^\sigma=O(1)\). The \(dw/w\) total variation is \(O(L)\); each factor of \(u^w\) has bounded modulus because its base has size between two fixed powers of \(x\) and \(\sigma=1/L\). Thus all cuts together cost only a fixed power of \(L\), uniformly in \(\beta\) and the chosen dyads. A power-small pointwise truncation error is negligible even when summed naively over all polynomially many tuples. Local predicates such as \(k>V_q\), individual smoothness and \((\cdot,N)=1\) are imposed directly. No step integrates a modulus label into the HB short sequence.

For each separated term and dyad, the first slot coefficient sums label factorizations \(s r_3\) with true \(\kappa_s\) (and any finite separated \(s\)-test), the second sums \(k r_1\) with true \(\Lambda(k)\), and the third depends on \(r_2\). Each slot is \(\ll L^C\) with an absolute log-power depending on the fixed original weights: a modulus of polynomial size has only \(O(1)\) possible primes \(s\) in the given macro-band, and \(O(L)\) possible prime-power divisors \(k\). For fixed \(s\) or \(k\) the corresponding \(r_3\) or \(r_1\) is determined; the Perron factors are bounded. Hence after log normalization the **separated** slots really are 1-bounded, as the source requires. The HB short factor clipping remains that of the earlier note with preserved SW, not a normalization by a power of \(x\). If a slot is empty, its coefficient is the singleton \(1\), exactly as in that earlier source application.

The argument applies the source to the centered discrepancy, so the reduced main terms undergo exactly the same canonical grouping by linearity. Summing the log-L¹ loss and the log number of dyads with an arbitrary reserve in Proposition 5.2 proves the centered prime distribution in both slabs (1). The two special HB long cases require no such three-way allocation and keep their original uniform estimates. Combining with §1 gives the claimed full high reflected cancellation, with the true signed \(\mu(r)\Lambda(k)\) input and the original semiprime \(1/\log q\) normalization.

This is a broad exponent slab for a particular family of *actual smooth* quotient divisors, not a coefficient bound over every quotient modulus in the slab. In particular ordinary balanced quotients with a prime factor exceeding \(x^{.018}\) remain untreated here; this provides no dominance on the entire low semiprime cell.

The smooth/flexible-factor concept itself is standard (e.g. Fouvry--Tenenbaum as discussed in [Pascadi, *Smooth numbers in arithmetic progressions to large moduli*](https://doi.org/10.1112/S0010437X2500747X)); the additional result here is the exact original signed quotient row with its two potentially nonsmooth labels \(s,k\), a target \(N=2x\), and cancellation against the matched full reflected high coefficient. The adjacent [Runbo Li manuscript, Theorem 5.5 and §6](https://runbolicarey.com/assets/downloads/Primes_in_arithmetic_progressions_to_large_moduli_and_refinements_of_Harman_s_sieve.pdf) uses a fixed nonzero residue in Theorem 5.5, and §6 starts from smooth squarefree *whole* moduli; neither formulation is used to substitute for this moving-target argument.

[Jain's November 16, 2026 preprint](https://arxiv.org/html/2611.21136v1) also has residue-uniform convolution estimates and an application to smooth numbers. Its smoothness is on an input/summand; the prime argument here remains a genuine von Mangoldt input, with a smooth component of the signed modulus instead. [Chan's November preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) separates other three-slot sieve supports. The current calculation keeps the canonical sorted cuts of the literal reverse quotient coefficient; neither result is used as a substitute for them.
