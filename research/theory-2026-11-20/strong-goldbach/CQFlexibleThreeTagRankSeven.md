# Flexible physical middle slots and a weighted reverse capacity for CQ wrong-rank subtraction

Written continuation of the [actual fixed-target CQ rank-seven subtraction](CQActualRankSevenSubtraction.md), 2026-11-24. Use the original \(x+y=N\), central \(J\), target units, \(M=|J|N\mathfrak S(N)\), \(L=\log N\), signed sharp \(H=V_{\rm raw}-\Pi\), literal \(Y=B_0+C\), and full genuine negative remainder \(K_-\). The nonnegative source \(D_0\) is the middle true rank-five part known to be contained in \(Y-A\) for the literal two-tag receiver \(A\); its actual score is \(-H\), and its exact ordinary mass is \(969075913/7200000000\). The original disjoint split by the \(Y\) coordinate therefore remains available.

**Result.** With the real receiver described below, both fixed-target directions give
\[
 M^{-1}\langle D_0,D_3'\rangle,\ M^{-1}\langle D_3',D_0\rangle
 >.00159469+o(1).
\]
The exact replay gives .0015946942064146 in 40,604 physical triple cells; 15,885 of them are **outside** the old 24,719-cell list and give .0003535297371491 per orientation on those newly reachable supports alone. The new total **replaces**, does not add to, the whole earlier .00090336 per orientation. Among the principle-level changes are a rank-five-only weighted reverse capacity (opening two or three actual tags), choosing the full physical middle-modulus subset per cell instead of physically preferring only its larger two tags, and an exact rank-four finite-difference sign bound. The complete signed exterior is still unestimated.

## 1. Rank-five-only reversed capacity

Fix an arbitrary nonnegative genuine fixed-floor compact angular source \(U\) of positive product type; the rank-seven count sources below qualify. Reverse the directed pairing so the \(D_0\) arm receives. In its original branch I, open its actual first two labels \(p,q\), with \(t\in(.04,.105]\) and \(v>.17\); sorted rank five gives \(v\le(1-t)/4\) in the ordinary limit. Its remaining three labeled widths sum to \(X=1-t-v\) and are all at least \(v\). In its original branch II, open its actual first three labels \(p,q,r\), with \(t\in(.04,.105]\), \(t\le v\le .17\), \(v\le w\le(1-t-v)/5\). The \(w\) interval forces \(v\le(1-t)/6<.17\). The last two widths sum to \(X'=1-t-v-w\) and are both at least \(w\). The cuts defining \(D_0\) are literal target-log cuts; replacing widths by own-log widths introduces vanishing fixed compact boundary collars only.

For a fine fixed angular cell of either branch, write \(s\) for the opened-width sum and \(\ell\) for the largest opened width. Summation in the true reflected source uses ordinary compact product Bombieri–Vinogradov at the actual modulus \(pqd\) (branch I) or \(pqrd\) (branch II), all at most \(N^{.499}\), not anything above root and not the cofactor length as source. For upper bins use \(E=.499-s_{\max}\), select quotient cutoff \(\zeta=\min(\ell_{\min},E/2)\), and apply the ordinary dimension-one upper function (ratio \(E/\zeta\ge2\)). This is a genuine majorant: every eligible quotient has all factors above its corresponding literal \(\zeta\). The weighted BV cost is controlled by the same compact product input as the earlier one-tag reverse upper: any physical modulus has a bounded number of named ordered tags because all tags are \(\ge N^{.04}\), and the extra sieve coefficients have at most fixed divisor-power weights. For each tag pattern, excluding the finitely many opened primes in the quotient sieve changes the local product by \(1+O(N^{-.04})\); without that exclusion the exceptional squareful rows can also be removed as in the earlier upper proof. The target-unit masks and true reciprocal main term are those of the existing reverse pairing, with independently selected bins and finite errors before taking a mesh limit. This argument applies in both orientations without identifying primes across arms.

At the integration limit the normalized quotient upper is at most
\[
 \max\left(2/(.499-s),\,2/(3\ell)\right).
\]
Indeed for \(2\le E/\zeta\le3\) the exact scaled upper is \(e^{-\gamma}F_1(E/\zeta)/\zeta=2/E\). For \(E/\zeta>3\), \(\zeta=\ell\) and monotonicity \(F_1(s)\le F_1(3)\) gives \(2/(3\ell)\). On branch I it is always \(2/(.499-t-v)\) since \(v>.17\) and \(E<.289\).

The true rank-five score \(-h_5=1920\prod u_i\) and AM–GM over the untagged widths give upper angular amplitudes \(1920tv(X/3)^3\) and \(1920tvw(X'/2)^2\). The genuine harmonic densities \(dt\,dv/(tv)\) and \(dt\,dv\,dw/(tvw)\) exactly remove the marked products. Consequently in either orientation the actual \(D_0,U\) pairing divided by \(M\) is bounded above by \(m(U)(U_2+U_3)+o(1)\), where
\[
\begin{aligned}
 U_2 &= \int_{.04}^{.105}\int_{.17}^{(1-t)/4}
       \frac{3840(1-t-v)^3}{27(.499-t-v)}\,dv\,dt,\\
 U_3 &= 480\int_{.04}^{.105}\int_t^{(1-t)/6}\int_v^{(1-t-v)/5}
       (1-t-v-w)^2
       \max\!\left(\frac{2}{.499-t-v-w},\frac{2}{3w}\right)
       \,dw\,dv\,dt .
\end{aligned}
\]
This is a true **score** cap, not a replacement model for ordinary mass. The directed replay covers each touching rectangular mesh cell of spacing \(1/4000\), taking the smaller endpoints for numerator widths and opposite endpoints for each denominator. It independently gives \(U_2\le.98041999178205\), \(U_3\le.69117235501950\), so **\(U_2+U_3<1.672\)**. The old bound 4.909 covered the entire middle low-rank receiver; the smaller bound is specifically for the actual rank-five \(D_0\), and can be reused for other genuine rank-count probes against \(D_0\).

## 2. Non-consecutive true tags are legal in the middle modulus slot

Open distinct actual least three primes \(p,q,r\) in ordered, disjoint half-open angular cells \(t_i,v_i,w_i\) of width .002. Set \(S_i=t_i+v_i+w_i\) and \(X_0=1-S_1,X_1=1-S_0\). The search extends the banks to \(t_0=.002,\ldots,.038\), \(v_0=t_0+.002,\ldots,.168\), and \(w_0=v_0+.002,\ldots,.198\), requiring \(S_1\le.49\) and \(5w_1\le1-t_1-v_1\). For any nonempty subset of the three fixed tag labels, let \(b_i\) be its lower/upper aggregate exponent. Its **actual prime product** is assigned to \(Q_2\); the product of all complementary tags (or 1 if empty) is attached to \(Q_1\) or \(Q_3\). The three labels themselves never change. Put
\[
 \mathcal B=.499+b_0/2,\quad E=\mathcal B-S_1,\quad P_+=N^{S_1-b_1},
 \qquad D=N^E,\quad A_0=H_0N^{-10^{-6}},
\]
where \(H_0\ll N^{.105}\) is the actual smallest true prime of the \(D_0\) source and is a Siegel–Walfisz factor. Keep only \(E>S_1-b_1\) and
\[
\begin{aligned}
2\mathcal B-b_1 &\le .999,\\
 2\mathcal B+3b_1+7/32 &<1.997,\\
 2\mathcal B+3b_1+(7/16)(\mathcal B-b_0-b_1)&<1.997.
\end{aligned}
\]
The product of the complementary tags attaches to the first slot when \(A_0\ge P_+\) (split \(d\) at \(A_0/P_+\) and \(DP_+/A_0\)); otherwise it attaches to the third slot (split \(d\) at \(A_0,D/A_0\)). These are the original two-way splits, and their scales are ≥1: \(D>P_+\), and \(\mathcal B-b_1=.499-b_0/2-(b_1-b_0)>.39\) (use the second rail and \(b_1-b_0\le.006\)). The subset product in \(Q_2\) is factorized into its named true primes **uniquely** by their ordered disjoint bins, whether or not those bins are consecutive in size; the slot only needs bounded coefficients on the actual product, not a constraint on which of the original tags it contains. The attachment slot has uniformly bounded multiplicity since each tag exceeds \(N^{.002}\). When all three tags sit in \(Q_2\) both other slots are plain divisors and \(P_+=1\). All three slots thereby have independently bounded coefficient sequences. If literal tags overlap sieve divisors, the squareful and reciprocal deletions are the same as in the known three-tag proof. Their fixed floors and divisor-power multiplicities make them negligible; no mask across the three slots is assumed factorized.

At dyadic scales, \(Q_1\ll A_0\), \(N^{b_0}/O(1)\le Q_2\ll N^{b_1}\), and \(Q_3\ll N^{\mathcal B-b_1}/A_0\). The three exponent rails of Lichtman's Proposition 5.2 are precisely the displayed exponents plus \(2\cdot10^{-6},10^{-6},(1+7/16)10^{-6}\) respectively; their strict slack, and \(Q_1<H_0/N^{10^{-7}}\), suffice. The true residue is always \(N\). Everything else in the actual first three-tag count (nonnegative product cells for the real source, Mellin insertion on the true central interval, exact unit corrections, local quotient density and directed half-open angular cutoffs) is unchanged.

The eligible cutoff list is still \(z=E/2-.0005j\), \(1\le j\le40\); retain only \(w_1<z,\ X_1<5z,\ E<4z\). These imply the actual quotient has from one to four prime factors after squarefree deletion. The three least named primes are uniquely determined by the actual argument because the cutoff exceeds all three upper bins. The physical lower on the entire cell has coefficient \(m(D_0)\mathcal L\,2\log(E/z-1)/E\), with \(\mathcal L=\log(t_1/t_0)\log(v_1/v_0)\log(w_1/w_0)\). Rank seven is removed using its actual ordinary upper \(\mathcal L(X_1-4z)_+^3/(144z^4)\) as in the existing proof, now at the true reversed weighted \(D_0\) capacity \(1.672\). It is not given any CQ score. **Exactly one** marked subset and \(z\) maximize the certified nonnegative bound for each original angular triple, with first maximizer used at ties. Packing alternatives are analytic calculations on the same physical cell, not different receiver sets; no counts or wrong-rank refunds are summed over rival subsets. The angular triples themselves remain disjoint.

## 3. Exact rank-four sign over the enlarged cells

For all \(S_1\le.49\), the remaining rank-four width is \(> .5\) in genuine own-log angles, with a fixed margin since the own-log vs target-log change is \(O_J(1/L)\). Every term containing this angle in the finite differences vanishes. The other three positive widths give
\[
 \frac{-h_4}{t v w}=
 \mathbb E\left[ F'''(t U+v V+w W)\right],
 \qquad F'''(x)=384(1-5x+5x^2), 
\]
with \(U,V,W\) analytic independent uniform variables on \([0,1]\) only to describe the finite-difference integral. There is no probabilistic hypothesis on prime sizes. The polynomial is convex and monotonically decreasing up to \(1/2\); applying Jensen to the integral mean \(S/2\) gives a genuine angular lower \(96(4-10 S_1+5S_1^2)>0\), with uniform negligible collars. This is stronger and covers more than the old endpoint-sign cap. Rank five and six keep their prior true lower amplitudes, so the minimum lower coefficient after factoring \(t_0v_0w_0\) is
\[
 K=\min\left(96(4-10S_1+5 S_1^2),\,1920z(X_0-z),\,
                        3840z^2(X_0-2z)\right).
\]
The positive rank-six minimum just uses the true symmetric unimodal density \(b_6(0)\ge1\), \(b_6''(0)\le0\), and the genuine product minimum of the three quotient widths at the stated lower bound.

The qualifying rank-four through rank-six receivers are all outside the accepted true \(C\): their third true least width \(w\le(1-t-v)/5\) contradicts the original accepted quotient cutoff, whenever their first two widths are in the accepted banks. They have positive physical least \(\le .04\) and do not meet the old middle cuts, rank-eight banks or the older rank-six plateau that requires actual least \(>.04\). Thus their original negative magnitude is in \(K_-\). In the numerical replay only the preapproved cutoff/packing pair on each literal angular cell contributes
\[
 t_0v_0w_0 K\,\mathcal L\left[
 \frac{2m(D_0)\log(E/z-1)}{E}
 -1.672\,\frac{(X_1-4z)_+^3}{144z^4}
 \right]_+.
\]
The exact rational log lower bounds are unchanged from the prior proof; all output weights are rounded down in \(10^{-16}\) units. Of the 40,604 selected packings, 183 put just the third tag in \(Q_2\), 13,137 put the first and third there, 6,548 put the second and third there, and 20,736 put all three there. The count outside the prior angular list is exact. As fixed finite sets the errors sum to \(o(M)\). Since \(D_0\le Y-A\) all these actual pair rows are still disjoint from the \(A\)-based \(c\,m(K_-)\) reservation, and the two true orientations follow independently. The improvement is a genuine but small new favorable sector, not an overall sign or resolution.

[Standalone exact replay](check_cq_flexible_three_tag_rank7.js).