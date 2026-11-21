# Actual far-angle cancellation at low reduced reciprocal frequencies

For the **nonzero** reciprocal terms of [FarAnglePoissonDescent.md](FarAnglePoissonDescent.md), including after the [Heath–Brown subtraction](HeathBrownLongFreeNotch.md), a weighted fourth moment removes all \(0<|\ell|\le x^{.029}\) with a power saving. On a subfamily with an extra actual prime divisor near \(x^{.19}\), it reaches \(x^{.091}\). These cutoffs apply to the **reduced** frequency at the primitive inverse modulus, and so also remove some complete high-gcd strata. The even target is fixed, and both original .09 prime-log slots remain. There is no bound here for the bulk large, nearly coprime reciprocal frequencies.

## 1. Setting and estimate

Let \(x=N/2\), \(L=\log x\). In one inherited pair of dyadic boxes, \(A,B\asymp Y\) are distinct primes in the exponent band \([.0149,.0151]\), \(p_i\asymp P_i\) are the distinct actual primes in \([.089,.091]\), and \(d,r,h,h'\) have dyadic magnitudes \(D,R,H,H'\) and exponent bands \([.489,.491]\), \([.489,.491]\), \([.418,.422]\), \([.418,.422]\). Then \(DP_1H,RP_2H'\asymp x\). Use the earlier row support
\[
 m_1=dp_1h=N-Au,\qquad m_2=rp_2h'=N-Bu,\qquad u>0.
\]
Both rows are units mod \(N\). Keep the smooth normalized free/product weights (fixed log-power derivative bounds), prime logarithms, \(\kappa_A\overline{\kappa_B}\) of log-power magnitude, and any bounded pair mask on \(A,B\) (in particular \(|B-A|\asymp Y\)).

Put \(j=B-A,\ g=(d,r),\ d_1=d/g,\ r_1=r/g,\ q=Ap_2r_1,\ C=Nj/g\). Retain the physical truncations \((j,d),(j,r)\le L^{K_0}\), which imply \(g\le L^{K_0}\), and \(f\mid N,\ f\le\exp(L^\beta)\) for fixed \(0<\beta<1\). The discarded portions of the **physical** sum are separately \(O_{B_0}(xY L^{-B_0})\), taking \(K_0\) sufficiently large, by the common-product gcd argument in the Heath–Brown note and the \(f\)-tail in the Poisson note. The latter argument also works for post-Heath–Brown absolute coefficients: replace \(\tau_3\) by \(\tau_5\) and use its reduced-progression square moment by choosing the largest of 25 factors (\(A_i\ll(x/f)^{1/25}\) for \(f\le x^{1/2}\)). These absolute physical bounds do not assert Fourier bounds on the discarded terms.

The exact retained Poisson factor, to be multiplied by the original arithmetic coefficients, is
\[
 \frac{H}{f q}\,
 \widehat W\!\left(\frac{\ell H}{f q};A,B,p_1,p_2,d_1,r_1,g\right)
 e_q\!\left(\ell(C/f)\overline{B p_1 d_1}\right).
 \tag{1}
\]
Here \((B,q)=1,\ (p_1d_1,q)=1\), all label and divisor factors are units mod \(N\), and \(g\mid j\) is the exact split of the common gcd of the row coefficients. \(W\) includes the coupled window on \(h'\); there is no independent \(h'\)-length substitution.

Write \(s=(C/f,q)\), \(q_*=q/s\) and, for \(\ell\ne0\),
\[
                     v_\ell=(|\ell|,q_*),\qquad k_\ell=|\ell|/v_\ell.
 \tag{2}
\]
We have \(s\le L^{K_0}\) and \(s\mid r_1\): \(q\) is a unit mod \(N\), \(A\nmid j\), and \(p_2>|j|\).

**Claim.** The following selected portions of the original signed sum (1) are \(O(xY x^{-c})\) for an absolute \(c>0\), uniformly in the fixed even target and the boxes.

* On the whole retained box take \(0<|\ell|\le x^{.1795}\) and \(k_\ell\le x^{.029}\).
* On the subfamily where \(d\) has exactly one distinct prime divisor \(c_0\) in \([x^{.1899},x^{.1901}]\), with \(c_0^2\nmid d\), take \(0<|\ell|\le x^{.1795}\) and \(k_\ell\le x^{.091}\).

The signed coefficients may be \(\mu(d),\mu(r)\) or \(b_U(d),b_U(r)\) from the Heath–Brown note, in any combination. The first assertion also allows arbitrary individual divisor-bounded coefficients. One may take \(c=.0002\) asymptotically. In either clause \(|\ell|>x^{.1795}\) costs any prescribed power of \(x^{-1}\) by decay, since \(fq/H\le x^{.1791+o(1)}\). Thus the first clause includes the whole stratum \(v_\ell\ge x^{.151}\) and the second all \(v_\ell\ge x^{.089}\), in particular **all frequencies divisible by the opposite actual \(p_2\)** on the marked subfamily.

## 2. Weighted inverse estimate

The source is [Shparlinski, *Trilinear forms with double Kloosterman sums*, Lemma 2.5](https://arxiv.org/pdf/1710.02777), which gives
\[
 \frac{1}{Q_0}\sum_{Q_0\le q_0\le 2Q_0} J_2(q_0;E)
          \ll (E^4/Q_0+E^2)Q_0^{o(1)}
          \quad(1\le E\le Q_0).
 \tag{3}
\]
Here \(J_2(q_0;E)\) counts unit quadruples in \([1,E]\) with equal sums of two reciprocals mod \(q_0\). We use this **counting lemma**, not the main trilinear theorem of that paper with unsupported arbitrary inverse weights.

Fix \(q_0\) in this dyad and a unit \(a_0\). For positive \(k\asymp T,\ m\asymp M,\ n\asymp Z\), permit bounded joint weights \(\alpha_{k,m}\) and separate bounded \(\gamma_n\), possibly depending on \(q_0\) and the other fixed outer labels. Require unit \(m,n\) mod \(q_0\), and allow stronger unit tests actually used in (1). Put
\[
 U(t)=\sum_{k\bar m=t\bmod q_0}\alpha_{k,m},\qquad
 V(t)=\sum_n\gamma_n e_{q_0}(a_0t\bar n).
\]
Suppose both possible products \(km'\) and \(k'm\) are \(<q_0\) (e.g. \(4TM<q_0\) for standard dyads). We have \(\|U\|_1\ll TM\) and \(\|U\|_2^2\ll TMx^{o(1)}\), since the product congruence implies literal \(km'=k'm\), with at most \(x^{o(1)}\) competing divisor factorizations per product. Hence \(\|U\|_{4/3}\ll (TM)^{3/4}x^{o(1)}\). If all \(n\le E\le Q_0\), additive orthogonality gives \(\|V\|_4^4\le q_0 J_2(q_0;E)\). Apply Hölder to \(U,V\), then average the fourth root over \(q_0\sim Q_0\) by Hölder and (3). The resulting upper bound for the average of the absolute sum is
\[
                   (TM)^{3/4} (Z+Q_0^{1/4}Z^{1/2})x^{o(1)}
                   \qquad(2Z\le Q_0).
 \tag{4}
\]
There is no uniform prime-residue theorem or typical-modulus assumption here. If \(2Z>Q_0\), collect \(n\) into positive residues mod \(q_0\) with coefficient bound \(O(1+Z/Q_0)\). For (3) split these representatives at \(Q_0\), and replace the upper ones \(n\) by \(q_0-n\le Q_0\) and \(a_0\) by \(-a_0\); use the norm triangle inequality. The modified bound in this case is \((TM)^{3/4} Zx^{o(1)}\). For divisor-bounded or log-power coefficients use the homogeneous versions of these inequalities. The result also bounds a sum over a multiset with uniformly bounded multiplicity per modulus: divide by \(Q_0\), not by the multiset's cardinality.

## 3. Arithmetic factorization and weight separation

Fix \(B,g,f,s\), a possible \(v=v_\ell\), and a signed dyad \(k=k_\ell\asymp T\). Set \(q_0=q_*/v\). The phase is exactly \(e_{q_0}(a_0 k\overline{p_1d_1})\), with the unit \(a_0=\pm(C/(fs))\bar B\bmod q_0\). The condition \(v=(|\ell|,q_*)\) becomes \((k,q_0)=1\). Original unit restrictions on \(p_1,d_1\) are still made modulo **\(q\)**, not just \(q_0\). They are permitted as stronger coefficient-side restrictions; no nonunit reciprocal is introduced.

In the first clause set \(m=p_1,n=d_1\). In the marked clause write \(d_1=c_0 n\) and \(m=c_0p_1\). The prime \(c_0>g,|j|,U\) and \(n\) has no prime divisor in the whole marking band. The two prime factors \(c_0,p_1\) can be recovered uniquely from a supported \(m\), by disjointness of their bands. The exact identities are
\[
 \mu(gc_0n)=-\mu(gn),\qquad a_U(gc_0n)=a_U(gn),\qquad
 b_U(gc_0n)=-\mu(gn)-a_U(gn).
 \tag{5}
\]
Here \(a_U(t)=-\sum_{e\mid t,\,e\le U}(\mu*\mu)(e)\) at every positive integer \(t\); its small-divisor formula ignores \(c_0>U\). The signed coefficient is therefore a genuine separate function of \(n\). The cut \((j,d)\le L^{K_0}\) depends only on \(gn\), since \(c_0>|j|\). The dependence on \(p_1\) in the outer row unit conditions is included in \((p_1,q)=1\). Remaining arithmetic restrictions are on the separately fixed labels, \(m\), \(k\), or \(n\), as required.

Split \(c_0,n\) in dyads for the marked clause, costing log powers; write \(C_0\) for the marker magnitude, so \(M\asymp C_0P_1\), \(Z\asymp D/(gC_0)\). The original sharp \(gc_0n\) box can be separated without replacing its endpoints: place half-integers between the last excluded and first included integer at each endpoint, then use truncated Perron on \(\Re z=1/L\) up to height \(x^{B_2}\). The error of each approximated half-line indicator here is \(O(x^{.491+o(1)}x^{-B_2})\) because the half-integer and \(gc_0n\) are separated by at least \(1/2\) and are \(\asymp D\) on these dyads. Choose a fixed large \(B_2\) against the trivial polynomial term count. The \(dz/z\) integration costs \(O(L)\) in absolute norm; powers of \(c_0\) are absorbed into \(\alpha_{k,m}\), and powers of \(n\) into \(\gamma_n\), with bounded magnitudes on the normalized scales.

The remaining \(\widehat W\) needs separation only across \(n\) versus \((k,m)\). For each fixed pair and fixed outer labels, multiply by a compact smooth cutoff in \(n/Z\) equal to one on its dyad. Mellin inversion on the imaginary axis writes the weight as separated powers of \(n/Z\) against a kernel depending on \((k,m)\) and the outer labels. The absolute kernel is bounded by \(L^{O(1)}(1+|t|)^{-2}\) uniformly: derivatives in normalized \(n\) act inside \(W\), whose dependent free-coordinate affine map has bounded coefficients and normalized derivatives on the stated support. More generally each \(\xi\partial_\xi\) on \(\widehat W(\xi)\) can be bounded by integrating derivatives of \(u^aW(u)\) by parts; this introduces no polynomial factor of \(\xi\). The kernel becomes a joint coefficient \(\alpha_{k,m}\); (4) permits that coefficient to depend on the particular modulus and outer labels. Thus we retain the coupled geometry and exact prime tests with only log-power cost.

## 4. Average over actual moduli and normalize

Partition \(q_0=q/(sv)\) in dyads \(q_0\sim Q_0\). For fixed \(B,g,f,s,v\), one \(q_0\) has \(O(1)\) representations
\[
                 s v q_0=A p_2 r_1
\]
in actual labels \((A,p_2,r_1)\): choose the two primes from the prime divisors of \(svq_0\), each in its own band of fixed positive exponent, and \(r_1\) is determined. The numerator \(a_0\) and the weights can vary with this representation; the absolute inverse moment majorant is unchanged. Crucially \(A\) and \(p_2\) both range in this counting argument, rather than holding \(A\) fixed and charging a sparse-moduli loss.

Here \(q_*=x^{[.5929,.5971]+o(1)}\). For all selected boxes, \(TM/Q_0\ll x^{.1795+.2811-.5929+o(1)}=o(1)\): the factor \(v\) divides both the possible \(T\) and the modulus. If \(2Z\le Q_0\), then \(Z\gg Q_0^{1/2}\) with a fixed exponent reserve, even for the marked clause because \(.489-.1901=.2989>.5971/2=.29855\). Thus in either the ordinary or wrapped case (4) is \((TM)^{3/4}Zx^{o(1)}\). Relative to \(MZ\), the exponent reserves are
\[
 .089/4-3(.029)/4=.0005,\qquad
 (.089+.1899)/4-3(.091)/4=.001475,
\]
respectively. All power margins allow the divisor and log-power factors above.

The prefactor in (1) is \(O(H/(fsvQ_0))\). The bounded-multiplicity modulus average after multiplying the prefactor is accordingly
\[
                    O\!\left(\frac{H MZ}{f s v} x^{-.0005+o(1)}\right).
\]
Since \(MZ\asymp DP_1/g\) and \(DP_1H\asymp x\), sum the reciprocal weights in \(g,f,s,v\) (each sum costs at most a log power even over its full integer range). The remaining prime \(B\) has \(O(Y)\) possibilities. This proves the claim with the \(xY\) normalization at the original fixed target.

**Symmetric orientation.** The progression Poisson choice may be reversed frequency by frequency. With \(u_1=h/H\), \(v_1=h'/H'=\lambda u_1-\gamma\), we have
\[
 \widehat{W'}(\xi')=\lambda e(\xi'\gamma)\widehat W(\lambda\xi'),\qquad
 W'(v_1)=W((v_1+\gamma)/\lambda).
\]
The reverse prefactor \(H'/(fBp_1d_1)\) times \(\lambda\) is \(H/(fq)\), and \(\lambda\xi'=\ell H/(fq)\) for \(\xi'=\ell H'/(f Bp_1d_1)\). For compatible representatives \(t=h/f,\ t'=h'/f\), the equation \(Bp_1d_1t-qt'=C/f\) gives \(t/q=t'/(Bp_1d_1)+(C/f)/(qBp_1d_1)\). This extra phase is exactly \(e(\xi'\gamma)\), so (1) agrees termwise with the reverse expression. Both \((j,d),(j,r)\) cuts and the \(f\)-expansion can be maintained. The symmetric statement in particular removes all frequencies divisible by \(p_1\) on the family marked in \(r\). No two-modulus independence is claimed.

## 5. Scope

The marked window has fixed width in the log-exponent coordinate. The prime number theorem gives \(\sum_{c_0}1/c_0\to\log(.1901/.1899)>0\), so in a complete dyadic \(D\)-interval the marked \(d\)'s have positive lower density: count \(D\sum 1/c_0+O(x^{.1901})\) first, and remove multiples of two distinct markers and squares, costing at most \(D(\sum1/c_0)^2+o(D)\) since \(x^{2(.1901)}=o(D)\). This is a statement about the structural subfamily of divisor integers, not about densities of the coupled prime constraints.

The large reduced-frequency sectors remain, in particular \(v_\ell=1\) and \(|\ell|\) at its ordinary \(x^{.175+O(.0041)}\) scale. Even in the marked sector the displayed positive fourth-moment method saves only when \(T^3<M\) with a reserve. It does not close the far-angle covariance, the signed notch, or binary Goldbach. The pre-Cauchy reference subtraction is unchanged.

[Wright arXiv:2609.35950v1 §§3,7](https://arxiv.org/html/2609.35950v1) treats primes in progressions at levels \(30/59\) and \(16/31\) **conditionally on an exceptional zero**. Unlike that prime-AP application, (3) and the estimate here are unconditional. [Jain arXiv:2611.21136v1 Prop. 3](https://arxiv.org/html/2611.21136v1#S3.SS1) treats certain separated triple products in ordinary reduced-residue progressions, not this fixed-target two-sided reciprocal cancellation.

[Wright, *Trilinear Kloosterman fractions II*, arXiv:2608.27732](https://arxiv.org/abs/2608.27732) strengthens nontrivial Kloosterman estimates for subdyadic intervals and applies them to an averaged nearly balanced congruence problem with a small-modulus equidistribution condition. The calculation here instead uses the average inverse-counting lemma (3) directly on the displayed original Poisson coefficient and states the frequency strata, without importing the resulting congruence theorem to the unmatched bulk.
