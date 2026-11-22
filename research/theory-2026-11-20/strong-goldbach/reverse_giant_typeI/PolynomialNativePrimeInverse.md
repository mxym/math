# Prime-inverse cancellation with the full polynomial quotient grouped

Use the fixed-gap calibrated score of [PolynomialNative.md](PolynomialNative.md), at each prescribed even \(N\). In particular \(x=Af\), \(y=N-x=mCh\), \(f,h\) are genuine primes, \(I\subset[N^{1-\gamma},B]\) with \(\gamma<1/2\) fixed, the exact \(m\)-range is \(y/m\in I\), and
\[
 Q_y(m)=\sum_{d\mid m,\ d<y/B}\mu(d),\qquad
 H_{U_i}(n)=1_{n>1}\sum_{a\mid n,\ a\le U_i}\mu(a),\qquad
 U_i=N^{\eta_i},\quad i=x,r.
\]
All original central, target-unit, roughness and prime-cutoff gates are kept. Put \(L=\log N\). The score is the sum of
\((\log f)(\log h)H_{U_x}(A)H_{U_r}(C)Q_y(m)\).
The bound below is for the same score, not an added credit to a different choice of cutoffs.

**Theorem.** Fix independent subintervals of dyads \(f\asymp N^\alpha\) and \(mh\asymp N^\beta\), and allow further independent interval cuts on the actual \(m,h\). Set \(\widetilde\beta=\beta+\eta_x+\eta_r\). Assume the following with fixed strict margins except that \(\alpha+\beta\ge1\) is permitted with equality:
\[
\begin{gathered}
 \alpha+\beta\ge1,\quad
 \tfrac12\widetilde\beta<\alpha<\tfrac47,\quad
 \eta_x<\min(\alpha,\,1-\alpha),\quad \eta_r<1-\beta,\\
 4\eta_x+\eta_r+
 \max\big\{\tfrac12\widetilde\beta+\tfrac{11}{8}\alpha,\quad
           \tfrac76\widetilde\beta+\tfrac23\alpha\big\}<1.             \tag{1}
\end{gathered}
\]
Then this whole box contributes \(O_D(NL^{-D})\) for every fixed \(D>0\), uniformly in all indicated real intervals. There is no condition on \(\operatorname{rad}(N)\), no division into covered and missed banks, and no loss proportional to the polynomial count of actual quotients \(m\).

For example, take \(\gamma=.24,\ \eta_x=\eta_r=.0001\), the original prime cutoffs \(W_x=N^{.30},W_r=N^{.20}\). The genuine box \(f\asymp N^{.36},\ mh\asymp N^{.65}\) is covered: its two exponents in the maximum are \(.8201\) and \(<.998567\), leaving room for \(4\eta_x+\eta_r=.0005\). A scale point on this box has \(m\asymp N^{.22},h\asymp N^{.43}\) and hence \(Ch\asymp N^{.78}\), within the fixed-gap giant range. The more symmetric box \((\alpha,\beta)=(.40,.62)\) admits \(m\asymp N^{.20},h\asymp N^{.42}\), with more than .009 of margin in (1). Neither choice asserts the number of its physical rows. In particular this estimate also reaches below-root true \(h\), without treating it as a free or averaged prime variable.

## 1. Literal product, moving boundaries and true zero mode

Use the same physical cutoff freezing and smoothing as in [PrimeInverseAveraging, §1](../nearfull_high_vaughan/PrimeInverseAveraging.md), with the polynomial \(m\)-range. For clarity, for a moved \(m\)-endpoint the actual \(y\) lies in a relative \(O(L^{-F})\) interval at a fixed multiple scale of \(m\), and \(m\mid y\). Thus the combined unweighted cost is \(O(NL^{1-F}+N^\gamma)\), summing \(O(NL^{-F}/m+1)\) for actual \(m\). For the strict \(Q_y\) cutoff use \(d\mid m\mid y\), \(d\ll S\), on the actual strip about \(y=Bd\). There is no per-cell floor multiplication in either global count. Cauchy with fixed crossed divisor moments then pays both boundaries and the thinner central smoothing collars. Each subsequent cell has a smooth central weight \(\Psi(x/N)\) with fixed log-bounded derivative costs, one real \(m\)-interval, and fixed \(Q_T(m)\).

Open the two short signed labels \(d\le U_x\), \(e\le U_r\) with \(\mu(d)\), \(\mu(e)\), keeping them \(z\)-rough. Both native cofactors exceed their respective \(U_i\) by a power on the stated dyads, by (1) and the central intervals, so no cutoff step depends on \(d,e\). The true roughness of the two remaining free coordinates opens with the same Bonferroni products \(e_1,e_2=N^{o(1)}\); all choices of these two labels are subpower. The two positive omitted tails are paid directly by \(e_i\mid x\) or \(e_i\mid y\) and the factorial reciprocal tails, combined with fixed physical divisor moments. The actual short label openings have fixed power divisor multiplicity, not a separate polynomial factor for this positive boundary cost.

At fixed \(d,e,e_1,e_2\), introduce the exact two coefficients
\[
 F=F_0 f,\quad F_0=d e_1,\qquad H=m h e e_2 .
\]
The free equation is \(F a+H c=N\), with \((FH,N)=1\), \((F,H)=1\). The genuine \(mh\) interval fixes the scale \(H_s\asymp N^\beta e e_2\), irrespective of the individual \(m\)-range. Open the remaining target-unit condition using \(u\mid N\) as in PrimeInverseAveraging, so \(u\mid a\) if and only if \(u\mid c\). The arbitrary-log physical truncation \(u\le\exp(L^{3/4})\) and exact extension of the zero mode follow by the same Rankin estimate; the divisor multiplicity of \(m\mid y\) is already in the physical envelope.

Poisson on the free equation gives the literal main with density
\(\varphi(N)/(N F H)\) in the \(x\)-variable. It vanishes to arbitrary log accuracy after restoring all temporary boxes and summing the original \(d\le U_x\) at fixed \(x,m,f,h,e,e_1,e_2\). The only \(d\)-conditions are \(z\)-roughness and \((d,NH)=1\). The uniform signed harmonic \(\sum\mu(d)/d\) is arbitrarily log-small since \(U_x=N^{\eta_x}\); equivalently use the stronger tail of [the high-cut proof, §1](../nearfull_high_vaughan/Proof.md). When the actual \(m\) is polynomial, the remaining absolute harmonic is still \(\sum_{m\le N^\gamma}\tau(m)/m\ll L^2\). No term depends on \(m\) through a false lcm in this density.

## 2. Reduced numerator and aggregation before the modulus bound

Write \(X\asymp N^\alpha\) for the true \(f\)-scale and \(J_*=uF_0 XH_s/N\). For each nonzero Fourier index \(j\) the exact phase is
\[
 e_H\big(j(N/u)\overline{F_0 f}\big).
\]
Use the smooth prefactor and partial summation in \(f\) exactly as in PrimeInverseAveraging, §2. Its absolute sup and variation per \(j\), uniformly over the dyad of \(H\), are bounded by \(L^{O(1)}J_*^{-1}(1+|j|/J_*)^{-2}\), of log-power total. Frequencies beyond \(N^\varepsilon\max(1,J_*)\) cost a power saving after taking arbitrarily many fixed smooth derivatives. The retained \(\varepsilon>0\) is chosen against the strict margins of (1). Here \(J_*\gg1\) since \(\alpha+\beta\ge1\).

At fixed \(j\ne0\) use only \(g=(j,H)\) among the divisors of \(|j|\) and write \(D_0=H/g\). After the reduction the phase is
\[
 e_{D_0}(a_*\overline{F_0 f})
   =e_{F_0D_0}(a_*\bar f)e_{F_0}(-a_*\bar D_0\,\bar f),
 \qquad a_*=(j/g)(N/u).                                             \tag{2}
\]
Because \(H\) is a target unit, \((a_*,D_0)=1\) exactly, including any square factor. The exact cross mask gives \((F_0,D_0)=1\). Every prime \(f\) in its retained dyad is larger than \(|j|\) for sufficiently large \(N\), since \(\widetilde\beta<1\) in (1) and \(|j|\ll N^{\alpha+\widetilde\beta-1+\varepsilon+o(1)}\). Thus \((f,H)=1\) is still precisely \((f,D_0)=1\). Genuine \(f\mid N\) are removed individually at power-small cost, using only \(O(1)\) such primes and \(O(H_sN^{o(1)})\) assignments after grouping.

Now hold \(j,g,d,e,e_1,e_2,u\) fixed. The actual new modulus \(q=F_0D_0\) determines \(H=gq/F_0\), and hence the exact product \(mh=H/(e e_2)\). All admissible \((m,h)\) at this modulus have total multiplicity at most \(\tau(H)\). Their signed \(Q_T(m)\), prime \(\log h\), physical \(m,h\) windows and relevant unit masks can be summed into one weight \(O(N^{o(1)})\) on this actual modulus before taking absolute values. There are only \(N^{o(1)}\) choices of \(g\) for a fixed \(j\). No new \(m\)-sum or sieve density is used. The congruence phase and its smooth prefactor are identical for all assignments to this same \(H\).

Split \(f,D_0\bmod F_0\) in (2), costing at most \(F_0^2\) independent classes. The final factor in (2) is constant in each. For \(Q=q_{\rm scale}\asymp F_0H_s/g\) one has, up to harmless dyadic constants,
\[
   N^{1-\alpha-\varepsilon-o(1)}\ \ll\ Q
      \ \ll\ N^{\widetilde\beta+o(1)},\qquad
  |a_*|/(XQ)\asymp |j|/J_*.
\]
The lower bound follows from \(g\le|j|\) and the actual frequency truncation. Thus \(Q^{1/2}\le X\le Q^{4/3}\) with room by (1), for every such \(g\). Partial summation in \(f\) uses a **common** real endpoint integrated against the summed variation (not a supremum over independent endpoints for every modulus).

## 3. Composite-modulus completion for the genuine short-class prime sum

We use the proof-level variant of [Irving, §4.3](https://arxiv.org/pdf/1301.6372) in PrimeInverseAveraging, §4, with the following precise stronger local input. On our arbitrary composite \(q=F_0D_0\), \(D_0\) may be squareful but \((F_0,D_0)=1\) and \((a_*,D_0)=1\). In Vaughan Type I, at any fixed short unit \(l\bmod q\), the free arithmetic progression in \(n\) modulo \(F_0\) adds frequencies \(kq/F_0\). On a complete period the reciprocal Kloosterman sum at \(D_0\) is exactly a Ramanujan sum with unit numerator, of absolute value at most one. The \(F_0\) factor is bounded trivially by \(F_0\). On an incomplete period use Fourier completion and the standard composite Weil estimate on \(D_0\), of size \(D_0^{1/2}\tau(D_0)\) since the inverse numerator is a unit. Thus the incomplete error is \(O(F_0q^{1/2}N^{o(1)})\), including logs. The uniform Type I bound is the same as before, multiplied by at most \(F_0N^{o(1)}\) (also for the complete-period term). This uses the actual single congruence class for each shorter \(l\) and not a prime theorem at \(q\).

In Type II open the product congruence of the two Vaughan variables by their unit classes modulo \(F_0\). This costs at most \(F_0\) assignments. Irving Lemma 3.2 applies to the resulting bounded factors, with the genuinely fixed numerator \(a_*\), including his arbitrary numerator reduction. Enlarge only the outer sum of absolute discrepancies from the actual moduli to all moduli in that dyad. The exact range, uniform prefix separation, and choice \({\mathsf V}=\min(X^{1/3},Q^{-1/3}X^{2/3})\) are as in PrimeInverseAveraging, §4. The two \({\mathsf V}\)-terms (from the short Type I length and the longest Type II length) are at most \(Q^{7/6}X^{2/3}+Q^{1/2}X^{11/8}\): for \(X\le Q\) substitute \({\mathsf V}=Q^{-1/3}X^{2/3}\); for \(X>Q\) both are dominated by the second term. The \(X\) and prime-power conversion error \(QX^{1/2}\) are smaller in these ranges. Put differently, the full additional class/completion cost is at most \(F_0^3 N^{o(1)}\), including both outer classes in §2, while \((1+|a_*|/(XQ))^{1/2}\ll N^{\varepsilon/2}\) at the retained frequencies.

Finally summing outer short \(d,e\) costs \(N^{\eta_x+\eta_r}\); their \(F_0^3\) cost is bounded by \(N^{3\eta_x+o(1)}\). Sum the \(N^{o(1)}\) remaining actual short labels and \(u,g\), the fixed log mesh, and the log-power \(j\)-weight. The nonzero sum therefore has the exponent (1) plus \(\varepsilon/2+o(1)\) and an arbitrarily small fixed loss from Irving's bound. The fixed margin gives a power saving. Combined with §1 this proves the theorem. The computation handles the native box itself; it is not a binary prime count and does not sign the complementary boxes.
