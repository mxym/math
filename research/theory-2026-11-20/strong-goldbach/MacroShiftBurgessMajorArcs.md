# An actual Möbius–prime Type II notch: normalized major arcs

This note gives an **unconditional major-arc estimate**, not the full Type II estimate, for a nonshrinking logarithmic range of an actual shifted-prime extraction. It uses the long unweighted factor on the \(\mu\times\Lambda\times1\) side, rather than asserting Möbius cancellation in every character of conductor comparable to the target. The normalized minor-arc graph remains unproved.

Retain \(x=N/2,\ L=\log x,\ M_N=\mathfrak S(N)x/(2L)\) and the mixed carrier \(C\) of [MixedCarrierTypeISeparation.md](MixedCarrierTypeISeparation.md). In its suffix \(v\) of exponent near .024 impose an actual prime factor \(A\) of exponent in \([.0149,.0151]\). The remaining suffix \(v/A\) is \(y\)-rough of exponent near .009, therefore smaller than \(A\). This makes the mark unique and distinct from all the earlier labels. If \(F(u)\) indicates the eleven earlier labels and an independently chosen \(y\)-rough suffix of exponent in \([.0088,.0092]\), the new subcarrier on \(I\) is exactly
\[
 C_\sharp(n)=1_{n\in I}\sum_{\substack{A\mid n\\ A\ {\rm prime}\\
             x^{.0149}\le A\le x^{.0151}}} F(n/A).
\]
The suffix exponent restriction is redundant on \(I\) after imposing these labels and \(A\); scale slack and disjointness ensure \(F\) has values 0 or 1. The reference mass of this subcarrier is a positive fixed constant times \(M_N/\varepsilon\) in the same iterated limit, by rough cofactor counts and prime reciprocal sums. No additional mark condition is put on actual primes in the Vaughan variables.

For a piece of the parity-sensitive term (61), take
\[
 \log_x d\in[.489,.491],\quad
 \log_x p\in[.089,.091],\quad
 \log_x h\in[.418,.422],\qquad p\ {\rm prime},\quad dph\asymp x .
 \tag{66}
\]
These are nonshrinking factor-exponent bands with \(\log_x(dp)\ge .578>.573\) and \(p<V=x^{.286}\). Split into \(O(L^4)\) dyadic boxes with variable lengths \(D,P,H,Y\), where \(DPH\asymp x\) and \(A\asymp Y\) in its band. All interval endpoints can also be intersected with the stated bands. The \(h\) factor of length \(x^{.418+O(.004)}\) is an actual unweighted variable from the divisor decomposition, not a replacement for \(\Lambda\).

## 1. The rough-reference subtraction is negligible on this block

Use a piecewise constant mesh multiplier as in (59), with \(\ll L^{O(1)}\) fixed mesh cells; each multiplier lies in \([0,1]\). Let \(J_j\) be one cell in the \(m=dph\) range. For fixed \(d,p\), put \(\mathcal H(d,p)=[H,2H]\cap(J_j/(dp))\), also incorporating the fixed \(h\)-interval restriction. Since \(p\ge x^{.089}\), no prime \(<Z=\exp(L^{1/4})\) divides \(p\). Subpower Bonferroni and CRT over the unweighted \(h\) variable give, for every \(B_0>0\),
\[
 \sum_{h\in\mathcal H(d,p)}\frac{1_{P^-(N-dph)\ge Z}}{V_0}
 =|\mathcal H(d,p)|\,r_N(d)+O_{B_0}(H L^{-B_0}+x^{o(1)}),
\]
uniformly in the cell, with
\[
 r_N(d)=1_{(d,\prod_{\ell<Z,\ \ell\mid N}\ell)=1}
           \prod_{\ell<Z,\ \ell\mid d}(1-1/\ell)^{-1}.
\]
Indeed for each prime \(\ell<Z\), if \(\ell\nmid dp\), one congruence class of \(h\) is excluded. If \(\ell\mid d\), either none are excluded (\(\ell\nmid N\)), or every \(h\) is excluded. The latter case gives zero exactly. Otherwise the CRT error is \(O(1)\) for each product up to the two even/odd Bonferroni ranks near \(L^{1/4}\), and their number is \(x^{o(1)}\). The density tails are smaller than every log power, also after multiplying by \(1/V_0\ll\log Z\).

There is uniform maximal prefix cancellation of \(\mu(d)r_N(d)\) on \(d\asymp D\), with error \(O_{B_0}(D L^{-B_0})\). To verify this, expand \(r_N(d)=\sum_{e\mid d}g(e)\), with squarefree \(g\), \(g(\ell)=-1\) for \(\ell<Z,\ell\mid N\), \(g(\ell)=1/(\ell-1)\) for \(\ell<Z,\ell\nmid N\), and zero otherwise. In the \(e\) sum \(\mu(d)=\mu(e)\mu(d/e)1_{(e,d/e)=1}\). The terms \(e>D^{1/2}\) are negligible by
\[
 \sum_{e>D^{1/2}}\frac{|g(e)|}{e}
 \le D^{-1/4}\prod_{\ell<Z}(1+|g(\ell)|/\sqrt\ell)=D^{-1/4}x^{o(1)}.
\]
For \(e\le D^{1/2}\) use uniform cancellation of \(\mu(b)1_{(b,e)=1}\) at \(b\)-scale \(D/e\ge D^{1/2}\) and sum the bounded log-power harmonic coefficient mass. This coprime cancellation follows by the exact convolution of \(\mu\) with the indicator of integers supported on primes dividing \(e\), using ordinary Mertens cancellation for short convolution factors. The long factors are power-small by Rankin: for \(E\le x^{O(1)}\), \(\prod_{\ell\mid E}(1-\ell^{-1/2})^{-1}=x^{o(1)}\), by separating primes \(\ell\le L\) from larger ones and using \(\omega(E)\ll L\); also \(\prod_{\ell\mid E}(1-1/\ell)^{-1}\ll\log\log(3x)\). These same bounds will be used below. The absolute mass \(\sum |g(e)|/e\) is \(L^{O(1)}\).

For fixed \(p\), the length \(|\mathcal H(d,p)|\) has variation \(O(H)\) in \(d\) (its clipped lower and upper endpoints are monotone). Partial summation, \(\sum_{p\asymp P}\log p\ll P\), and \(DPH\asymp x\) show that the sum with the rough-reference weight is \(O_{B_0}(xL^{-B_0})\). All polynomially many log losses from cells and dyadic boxes fit the reserves. Thus it suffices to estimate the corresponding true carrier block. The Type I proof of (58)–(60) also applies to \(C_\sharp\): in each Jain grouping keep the whole independently supported suffix \(v\) in the same slot, replacing its rough \(0,1\) coefficient by the \(0,1\) coefficient that also requires its unique extra prime \(A\). The length and its independence of the named .054 prime used at low conductors are unchanged. For ordinary BV decompose the extra \(A\) as a distinct labelled interval-prime slot and the now shorter rough remainder by its bounded rank. The interval restriction on the whole suffix stays redundant on \(I\). Thus the same calibrated mesh reference may be chosen for \(C_\sharp\), and the current estimate removes that particular reference contribution. In fact the displayed estimate applies to any bounded constant multiplier on each log-power mesh cell.

## 2. The actual covariance and its major-arc part

Delete \((dph,N)>1\) from the carrier sum at cost \(o(M_N)\) by the nonunit estimate of [MacroShiftRootLattices.md](MacroShiftRootLattices.md), since \(N-dph\) is at least \(y\)-rough. Then also \((A,N)=1\). Smooth the product endpoints into a nonnegative \(\Psi(dph/x)\) of fixed compact support inside \((0,2)\), with possible transition widths \(L^{-B_0}\) and derivatives bounded by powers of \(L\). This changes the original sharp sum by \(o(M_N)\): the total coefficient per product \(dph\) is \(\ll L\tau_3(dph)\); Cauchy with its global second moment bounds the mass of the thin transition intervals. No smoothing of \(\mu(d)\) or the prime indicator is required.

The true sum, for one dyadic \(A\)-range, is
\[
 T=\sum_{N-dph=Au} F(u)\,\kappa_A\mu(d)(\log p)\Psi(dph/x)
\]
with \(p,A\) actual primes, \(h\) unweighted, all product factors units mod \(N\), and \(\kappa_A=1\) sufficient. Allow bounded log-power \(\kappa_A\) on the same prime support. Cauchy gives \(|T|^2\ll(x/Y)\mathcal Q\), where \(\mathcal Q\) is the sum over \(u>0\) of the squared inner sum in \(A,d,p,h\); here \(u\ll x/Y\) and \(0\le F\le1\).

On expanding that square, the original marked forms are \(N-m_1=Au,\ N-m_2=Bu\) with independent \(A,B\) and \(m_i=d_i p_i h_i\). In the determinant and character factorization the crossed pairs are \((B,m_1),(A,m_2)\); put \(T_0=B m_1-A m_2\). The \(\kappa\) factors thus have the opposite conjugation from the \(m_i\) factors, which does not affect any coefficient bound (and \(\kappa=1\) suffices). The exact equation is \(T_0=N(B-A)\). Include \(1_{N\mid T_0}\) and integrate
\[
 e\big(\theta[T_0/N-(B-A)]\big)
\]
over the unit circle to enforce it. This is exact on the specified support; such solutions have positive \(u\) by the support of \(\Psi\). Define the **normalized determinant major arcs** by \(k\le L^{A_0}\), \((a,k)=1\), \(\theta=a/k+\xi\), \(|\xi|\le L^{A_0}/Y\), including the central arc. For any fixed \(A_0,B_0>0\), the sum on these arcs satisfies
\[
 |\mathcal Q_{\rm maj}|\ll_{A_0,B_0} xY L^{-B_0}.
 \tag{66a}
\]
An integral with a partition at overlapping arcs is immaterial (they are in fact disjoint for large \(x\)). This does not estimate \(\mathcal Q_{\rm min}\).

## 3. Separating all the major arcs, including \(k\) sharing \(N\)

Split \(k=k_1 k_2\), where \(k_1\mid N^\infty\), \((k_2,N)=1\), and hence \((k_1,k_2)=1\). Partition both sets of independent variables into residues modulo \(k\), \(O(k^8)\) choices. The rational phase involving \(B-A\) is now constant. On \(k_2\), \(T_0/N\equiv \bar N T_0\bmod k_2\) once \(N\mid T_0\), so that phase is constant too. On \(k_1\), fix \(j=T_0/N\bmod k_1\) (at most \(k_1\) choices) and \(z=A m_2\bmod k_1\), a unit fixed by the residue bins. Then
\[
 T_0\equiv Nj\bmod N k_1
 \quad\Longleftrightarrow\quad
 Bm_1\equiv (A m_2)(1+Nj\bar z)\bmod N k_1.
\]
The factor on the right is a unit, and \(\bar z\) need only be an inverse modulo \(k_1\). A multiplicative character average of modulus \(Q=N k_1\) gives this congruence, with a coefficient of modulus one for each character. No sum over \(N\) residue classes is lost: only the bins modulo \(k\), the \(j\)-choices modulo \(k_1\), and the normalized \(1/\varphi(Q)\) character average occur. The small-denominator phases are held exactly; the remaining real phases are independent on the two sides, of the form \(e(\xi A(m/N-1))\).

For each \(\xi\) and bin, use Mellin separation of \(e(\xi(A/Y)(m/x)Yx/N)\) on its fixed compact positive support in the product \((A/Y)(m/x)\), and of the optional smooth weight \(\Psi(m/x)\). The factor \(e(-\xi A)\) is absorbed into the \(A\) coefficient. The Mellin \(L^1\) norms cost only powers of \(L\), since \(|\xi|Y\le L^{A_0}\) and the derivatives of the other cutoffs cost log powers. Frequencies outside some fixed log power may be discarded with any log-power precision by repeated integration by parts; for those tails use the trivial \(A\) bound and the full threefold character energy in §4, so no gratuitous \(x\)-scale loss is incurred. Thus Cauchy with the Mellin \(L^1\) norms, and \(|XY|\le(|X|^2+|Y|^2)/2\) for the bins on opposite sides, reduce the estimate to
\[
 \frac1{\varphi(Q)}\sum_{\chi\bmod Q}
       |A_\chi D_\chi P_\chi H_\chi|^2
       \ll_{B_0} xY^2 L^{-B_0}
 \tag{67}
\]
with arbitrary log-power reserve. Here the named polynomials are the four independent factor sums with their own bin restrictions, unit character, and phases \(m^{it}\) of log-power \(t\); the \(A\) coefficient also includes the bounded phase \(e(-\xi A)\). The \(D\) coefficients retain \(\mu\), the \(P\) coefficients retain the true prime log, and the only weight on \(H\) other than the bin, interval and character is a Mellin phase.

## 4. The two sources of actual cancellation

By character orthogonality and the divisor moment,
\[
 \frac1{\varphi(Q)}\sum_\chi |D_\chi P_\chi H_\chi|^2\ll xL^{O(1)}.
\]
Indeed the convolution has coefficients bounded by \(L^{O(1)}\tau_3(m)\), is supported on a fixed constant multiple of \(x\), and has \(O(1)\) possible ordinary products per residue since \(Q\ge N\). This also gives a uniform \(xY^2 L^{O(1)}\) bound after multiplication by the trivial \(A\) sup norm, for all Mellin frequencies.

For \(\ell=66\), \((2Y)^\ell<Q\) throughout the label scale \(\log_xY\le.0151+o(1)\), since \(66(.0151)=.9966<1\). Therefore character orthogonality for \(A_\chi^{\ell}\) reduces to equality of the ordinary integer products, and each prime product has at most \(\ell!\) representations. Thus
\[
 \frac1{\varphi(Q)}\sum_\chi |A_\chi|^{2\ell}\ll_\ell (Y L^{O(1)})^\ell.
\]
With \(\eta_0=.005\), the fraction of characters with \(|A_\chi|>Y^{1-\eta_0}\) is at most
\[
 L^{O(1)}\,Y^{-66(1-2\eta_0)}\le x^{-.973566+o(1)}.
\]
On the other characters the threefold energy already proves (67), since saving \(Y^{2\eta_0}\) beats any log power.

For characters with conductor not dividing \(k\), the long unweighted slot satisfies
\[
 |H_\chi|\ll H x^{-.020}
\]
uniformly. For a bin \(h\equiv e\bmod k\), put \(g=(e,k)\); if \((g,Q)>1\), the sum vanishes. Otherwise factor \(h=g h'\) and expand the reduced residue of \(h'\) modulo \(k/g\) by characters. None of the products with \(\chi\) can be principal, since a conductor not dividing \(k\) cannot be canceled by a character of modulus dividing \(k\). Each resulting character is induced from a nonprincipal primitive character of conductor \(\le {\rm lcm}(Q,k)\ll x L^{O(1)}\). Its additional imprimitive unit exclusions are removed by inclusion-exclusion over primes dividing its modulus and not its conductor, at cost \(x^{o(1)}\), using the factor \(f^{-1/2}\) in the length after \(f\)-divisibility. The \(r=2\) Burgess inequality is valid for every primitive conductor (no cube-free hypothesis); see the classical result with \(H^{1/2}q^{3/16+\eta}\), also recorded in [arXiv:2610.22939](https://arxiv.org/abs/2610.22939). At \(H\ge x^{.418+o(1)}\) it has power margin \(.418/2-3/16=.0215\), retaining .020 after log-power and divisor losses, including partial summation for the bounded Mellin phase. Other factors trivially cost \(D P L^{O(1)}\). The exceptional-large-\(A\) characters of this conductor class thus cost at most
\[
 Y^2 x^{2-.040-.973566+o(1)}=Y^2 x^{.986434+o(1)},
\]
which proves their part of (67).

Finally the characters with conductor dividing \(k\) are only \(L^{O(1)}\) in number. For those \(\mu\) in the \(D\) slot has \(O_{B_0}(D L^{-B_0})\) cancellation even with the unit exclusions from \(Q\). To verify uniformity in the bin, let \(\chi_*\) be the inducing character and convolve \(\mu\chi_*\) with the \(\chi_*\)-weighted indicator of integers supported on primes of \(Q\) outside its conductor. This restores \(\mu(d)\chi(d)\) exactly. On the divisor factor \(\le D^{1/2}\), the remaining sum is \(\mu\) in a residue class modulo at most \(k\) times its fixed log-power conductor; a nonreduced class is reduced by taking out its forced squarefree gcd (if not squarefree the sum is zero). The extra coprimality with that gcd may be imposed by splitting into classes modulo its lcm with the new progression modulus, still a log-power modulus. Now use the usual coprime \(\mu\) Siegel–Walfisz estimate. The complementary convolution factors are power-small by the Rankin argument in §1. Partial summation absorbs log-power Mellin phases. With \(\varphi(Q)\gg x/\log\log x\), this proves (67) for these characters as well.

There are only log-power many bin and arc factors, and the total arc length is \(O(L^{3A_0}/Y)\). Thus (67), with its arbitrary log-power reserve, proves (66a). By Cauchy this controls the major part at \(o(M_N)\) scale if the normalized minor part is controlled too. It does not prove the full signed block small on its own; the exact covariance is the sum of the two pieces.

## 5. Remaining problem and scope

The finite-width block (66) has true \(\mu(d)\) and true \(\Lambda(p)=\log p\). It is not estimated by replacing the prime-type quotient weight with a constant. The **free \(h\)** length is what permits Burgess, and it would fail if one applied the argument unchanged to all of (60), whose large prime factor forces a shorter unweighted cofactor. The proof also uses that the mark in the small suffix is an actual uniquely selected prime, supplying the 66th character moment.

The exact large-target root counts of [MacroShiftRootLattices.md](MacroShiftRootLattices.md) may help with the normalized minor part, but the graph still requires a bounded signed operator over the union of target-index lattices, with actual polynomial-scale marks at the physical endpoints and with a quantitative trace saving through all repeated-mark and unequal-scale cases. The primary fixed-shift determinant proofs insert **subpower** marks and rely on a corresponding path complexity budget; using them as-is at \(N\) or with the polynomial mark in this note is not justified. No estimate for \(\mathcal Q_{\rm min}\), the full shifted-prime count for this subcarrier, or Goldbach is claimed.

For comparison, [Lü–Wang–Wu, v2](https://arxiv.org/html/2610.20242v2) proves a theorem for the fixed shift at \(p+2\); [Jiang–Lau–Lü, v2](https://arxiv.org/abs/2611.12467) develops major and minor arc estimates for a different fixed-shift mean square. Their fixed-shift minor analyses are not used to bound the large-target minor arc in this note.
