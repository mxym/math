# Difference-set requirements for the Gaussian gain-to-win argument

This is a separate supplement to [the anisotropic scope note](afllw-anisotropic-kernel-scope.md). Its counterexample concerns the deterministic Lemma 4.7 in the 59-page full version of Albrecht, Felderhoff, Lai, Lapiha and Woo, *A Gaussian Leftover Hash Lemma for Modules over Number Fields*, §4.3, printed p. 25. The [author-hosted manuscript](https://perso.jfelderhoff.fr/work/papers/AFLLW25.pdf) and [fixed manuscript mirror](https://opencryptology.org/2025/1852/versions/20260428T172000Z.pdf) of the [February 24, 2026 ePrint revision](https://eprint.iacr.org/2025/1852) contain this formulation. The deterministic implication fails even with spherical widths. We also give a modified gain-to-win estimate in a clearly delimited model. The deterministic counterexample does **not** disprove their random spherical Lemma 4.5 or a spherical main theorem, and says nothing about a real scheme.

## 1. The deterministic growth statement fails even for spherical widths

Use the definitions of §4.3. In a module of rank \(r\), let \(A\) be a symmetric finite coefficient set containing 0 and 1, of size at least \(2^d\) and largest embedding absolute at most \(B\). Set
\[
 S_j=\Big\{\sum_{i\le j}a_i x_i:a_i\in A\Big\},\qquad
 \widehat S_j=\{s/a:s\in S_j,\ a\in A\setminus\{0\}\}.
\]
There is a win at \(j\) if two of the \(f+1\) translates of \(\widehat S_j\) by \(0,\zeta_f^i e_1\) meet. There is a gain at \(j\) if \(x_{j+1}\notin\widehat S_j\) and it meets the norm cutoff. Lemma 4.7 asserts, up to a shift of one index, that \(O(r\log(rBs_{\min}(S)/\Delta_K^{1/(2d)}))\) gains force a win, with an absolute implied constant. Our indexing below gives successive gains at every available positive index, so the offset convention does not matter. The inference of full \(|A|\)-fold growth from a gain does not hold: collision of two translates tests a difference \(a-a'\) and a difference of old sums, not necessarily an element of \(A\) and a member of \(S_j\). The next constructions refute the deterministic implication rather than just that proof step.

### A simple spherical example

Take growing powers of two \(d\), \(K=\mathbb Q(\zeta_{2d})\), \(f=2d\), \(r=2\), and \(A=\{0\}\cup\{a\in\mathbb Z: a\text{ odd},\ |a|<2^d\}\). It has size \(2^d+1\) and \(B\le2^d\). Take spherical canonical width \(s=2^d\). For each \(i=0,\ldots,d-1\), append the columns \(2^j\zeta^i e_2\) for \(j=0,\ldots,d-1\), in increasing \(j\) within each \(i\). Their norms are \(\sqrt d\,2^j\), below the cutoff. The stated lower bounds on the width hold for large \(d\), since the canonical lattice is \(\sqrt d\) times a unit cubic lattice. Each nonzero rational coefficient in an old sum in the currently active \(\zeta^i\) direction has 2-adic valuation equal to the least exponent with nonzero coefficient, strictly below the new exponent \(j\). Every nonzero element of \(A\) is odd, so multiplying the new column by it gives an active-coordinate valuation \(j\), or gives a nonzero active coordinate when no column in that direction was present. Other coordinate directions on the power basis cannot alter it. Thus every new column gives a gain. But all fractional sums have first module coordinate zero; the \(f+1\) shifts have pairwise different first coordinates, so no win is ever possible. The \(\Omega(d^2)\) gains contradict the claimed \(O(d)\) bound, since \(\Delta_K^{1/(2d)}=\sqrt d\).

### A polynomial-width example

For \(d=2^k\), let \(g\) be the largest power of two at most \(k\), \(d_0=d/g\), and use the subfield \(L=\mathbb Q(\zeta^g)\subset K\). Thus \([K:L]=g\) and \(1,\zeta,\ldots,\zeta^{g-1}\) is an \(L\)-basis of \(K\). Use \(A\) consisting of 0 and the elements of \(\mathcal O_L\) whose \(d_0\) power-basis coefficients lie in \([-d,d]\) and have odd sum. This is symmetric, contains 1, and has size at least \(1+((2d+1)^{d_0}-1)/2\ge2^d\), by counting even/odd first and using \(k\ge g\). The largest embedding absolute is at most \(d_0 d\le d^2\). Its nonzero elements are all units at the unique prime of \(L\) over 2, since the root reduces to 1 there.

Use spherical canonical width \(s=d\), and for each of the \(g\) relative basis directions append \(2^j\zeta^i e_2\), \(j=0,\ldots,k-1\). As above, the \(L\)-valuation of a nonzero previous coefficient sum in the active direction is that of the least nonzero term, now using \(v_{\mathfrak p_L}(2)=d_0\) and \(v_{\mathfrak p_L}(a)=0\) for \(a\in A\setminus\{0\}\). Hence all \(gk-1=\Omega((\log d)^2)\) possible positive-index gains occur with no wins. The standard canonical lattice is \(\sqrt d\) times a unit cubic lattice here, so width \(s=d\) exceeds \(\eta_{1/2}(\mathcal O_K^2)\) and \(\sqrt{2\pi d}\) for large \(d\); the cutoff holds since the largest column norm is at most \(\sqrt d\,d/2\). The stated threshold is only \(O(\log d)\). This counterexample uses polynomial \(B,s\).

The construction is deterministic. It does not by itself disprove the intended *spherical random* conclusion of Lemma 4.5: its exhibited sequences can be extremely rare. In particular it should not be used to infer failure events in an implementation or hardness reduction.

## 2. A corrected gain-to-win bound for dyadic fields

There is a direct deterministic repair with additional control on differences. Let \(C\) be a finite set of size \(c\ge2\) such that \(C-C\subseteq A\); by translation assume \(0\in C\), so \(C\subseteq A\). For an ellipsoid \(S\), use the gain cutoff
\[
             \|S^{-1}x_{j+1}\|\le\sqrt{D},\qquad D=rd,
\]
keeping all definitions of \(S_j,\widehat S_j\) and win. Suppose \(\sigma_{\min}(S)\ge\sqrt{2\pi d}\). Let \(M_a\) denote multiplication by \(a\) on canonical module coordinates. Set
\[
 B_C=\max_{a\in C}\|S^{-1}M_aS\|_{\mathrm{op}},\quad
 J_S=(\det S)^{1/D}/\sqrt d,\quad \overline B=\max(1,B_C).
\]
If \(S\) commutes with multiplication, as for spherical or canonical placewise widths, \(B_C\) is bounded by \(B\). In general it is the displayed relative operator norm.

If \(h\) gain columns have occurred without a win, then
\[
       (f+1)c^h \ \le\ \big[C_0 J_S(1+h\overline B)\big]^D       \tag{1}
\]
for an absolute constant \(C_0\). Indeed, the sums with independent \(C\)-coefficients on these columns are all distinct. If two differed last at a gain column \(x_\ell\), then its nonzero coefficient difference is in \(A\); the other differences give a sum in \(S_{\ell-1}\) after padding missing columns with zeros. This would put \(x_\ell\) in \(\widehat S_{\ell-1}\), contrary to gain. Their sums belong to \(S_j\subseteq\widehat S_j\) and hence have \(f+1\) disjoint translates. In standardized coordinates the sums and translates lie in a ball of radius at most \(h\overline B\sqrt D+1\), since each shift has standardized norm at most \(\sqrt d/\sigma_{\min}(S)<1\). In physical canonical coordinates, the lattice in the dyadic field is cubic with side \(\sqrt d\). Put a fundamental cube around each point in the ellipsoid given by this ball. Its standardized radius is enlarged by at most \(\sqrt{dD}/(2\sigma_{\min}(S))\). The volume ratio, using the unit \(D\)-ball volume at most \((2\pi e/D)^{D/2}\), gives the right side of (1).

Consequently it is enough to take \(h\) a sufficiently large absolute multiple of
\[
       \frac{D}{\log c}\,\log\!\left(
          2+\frac{D}{\log c}J_S\overline B + J_S\overline B\right)
\]
to force a win. This follows by taking logarithms of (1) and bounding the one occurrence of \(\log h\) with a large constant multiple of the other logarithm. The explicit inequality (1) may be used instead. When \(A\) is the full \(\{-1,0,1\}^d\) box in a basis, one may use \(C=\{0,1\}^d\), which retains the desired scale \(r\), instead of \(rd\), outside the logarithm. In general \(A\) only guarantees \(C=\{0,1\}\). If every nonzero element of \(A\) is coprime to an ideal \(I\), reduction modulo each prime dividing \(I\) must be injective on \(C\). Thus \(c\le \min_{\mathfrak p\mid I}\mathcal N\mathfrak p\); the ramified prime of norm 2 is a barrier to using this proof with exponentially large \(c\) in the second step of §4.4.

For a basic probabilistic companion, take the input columns independently from \(D_{\mathcal O_K^r,S}\) and use the ellipsoid cutoff. For any fixed old columns with no win, let \(Y=\widehat S_j\cap\mathcal O_K^r\), symmetric by construction. For every shift \(u\) appearing in the win definition, pairing \(y,-y\) gives
\[
       \rho_S(Y+u)\ge e^{-\pi\|S^{-1}u\|^2}\rho_S(Y)
          \ge e^{-1/2}\rho_S(Y).
\]
The integral translates are disjoint. Therefore the probability that the next column belongs to \(\widehat S_j\) is at most \(1/(1+f e^{-1/2})\). The probability of missing the new cutoff is at most \((\sqrt{2}\,e^{-\pi/2})^D\): exponential Markov with \(\pi\|S^{-1}x\|^2/2\), then Poisson summation gives \(\rho_{\sqrt2 S}/\rho_S\le 2^{D/2}\) since the widened dual theta decreases. So for any no-win history, the next step fails to be a gain with probability at most
\[
                   \alpha=(1+f e^{-1/2})^{-1}
                                 +(\sqrt2\,e^{-\pi/2})^D .
\]
For \(d\ge4\) dyadic, \(\alpha<1/4\). Fix \(h\) violating the hypothetical no-win inequality (1). For \(m\ge2h\), no win through \(m\) steps requires at least \(m-h+1\) failures while still no win. Set such failure indicators to zero after any win; they have conditional means at most \(\alpha\). Iterating the conditional bound over any selected set of steps and taking a union bound shows that no-win probability is at most \(\binom m{m-h+1}\alpha^{m-h+1}\le (2\sqrt\alpha)^m\). This repairs the two gain-to-win steps under the stated modified parameters. It does not repair the original arbitrary-anisotropic \(s_{\min}\)-only smoothing conclusion, nor claim the original sample threshold for an arbitrary coprime alphabet.

The gain-to-win counting here is only an analysis of finite sets and independent mathematical laws. It uses no real scheme, deployment parameter, attacker, or procedure to solve a sample instance.

The accompanying synthetic exact verifier checks the local parity certificate, relative power-basis indexing, and the finite difference-set counting step. The proof does not depend on executing it.
