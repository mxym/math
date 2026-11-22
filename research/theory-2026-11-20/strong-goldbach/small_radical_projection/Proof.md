# Genuine near-full prime factors at each even target of polylogarithmic radical

Write \(\operatorname{rad}(P)=\prod_{\ell\mid P}\ell\). Fix \(B\geq 0\), \(L=\log P\), \(I=[P/3,2P/3]\), and \(S=\exp(L^{1/4})\). For every sufficiently large **individual even integer** \(P\) satisfying \(\operatorname{rad}(P)\leq L^B\), each of the two signs occurs in
\[
 P=p+s q,\qquad p,q\text{ prime},\quad p\in I,\quad q>P/S,\qquad
 (-1)^{\Omega(s)}=\pm1
\]
with count
\[
 (1+o_B(1))\frac{|I|\log S}{2L^2}.
\tag{1}
\]
Here \(\Omega\) counts prime factors with multiplicity. In particular this applies to powers of \(2\) and to even integers supported on any fixed finite prime alphabet, with no Riemann hypothesis or conjectural real-zero bound. The threshold can be ineffective.

There is also a fixed-rank version. For every sufficiently large fixed \(K\), fix any one admissible family of \(K\) disjoint full tag bands as in [the near-full cofactor theorem](../near_full_cofactor/Proof.md), §4. If \(\mathcal T\) consists of the products of one prime from each band, and \(\mathcal V=\sum_{a\in\mathcal T}1/a\), the number of \(P=p+a q\) with \(p\in I\), \(p,q\) prime and \(a\in\mathcal T\) is
\[
 (1+o_{B,K}(1))\mathfrak S(P)\mathcal V |I|/L^2,
\tag{2}
\]
where \(\mathfrak S(P)\) is the usual binary singular series. This gives exactly \(K+1\) distinct factors of \(P-p\) and applies to adjacent sufficiently large ranks. Neither result controls \(s=1\); there is no assertion of binary Goldbach even on these target families.

We prove the replacement for the external zero-free hypothesis in §1 of the former near-full cofactor theorem. We use its unchanged Type I and unweighting arguments and the [full-target projected minor comparison](../target_slope_switch/Proof.md), which in turn uses the real labelled-operator estimates of [Jiang, Lau and Lü, v2, §§5–6](https://arxiv.org/html/2611.12467v2). The new input is a separation of the characters having unusually large tag polynomials from the rest. No prime equidistribution at the tag lengths for individual large-conductor characters is assumed.

## 1. Two classical consequences of having small radical

Fix positive constants \(A_0,\delta,C\). Throughout this proof \(D=P d\), \(1\leq d\leq L^{A_0}\), so
\[
 P\le D\le P L^{A_0},\qquad
 \operatorname{rad}(D)\le L^{B+A_0}.
\tag{3}
\]
The bounds below also apply after multiplying a character by any lift of a character modulo \(d\). Such a lift permutes the characters of \(D\); it is not a change to a larger uncontrolled modulus. If needed one can use \(4D\) instead throughout, leaving all estimates the same.

**Distinct-character Gram bound.** For every fixed \(\delta>0\), there is \(c_\delta>0\) such that, uniformly for \(P^\delta\le H\le P^{O(1)}\), for the full interval \(J_H=[H,1.1H]\), and for distinct characters \(\chi_1,\chi_2\) modulo \(D\),
\[
 \left|\sum_{n\in J_H}\chi_1(n)\overline{\chi_2(n)}\right|
 \ll H P^{-c_\delta}.
\tag{4}
\]
One may use the endpoints of the interval as real numbers and omit integer endpoints at cost \(O(1)\).

To prove (4), let \(\psi\) be the nonprincipal primitive character of conductor \(f\) inducing \(\chi_1\overline{\chi_2}\). Put \(D_0=\prod_{\ell\mid D,\ \ell\nmid f}\ell\). Inclusion–exclusion on \((n,D_0)=1\) writes the sum as
\[
 \sum_{e\mid D_0}\mu(e)\psi(e)
             \sum_{H/e\le h\le 1.1H/e}\psi(h).
\tag{5}
\]
For \(f<\sqrt{H/e}\), complete periods leave a remainder \(O(f)\). For the remaining \(f\), apply [Iwaniec, *On zeros of Dirichlet's L series*, Invent. Math. 23 (1974), 97–104, Lemma 6](https://doi.org/10.1007/BF01405163) to a primitive character at height \(t=0\). In the lemma the interval is \([X,X']\), \(\operatorname{rad}(f)^{100}<X<X'<2X\), and \(z_0=\log(f(|t|+3))/\log X\geq 1/2\); the bound is \(O_{z_0}(X^{1-\epsilon(z_0)})\) with a uniformly positive exponent on compact ranges of \(z_0\). The constants follow from the displayed \(\gamma_k,\epsilon_k\) in that paper's Lemmata 4 and 6. Here \(e\leq L^{B+A_0}\), \(X=H/e\geq P^{\delta/2}\), and \(z_0\) is bounded in terms of \(\delta\). This includes prime powers of \(2\) and mixed prime powers without any balanced-valuation assumption. The number of summands in (5) is at most \(D_0\leq L^{B+A_0}\). A power saving remains after summation.

It follows that, for any set \(\mathcal E\) of \(D\)-characters of size \(P^{o(1)}\) and any coefficients \(\beta_n\) supported within \(J_H\),
\[
 \sum_{\chi\in\mathcal E}\left|\sum_n\beta_n\chi(n)\right|^2
 \ll H\sum_n|\beta_n|^2.
\tag{6}
\]
Indeed the normalized Gram matrix of the vectors \(n\mapsto\chi(n)\) on **all** integers in \(J_H\) has diagonal bounded by an absolute constant and sums of absolute off-diagonal entries \(O(|\mathcal E|P^{-c_\delta})\). Use the operator norm of this matrix, or the dual Bessel inequality. No rough mask is put into the Gram entries: extend \(\beta_n\) by zero at any endpoints, nonunits or nonrough integers it excludes.

**Uniform long rough Möbius bound.** With \(z=\exp(L^{.24})\), every \(D\)-character, every interval \(J\subseteq[M,1.1M]\) with \(P^\delta\leq M\leq 2P\), and every \(|v|\le L^C\) satisfy
\[
 \sum_{\substack{m\in J\\ P^-(m)>z}}\mu(m)\chi(m)m^{iv}
 \ll_{B,A_0,\delta,C,E} M L^{-E}\qquad (E>0).
\tag{7}
\]

Here are the zero-free and reciprocal estimates behind (7). For a nonprincipal primitive character of conductor \(f\mid D\), Iwaniec's Theorem 2 gives a zero-free region except for a possible simple real zero of a real character, with width
\[
 \bigl[4\cdot 10^4\{\log\operatorname{rad}(f)+(v_f\log(2v_f))^{3/4}\}\bigr]^{-1},
 \qquad v_f=\log(f(|t|+3)).
\tag{8}
\]
For the normalization of (8), see also the explicit quotation of that theorem in [Banks and Shparlinski, October 2026, equation (2.5)](https://arxiv.org/html/2610.19597v1). The conductor of a primitive real character is at most \(4\operatorname{rad}(f)\): its odd part is squarefree and its 2-part is at most \(8\). Thus Siegel's classical theorem excludes a real zero closer to \(1\) than \(\gg_{B,A_0}L^{-1/4}\), on choosing its fixed exponent smaller than \(1/[4(B+A_0+3)]\). This is much wider than the strip used below. There is no reliance on a uniform effective lower bound for \(L(1,\chi)\). The character of conductor \(1\) uses the usual zeta-function Mertens estimate, rather than (8).

For precision, fix any desired Perron exponent \(J_0\), put \(T=L^{J_0}\), write \(H_0=1+\log L\), and take
\[
 u=c_0 L^{-1/2}H_0^{-2},\qquad
 \Theta=C_0 L^{3/4}H_0^2,\qquad
 \theta=\Theta^{-1},
\]
where \(c_0>0\) is small and \(C_0\) is large. Iwaniec's Theorem 1 gives \(\log|L(w,\psi)|\ll L^{1/4}+\log\operatorname{rad}(f)\ll L^{1/4}\) on discs of radius \(3u\) about \(1+2u+it\), \(|t|\le 2T\). Indeed \(v_f=O_{A_0,J_0}(L)\) throughout, and \(u\) is inside the growth region of that theorem (its width is \(\gg L^{-1/2}H_0^{-3/2}\)). Equation (8) and the real-zero bound show that throughout \(|t|\le 2T+1\) there are no zeros with \(\operatorname{Re}w>1-8\theta\), for sufficiently large \(P\).

We give the step to the reciprocal bound, since mere existence of this strip without growth control would not suffice. Use the standard local logarithmic derivative estimate, for example [Banks and Shparlinski, Lemma 8.1 of arXiv:1801.10276](https://arxiv.org/pdf/1801.10276), on the disc of radius \(3u\), taking interior radii \(2.2u,2.9u\). At the center the Euler product has modulus \(\gg u\). The error in approximating \(L'/L(s,\psi)\) by the sum of \((s-\rho)^{-1}\) over zeros within radius \(2.9u\) is therefore \(O(u^{-1}(L^{1/4}+\log(1/u)))=O(\Theta)\). Put \(s_*=1+\theta+it\). There the usual Euler-product estimate \(|L'/L(s_*,\psi)|\ll\theta^{-1}\) shows that the complex zero sum is \(O(\Theta)\), and the sum of the nonnegative real parts at \(s_*\) is likewise \(O(\Theta)\). For \(s=\sigma+it\), \(1-\theta/2\leq\sigma\leq1+\theta\), each zero in that disc has \(\beta\le1-8\theta\), so \(|s-\rho|\asymp |s_*-\rho|\) and
\[
 \left|\frac1{s-\rho}-\frac1{s_*-\rho}\right|
 \ll \frac{\theta}{|s_*-\rho|^2}
 \ll \operatorname{Re}\frac1{s_*-\rho}.
\]
This bounds \(L'/L(s,\psi)\) by \(O(\Theta)\). Integrate horizontally a distance \(O(\theta)\) from \(s_*\), where the Euler product gives \(|1/L(s_*,\psi)|\ll\theta^{-1}\). We obtain \(|1/L(s,\psi)|\ll\Theta\) throughout the segment, and on its right the same bound follows directly from the Euler product.

For a half-integer \(x\) in \([P^{\delta/3},2P]\), truncated Perron with \(\sigma_0=1+1/\log x\) gives the prefix sum of \(\mu(n)\psi(n)\) from \(1/L(w,\psi)\), with truncation error \(O(x\log x/T)\). Shift the vertical line to \(1-\theta/2\) at the same height \(T\). The vertical integral is \(O(x\Theta \log(2T)e^{-\theta\log x/2})\) and both horizontals are \(O(x\Theta/T)\). Since \(\theta\log x\gg_\delta L^{1/4}H_0^{-2}\), \(J_0\) can be set large enough for any specified logarithmic saving. For a real prefix use the half-integer with the same integer part. This proves \(\sum_{n\le x}\mu(n)\psi(n)\ll_A x L^{-A}\) uniformly on the stated length range, without a gap at small heights. For the principal primitive character the same estimate follows from the classical zeta zero-free region and ordinary Mertens bound.

For (7), all primes dividing \(D\) are \(<z\) by (3). Consequently an imprimitive character and its primitive inducing character agree on **all** integers in the rough support, including when the inducing character is principal. The exact convolution
\[
 \mu\,1_{P^->z}=\mu*1_{P^+\le z}
\]
follows by multiplying the local Euler factors at each prime. Twist both convolution factors by the inducing character. For \(x\asymp M\), the smooth factor \(j\le\sqrt{x}\) leaves inner prefix length \(x/j\ge P^{\delta/2}\); its total reciprocal weight is \(O(\log z)\). For larger \(j\) use the trivial inner bound \(x/j\) and Rankin:
\[
 \sum_{\substack{j>\sqrt x\\P^+(j)\le z}}\frac1j
 \le x^{-1/(2\log z)}
       \prod_{\ell\le z}(1-\ell^{-1+1/\log z})^{-1}
 \ll x^{-1/(2\log z)}L^{O(1)} .
\]
The product bound follows from \(\ell^{1/\log z}\le e\) and the prime reciprocal sum (treat the primes \(2,3\) separately). The tail is smaller than every fixed negative log power. Differences of prefixes and partial summation pay at most \(1+|v|\) on the \(M\)-interval and give (7).

## 2. High tag moments and the full projected major term

Use the same \(\alpha_m,\beta_n\), source boxes with \(MN\asymp P\), \(M,N\ge P^\delta\), prime bands, tag product shells \(a,c\in[Y,1.1Y]\), and arc denominators \(d\le L^{A_0}\) as in §1 of the prior near-full theorem. Thus \(\alpha_m=\mu(m)m^{iv}\) with the exact interval and rough/unit masks, \(\beta_n\) is arbitrary bounded by \(L^C\), and each tag is the product of one prime from each of \(K\) disjoint bands. The only facts about this shell used below are
\[
 \exp(c L^{.1})\le Y\le\exp(C_K L^{.2}), \qquad \#\{a\in[Y,1.1Y]\}\ll Y
\tag{9}
\]
and unique factorization of each tag into its \(K\) colors.

Let \(A_\chi=\sum_{a\in\mathcal T\cap[Y,1.1Y]}c_a\chi(a)\), \(|c_a|\ll_K1\), permitting any of the individual archimedean and small-character factors supplied by the separation. Set \(j=\lfloor\log(D/2)/\log(2Y)\rfloor\). Products of \(j\) tags are positive integers smaller than \(D\), so their congruence in character orthogonality forces literal equality. A product has at most \((j!)^K\) ordered decompositions into \(j\) tags, because the \(j\) prime occurrences of each color can only be assigned among those \(j\) positions. Cauchy's inequality on each exact product therefore gives
\[
 \sum_{\chi\bmod D}|A_\chi|^{2j}
 \le \varphi(D)(j!)^K\Big(\sum_a|c_a|^2\Big)^j .
\tag{10}
\]
This includes repeated occurrences with their multiplicities. For each fixed \(E\), Markov's inequality gives
\[
 \#\{\chi:|A_\chi|>YL^{-E}\}
 \le \exp\bigl(O_{E,K}(L^{.9}\log L+L^{.2})\bigr)=P^{o(1)}.
\tag{11}
\]
Indeed \(\log D-j\log Y=O(j+\log(2Y))\), the factorial and threshold cost is \(O_{E,K}(j\log L)\), and \(j=O(L^{.9})\). No individual estimate on a short prime sum modulo \(D\) is used.

We recall exactly the character coefficient needed from the prior calculation. If \(k=c mn-a r s'\), the projection at rational frequency \(b/d\) is \(1_{P\mid k}\,e_d(bk/P)\). On units modulo \(D\), put \(u=c mn/(a r s')\), and first split \(a r s'\bmod d\). The projection is supported on \(u\equiv1\bmod P\), with absolute value one on that subgroup. Its multiplicative Fourier coefficients are consequently bounded by \(1/\varphi(P)\). This bound applies also if \((d,P)>1\), since the unit-group reduction to modulus \(P\) is onto. The remaining finite terms have total cost \(L^{O(A_0+1)}\) in coefficients, with possible low-character twists of individual variables. The real smooth compact factor on each major arc separates into product weights with \(L^{O(A_0+1)}\) total transform mass, all retained logarithmic frequencies \(\le L^{C_1}\); the cut error is arbitrarily log-small before projection expansion, as in the previous proof. In this step on \(P\mid k\), each fixed pair \(a,c\) and product \(mn\ll P\) allows \(O(1)\) values of \(rs'\ll P\), the exact normalization behind the cut error. All variables are units on these arcs because the endpoints' integer factors are \(z\)-rough and target units, and the tag primes exceed \(L^{A_0}\).

Thus a separated integrand is bounded by a sum with absolute terms of the form
\[
 \frac{1}{\varphi(P)}\sum_{\chi\bmod D}
        |A_\chi C_\chi B_\chi B'_\chi|,\qquad
 B_\chi=M_\chi N_\chi,\quad
 M_\chi=\sum_m\alpha'_m\chi(m),\quad N_\chi=\sum_n\beta'_n\chi(n).
\tag{12}
\]
The other endpoint \(B'_\chi\) has possibly different weights, twists, conjugations and frequencies with the same budgets. The usual divisor-square bound and character orthogonality over the products \(mn\ll P\) give
\[
 \frac1{\varphi(P)}\sum_{\chi\bmod D}|B_\chi|^2
 \ll dP L^{O_C(1)}
\tag{13}
\]
for each endpoint. This is the **full** projector normalization; no factor \(\varphi(P)\) is discarded.

Let \(\mathcal E\) be the union of the two exceptional sets (11). Outside \(\mathcal E\), use \(Y^2L^{-2E}\) for the two tag factors in (12) and Cauchy with (13). On \(\mathcal E\), use the trivial \(O_K(Y^2)\) for the tags. Apply (6) on this set, with its fixed low-character twist or conjugation, to the arbitrary \(n\)-coefficients on each endpoint. This gives \(\sum_{\chi\in\mathcal E}|N_\chi|^2\ll N^2L^{2C}\), while (7) gives \(\sup_\chi |M_\chi|\ll_A M L^{-A}\). Hence the contribution of the exceptional set to (12) is at most
\[
 \ll_{A,K} \frac{Y^2}{\varphi(P)}P^2 L^{-2A+2C}.
\tag{14}
\]
Because \(P/\varphi(P)\ll 1+\log L\), this has an arbitrary logarithmic saving relative to \(Y^2P\). It is important to use the restricted Bessel bound here, not a factor \(\#\mathcal E\) multiplying an individual Möbius bound.

Take \(E,A\) large after the fixed arc and separation costs. The major arcs have measure \(O(L^{3A_0}/Y)\), so the full projected major term is \(O_R(PY L^{-R})\) for every prescribed \(R\). The prior projected-minor comparison yields the same bound for the original reflected mean square. The choices of \(K\) and of the separated bands remain those of that comparison; the extra constants above only affect the sufficiently large threshold and log-saving choices, not the size of the auxiliary prime bands.

## 3. Physical extraction and scope

This proves exactly the mean-square estimate required in the prior near-full cofactor theorem, now with (3) in place of its conjectural/conditional high-conductor input. Its Vaughan Type II application uses \(\mu\) on the long indicated \(m\)-slot, so (7) supplies that application rather than an estimate for arbitrary \(\alpha_m\). For the unsigned and signed counts the physically extracted weight is
\[
 F_b(y)=\sum_{\substack{y=sq,\ q>P/S\ \mathrm{prime}\\(s,P)=1}}
              b(s)\log q/L,\qquad b(s)=1\ \text{or}\ (-1)^{\Omega(s)}.
\]
It is bounded by one; the signed version satisfies \(F_b(ah)=(-1)^K F_b(h)\) on a \(K\)-tag family because Liouville is completely multiplicative, whether or not a marked prime repeats in \(h\). This sign has modulus one and does not change (10), (12) or the Cauchy bounds. The actual \(q\)-prime Type I argument and two-form upper sieve unweighting in §§2–3 of that proof need no zero-free hypothesis. They give the two equal main terms in (1) with the same eventual \(P\)-range. For (2) use the already stated fixed-\(K\) extraction in its §4: after extracting \(a\) the residual is the actual prime indicator times \(\log q/L\), and the tags and the unique near-full factor are in disjoint ranges.

The cited prior near-full theorem concerns the same counting question for unrestricted even targets under a high-conductor zero-free input. The present theorem replaces that input only on a structured target family, retaining the actual two primes and an extra multiplier. For comparison, [Lü, Wang and Wu, arXiv:2610.20242v2](https://arxiv.org/html/2610.20242v2), Theorem 1 treats a fixed shift of a prime for ordinary Möbius cancellation; their Remark 3 discusses moving shifts conditional on a zero-free hypothesis. Neither ordinary shifted parity nor the Burgess/Postnikov estimates alone give (1), where there is a second actual prime of size \(P^{1-o(1)}\). No claim is made about priority or general moving-shift estimates.
