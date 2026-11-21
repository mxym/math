# Whole marked compensation, with a strictly negative net on actual rows

Use the exact fixed-target \(N=2x,\ n=sq\in(x/2,x],\ m=N-n,\ (n,N)=1\) and genuine \(\mathcal Q_i\) families of [AdjustedFirstTaperAllRank.md](AdjustedFirstTaperAllRank.md). Write \(w(s,q)=W_s(q)D_B(q)/\log q\), exactly positive and bounded on each, \(M_N=\mathfrak S(N)x/(2L)\), \(L=\log x\). Their weighted physical source sizes are \(A_i(x,N)=(I_i+o(1))x/(2L)\) with \(I_i\) as previously. Use the **same prime band** as the actual Richert reserve:
\[
       \mathcal P_x=\{p\text{ prime}:x^{.04}<p<x^{.09}\},\qquad
       k(m)=\#\{p\in\mathcal P_x:p\mid m\}.
\]
Let \(E_K(m)=\Lambda(m)-\log m\sum_{d\mid m}\mu(d)K(\log d/\log m)\), with \(K(t)=0\) for \(t\ge .03\), \(K(0)=1\), and \(K'(0)=-1\). Take \(K\) smooth, equal to \(1-t\) near \(0\), as in [FixedDetectorFiniteRoughWindow.md](FixedDetectorFiniteRoughWindow.md), or take the fixed finite-smoothness polynomial version specified in §3 below. These are genuine whole-profile replacements of the original \(C\) with unchanged weighted sum up to \(o(M_N)\); no replacement is claimed to be individually zero after restricting to the marked rows.

Set \(H_0=\log(9/4)\) and
\[
 \begin{split}
 \Phi(k)&=\sum_{h=1}^5 \lambda_h\binom{k}{h},\\
 (\lambda_1,\lambda_2,\lambda_3,\lambda_4,\lambda_5)
      &= (2497/3430,\ -782/1715,\ 1119/6860,\ -33/980,\ 11/3430),\\
 \Theta&=\sum_{h=1}^5\lambda_h H_0^h/h!.
 \end{split}
\tag{1}
\]
The [finite rational certificate](check_whole_marked_compensation.py) gives \(0\le\Phi(k)\le1\) on all integers \(0\le k\le25\) and \(.454<\Theta<.455\). For sufficiently large \(x\), \(k(m)\le25\) throughout \(m<3x/2\), since 26 such distinct primes give a product \(>x^{1.04}\). Thus the whole physical weight splits **exactly** into the two nonnegative fractions \(\Phi(k(m))\) and \(1-\Phi(k(m))\).

Uniformly in large even \(N\), for **all reflected ranks**,
\[
 \boxed{\quad
   \sum_{\mathcal Q_i} w(s,q)\Phi(k(m))E_K(m)
                   =-(\Theta I_i+o(1))M_N .
   \quad}
\tag{2}
\]
This pays the whole marked fraction, including its genuine positive compensation. Its strictly negative net is \(>.023M_N\) or \(>.014M_N\) in magnitude in the two profiles. It does not bound the remaining unmarked fraction with weight \(1-\Phi\) or the other quotient profiles.

## 1. Actual factorial moments through five marks

For \(1\le h\le5\) and each marked product \(F=p_1\cdots p_h\) of distinct primes in \(\mathcal P_x\), consider the literal constraint \(F\mid m=N-sq\). The detector divisors have \(d\le m^{.03}<x^{.0301}\) for large \(x\). Hence \((F,d)=1\) **always**; in particular its residue modulus is the product \(Fd\), not a model product in place of an lcm. If \((F d,N)>1\) there are no actual rows on unit support. Otherwise the class is \(N\bmod Fd\) reduced, and \(Fd<x^{.481}\). There is unique recovery of the unordered \(F\) from the modulus and \(h\) because all its primes exceed \(x^{.04}\), above every \(d\)-factor; this gives the absolutely summed full-scale BV discrepancy on the real prime \(s\) and the independent \(1\)-bounded genuine \(q\)-mask. No weight \(x^{o(1)}\) is inserted into a log saving. The usual true logarithm, \(w\) and central product endpoints are paid by the same smooth separation / log-fine rectangles as in the finite detector note. The support gate in \(K(\log d/\log m)\) depends on \(m\), not on either source coefficient; at a fixed modulus its variation is bounded by \(K\)'s fixed derivatives, with the uniform subhalf slack handling the short-divisor data. 

In the reduced main at fixed actual \(n=sq\), the constraints are \((F d,Nn)=1\). Omit proper prime powers in \(\Lambda(m)\) at total power-small cost; a true prime \(m\asymp x\) cannot have such an \(F\), while a proper prime power has at most one distinct mark, so it costs no larger mark multiplicity. The short detector main for the **minus** of its log-weighted divisor sum, at fixed \(F,n\), is
\[
 -\frac{\log m}{\varphi(F)}
       \sum_{(d,Nn)=1}\frac{\mu(d)}{\varphi(d)}
                   K(\log d/\log m)
          =-\frac{\mathfrak S(Nn)+o(1)}{\varphi(F)} .
\tag{3}
\]
For smooth \(K=1-t\) near zero the error here has arbitrary negative log powers, by the constant and log moments of [Huang--Li, Lemma 1](https://arxiv.org/pdf/2005.03811) and partial summation over the difference supported away from zero. For the fixed polynomial germ of §3 use the finite higher moments proved in [AdjustedPolynomialRankAbsorption.md](AdjustedPolynomialRankAbsorption.md); every higher term is still \(o(1)\) uniformly at the actual mask \(Nn\). The detector local derivative \(K'(0)=-1\) is essential. There is no \(p\mid d\) term from any mark to cancel this first moment: exactly those divisors vanish by the support gap.

At fixed actual \(n\), \(\mathfrak S(Nn)/\mathfrak S(N)=1+O(x^{-.010})\) since all its prime factors are \(>x^{.010}\). Exclude \(p\mid Nn\) from the \(F\)-sum at power-small harmonic cost: any excluded marked prime is \(>x^{.04}\), the number of prime factors of \(Nn\) is \(O(L)\), and the other \(h-1\) reciprocal choices have bounded total mass. Thus
\[
 \sum_{\substack{F=p_1\cdots p_h,\ p_j\in\mathcal P_x\ {\rm distinct}\\(F,Nn)=1}}
       \frac1{\varphi(F)}
       =\frac{H_0^h}{h!}+o(1)
\]
uniformly in \(n,N\), by ordinary prime reciprocals on the fixed polynomial band; the repeated-prime correction in the \(h\)-th product is power-small, and \(F\) here is unordered. Since \(\sum_F1_{F\mid m}=\binom{k(m)}{h}\), (3) proves
\[
 \sum_{\mathcal Q_i}w(s,q)\binom{k(m)}h E_K(m)
                   =-\left(\frac{H_0^h}{h!}\,I_i+o(1)\right) M_N ,
                  \qquad 1\le h\le5 .
\tag{4}
\]
Combining these **actual signed** factorial moments with the finite bounded polynomial (1) proves (2) at every sufficiently large even target, with no pointwise independence claim or uncontrolled high-multiplicity tail. The polynomial was chosen merely as a feasible rational certificate, not as a claimed optimal value.

## 2. Compensation and the actual negative magnitude on the same mark

On the exact Richert chamber \(\mathcal C\) of [ActualRichertNegativeReserve.md](ActualRichertNegativeReserve.md), the mark \(p\) is unique, so \(k(m)=1\), and every factor of \(m\) exceeds \(x^{.04}\). The compact detector therefore has \(d=1\) only and \(E_K(m)=-\log m\) exactly. Its actual fixed-target occupancy, inequality (5) of that note, yields
\[
  \sum_{\mathcal Q_i,\ m\in\mathcal C} w(s,q)\Phi(k(m))E_K(m)
      \le -\bigl(\Phi(1)\,1.57\cdot .81\, I_i+o(1)\bigr)M_N
      < -(.9257\, I_i+o(1)) M_N.
\]
This is not added as a separate negative reserve to the whole marked fraction. Rather, subtract it from (2). Because \(\Theta<.455\), the exact other marked contribution satisfies, for all sufficiently large even \(N\),
\[
          \sum_{\mathcal Q_i,\ m\notin\mathcal C}
                         w(s,q)\Phi(k(m))E_K(m)
                                     \ge .47 I_i M_N .
\tag{5}
\]
This is an actual **signed positive compensation** on the same fixed-target equation, not a dyadic-average positivity result. The selected negative \(>.9257I_i\) has already paid it in the net \(-\Theta I_i\). Every positive composite term in (5) must contain at least one factor below \(m^{.03}\), outside the marked band: otherwise again \(d=1\) only and \(E_K=-\log m\). Proper prime powers have a negligible exception as usual.

The exact matched net is consequently available as a reserve when bounding the remaining *fraction*:
\[
 \sum_{\mathcal Q_i}w(s,q)E_K(m)
    =-(\Theta I_i+o(1))M_N
       +\sum_{\mathcal Q_i}w(s,q)(1-\Phi(k(m)))E_K(m).
\]
The last term is not bounded here. In particular the equation cannot be used with the full richter reserve in place of \(\Theta I_i\) without paying the other marked rows; (5) proves one genuine obstruction to doing so.

## 3. The compensated marked contribution can be forced into higher ranks

Given any fixed \(R_0\ge4\) and \(\delta>0\), choose the polynomial detector of [AdjustedPolynomialRankAbsorption.md](AdjustedPolynomialRankAbsorption.md) with \(j\) sufficiently large odd, \(\epsilon<.01\), and then choose its fixed flattening parameter sufficiently small, to give actual bounded-rank positive part at most \(\delta M_N/2\). Use its exact whole replacement \(E'_j\) of [AdjustedFirstTaperAllRank.md](AdjustedFirstTaperAllRank.md), with the full first taper on \(t<1/2\). The value of (1) here is unchanged by this choice.

Choose a fixed smooth cutoff \(\chi(t)\) equal to \(1\) on \(0\le t\le .01\), zero on \(t\ge .03\). Define the **fixed compact** scalar kernel
\[
     K(t)=\frac{\chi(t)}{2j}(1-2t)_+^j
                +\left(1-\frac1{2j}\right) f_\rho(t/\epsilon)
                \qquad(t\ge0).
\]
Its polynomial germ at zero has \(K(0)=1,K'(0)=-1\); it has no support at the mark primes. Even if the plateau \(f_\rho\) is only bounded-variation, this is sufficient for the BV and principal calculations of §1. It is only the difference from \(E'_j\) that uses Fourier control here. That difference has kernel \((1-\chi(t))(1-2t)_+^j/(2j)\) supported on \([.01,1/2]\), with fixed compact extension by zero to \(t<0\). Its \(L^1\) norm and fourth derivative \(L^1\) norm are \(O(j^3(.98)^{j-4})\). The all-rank Fourier--Henriot upper of §2 of the first-taper note, including the genuine \(\log m/L\) dilation, thus pays its whole absolute cost \(O(j^3(.98)^{j-4}M_N)\), with a constant independent of \(j\). Choose \(j\) large enough for this cost to be \(<\delta M_N/2\). The analog of the bounded-rank positive conclusion for \(E'_j\) therefore holds for this \(E_K\) with allowance \(\delta M_N\). The finite log moments and the actual support give the required entire profile normalization independently.

Since \(\mathcal C\) is supported in \(\Omega(m)\le4\), (5) and this actual bounded-rank positive bound imply
\[
 \sum_{\mathcal Q_i,\ \Omega(m)>R_0} w(s,q)\Phi(k(m))E_K(m)
                         \ge (.47 I_i-\delta)M_N.
\]
Thus for a detector with the prescribed low positives removed, the compensating **high-rank marked** sum is genuinely positive, but always paid in the exact whole net (2). The detector depends on the prescribed \(R_0,\delta\); no interchange of limits is implied. Nothing here controls the unknown remainder with \(1-\Phi\), or proves a pointwise Goldbach prime-pair estimate.
