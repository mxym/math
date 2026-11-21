# Whole genuine reverse columns on positive reflected triprimes

Use \(N=2x,L=\log x,n=sq\in(x/2,x],m=N-n\), with \(s\) a true prime in \(x^{.10}<s<x^{.14}\) and \((n,N)=1\), and the literal \(W_s(q), C(m)\) of [PositiveTriprimeReverseJainTube.md](PositiveTriprimeReverseJainTube.md). The source \(m=p_1p_2p_3\) has three actual distinct ordered primes, on boxes below exponent \(.41\) and with every pair above exponent \(.59\) in the high tube, or below .45 and every pair above .55 in the intermediate box below. In either event \(C(m)=+\log m\) exactly. The reverse row has \(q=rkh\) an integer with
\[
        r>U_q,\ k>V_q,\qquad \mu(r)\Lambda(k)
\]
as the actual original signed coefficient. If the redundant product test \(r k>E\) is written separately, take \(E=U_qV_q\) for each opening, including the changed opening in B. All other tests are unchanged. We consider **one column selection at a time**; neither result will be added across intersecting selections.

### A. Original cutoffs, a contiguous intermediate scale

Take the original \(U_q=x^{.070},V_q=x^{.010}\), and the fixed independent reflected exponent box
\[
   |\log_x p_1-.179|<10^{-4},\qquad |\log_x p_2-.379|<10^{-4},
 \qquad \log_x p_3=.442+O(2\cdot 10^{-4}+1/L).
 \tag{1}
\]
Uniformly at each fixed even \(N\), each of the following **whole** selections has signed sum \(O_D(x L^{-D})\) for every fixed \(D\), against \(C(m)W_s(q)/\log q\):
* all \(r>U_q\) and \(V_q<k\) with \(s k\le x^{.486}\);
* all \(k>V_q\) and \(U_q<r\) with \(s r\le x^{.546}\).

Each line may have an additional fixed smooth geometric test depending on \(s,m\) and its marked label \(k\), respectively \(r\), but **not** on the variable being recombined. No upper cutoff on the original \(A=srk\) is used. These are closed subfamilies of the original reverse row, not merely changes of parameters in another opening.

### B. Higher marked scales with a changed but exactly matching opening

In the literal high-Jain tube of [PositiveTriprimeReverseJainTube.md](PositiveTriprimeReverseJainTube.md), use \(\rho=\log_x(s k)\) in a \(k\)-selection and \(\rho=\log_x(s r)\) in an \(r\)-selection, rather than \(\log_x(s r k)\). Use its open support (2), with profiles \(a(\rho),b(\rho),c(\rho)\) as defined there; its constants \(\nu,\lambda,w\) stay fixed. Set **new** reverse cutoffs \(U_q=V_q=x^\epsilon\), with \(0<\epsilon<\lambda/100\). In either selected marked column the complete original signed sum over the *other* reversed label and the true free \(h\) is \(O_D(xL^{-D})\), at every fixed even target. The smooth \(\Phi(\rho,\log_xp_1,\log_xp_2)\) is retained.

In B specifically, statements refer to the changed reverse decomposition. Its full true-prime row has the same positive reference \(\mathcal R_{\mathcal B}\) as in the cited tube note (ordinary small moduli give the same finite harmonic centers for any two fixed polynomial cutoffs with \(s U_q V_q<x^{.5-\delta}\)). The higher marked column theorem is not asserted for all \(r> x^{.070}\) or \(k>x^{.010}\) of the *old* decomposition on that high tube. In A, by contrast, the stated bounds use the original cutoffs.

## 1. Two literal reassemblies, each preceding any original high-product cut

In a \(k\)-column, fix \(s,k,m\). The physical congruence \(m\equiv N\bmod s k\) makes \(v=(N-m)/(s k)\) a positive integer. On either selected range its scale is at least \(x^{.37+o(1)}\), in particular \(v>1\). The flag \(k>V_q\), the actual coefficient \(\Lambda(k)\), and all support restrictions used for the column are independent of \(r,h\). Thus, *before any cut on \(s r k\)*,
\[
 \sum_{\substack{r h=v\\r>U_q}}\mu(r)
       =-\sum_{\substack{r'\mid v\\r'\le U_q}}\mu(r').
 \tag{2}
\]
The right side uses only literal new moduli \(s k r'\) and their reduced residues \(N\bmod s k r'\). The weight \(W_s(q)/\log q\) is a smooth function of the physical \(m,s\); it does not depend on \(r'\). No replacement of \(\Lambda(k)\) by an integer density has been made.

In an \(r\)-column fix \(s,r,m\), write \(v=(N-m)/(s r)\) on its physical congruence, and use
\[
 \sum_{\substack{k h=v\\k>V_q}}\Lambda(k)
      =\log v-\sum_{\substack{k'\mid v\\k'\le V_q}}\Lambda(k').
 \tag{3}
\]
The outer original \(\mu(r)\) remains. The first modulus is \(s r\), the others are \(s r k'\). The first term's extra \(\log v=\log((N-m)/s)-\log r\) splits exactly. It will be handled by partial summation or by separating its two summands, not discarded. \(\Lambda(k')\) retains its actual prime-power labels. Equations (2) and (3) are not used after requiring the original product \(A\) or the free \(h\) to be in a proper subinterval.

## 2. Contiguous actual local distribution for the projected moduli

For A, after either reassembly all projected moduli have size \(\le x^{.556}\), by the exact endpoint calculations \(.486+.070=.556\) and \(.546+.010=.556\). On (1), generalized full-scale BV from Maynard I, Lemma 8.9, gives absolute distribution to \(x^{.499}\) on a prime slot and the independent product of the other two. For \(R\ge x^{.499}\) use [Jain's arXiv preprint 2611.21136v1, Proposition 3](https://arxiv.org/html/2611.21136v1#S3.SS1), on the three true prime slots with exponents \(u=.179,\ell=.379,b=.442\) at full scale \(x\), \(a_1=N,a_2=1\), \(\theta=7/32\). The center rails on \(.499\le\rho=\log_xR\le.556\) have:
\[
\begin{array}{ll}
 u+\ell=.558<2/3,& \ell=.379<b=.442<.499,\\
 \rho\le .556<.558=u+\ell,& 2u+3\ell-1=.495<.499,\\
 7u+4\ell+\theta=2.98775<2+2(.499)=2.998,&\\
 (7-4\theta)u+(4-\theta)\ell = 2.52946875
       < 2-2\theta+(2+\theta)(.499)=2.66965625.&
\end{array}
 \tag{4}
\]
All margins survive the indicated exponent box, dyadic factors, and fixed small theorem reserves. The physical projected moduli can be any integers with the stated size, not just ones with an extra known factorization. Thus this application joins the ordinary full-scale BV range to \(.556\) without a gap **for this particular actual triprime profile**. It is not an arbitrary-sequence level.

For B, after reassembly each new modulus has exponent \(\rho+t\), \(0\le t\le\epsilon\), where \(\rho\) is that of the genuine marked product \(s k\) or \(s r\). Use [Jain's different Hexagon preprint 2611.00530v1, Proposition 2](https://hexagonmath.org/pdf/2611.00530v1) on the same true prime slots \(a(\rho),b(\rho),c(\rho)\) as the high-tube theorem. Increasing its modulus exponent by \(t\) preserves all rails there: it changes the positive lower difference \(a+b-\rho\) from \(\lambda\) to \(\lambda-t> .99\lambda\), and makes its diagonal and complementary-divisor inequalities easier; \(M_{\rm slot}\le R\) also becomes easier. The genuine profile widths have the same common strict margins used in that theorem. This controls every possible projected modulus in a selected whole column, including \(r'=1\) or the log term of (3). It does not control arbitrary \(s k r'\) with larger \(r'\) on the same profile.

These uses of the two preprints are as stated in their exact source propositions, not as applications of their published smooth-number corollaries to arbitrary primes. In both cases take the character cutoff \(D_0=L^F\); ordinary SW on a genuine polynomial prime slot removes small nonprincipal characters. This yields the ordinary centered error \(\Delta_A\) unweighted with arbitrary log reserve. Attach the signed modulus decompositions and weights *after* centering via the same divisor-moment Cauchy as in the triprime tube:
\[
 \sum_A \tau(A)^{2j}|\Delta_A|
 \ \ll\ \sum_{x/2<m<1.6x}\tau(m)^C\tau(N-m)^C
               +x\sum_A \tau(A)^{2j}/\phi(A)
 \ \ll\ xL^C .
\]
Source boxes are confined to \(m<1.6x<N\) so that no difference zero occurs. An elementary pointwise \(x^{o(1)}\) divisor factor is not inserted into a log saving. Prescribed \(s\) and either long label can have common base primes with the short label; all decompositions are counted in the displayed divisor envelope.

In A the reflected factor boxes are fixed and the inequalities on \(s k\) or \(s r\) stay in the external labels. In B the test is coupled to the **marked product** \(s k\) or \(s r\), not to the original \(A\) or to an independently varied \(m\)-slot. Cover its compact exponent support by finitely many boxes on which all the projected modulus exponents fit the rails, then separate the smooth geometry by Fourier in the normalized log coordinates, as in the earlier tube. For the exact central product and physical \(W_s(q)/\log q\) use its same relative log-fine mesh and separated Taylor expansion in \(\log((N-m)/x)\). This leaves genuine prime indicators and independently smooth/log-weighted coefficients. No twist alters the primality label of a source factor or of \(k\).

## 3. The principal terms and the comparison with the old high tube

In (2) the exact reduced mean at fixed \(m,s,k\) has the signed sum
\[
        -\sum_{\substack{r'\le U_q\\(r',Nm)=1}}
                             \mu(r')/\phi(s k r'),
\]
and the original marked selection is independent of \(r'\). The premise \((s k,Nm)=1\) is necessary, otherwise this contribution is zero. Factor \(1/\phi(s k)\), then expand the exact overlap multiplier \(\prod_{p\mid(s k,r')}(1-1/p)\) into at most four divisors of \(\operatorname{rad}(s k)\) with coefficient \(\mu(d)/d\). For \(d\le\sqrt{U_q}\) set \(r'=d v\) with true \((v,d)=1\). The finite coprime \(\mu/\phi\) constant moment at \(U_q/d\ge\sqrt{U_q}\) gives arbitrary log reserve (its mask is \(dNm\)). For \(d>\sqrt{U_q}\) use \(1/(d\phi(d))\) and the trivial harmonic sum to get a power-small bound. This keeps the literal negative sign of (2); the principal has no nonzero main to subtract.

For (3) fix the possible short \(k'\), or take \(k'=1\) for its free-log piece. The same overlap calculation now applies to the actual outer \(\mu(r)\) as \(r\) varies over a polynomial interval beginning at or above \(U_q\). The smooth \(\rho=\log_x(s r)\) selector, any fixed endpoint, and the extra \(\log(q/r)\) have bounded variation up to log powers. At \(d\le\sqrt{U_q}\) both finite \(\mu/\phi\) moment endpoints stay polynomial, and for larger \(d\) the harmonic tail is power-small as above. The remaining \(s,k\) or \(s,k'\) weights have harmonic log cost. Thus all principal terms in either whole-selected column are \(O_D(xL^{-D})\), including the exact \(\log v\) part.

In B the old \(k\)-column at \(U_q=x^{.070}\) differs from the new one by the literal additional short-after-switch sum over \(x^\epsilon<r'\le x^{.070}\) (with its sign from (2)). The part of that additional interval still inside the same strict dispersion chart can also be centered, but the rest can extend projected exponents to \(\rho+.070\) and is **not** covered. The same qualification applies to the old \(r\)-column and its additional \(k'\) interval. This is why B uses a changed reverse decomposition; A supplies a separate original-cutoff result in a lower marked range. No two column bounds are combined without accounting for their genuine intersecting \(r,k\) terms.

These whole columns reach original \(A=srk\) well above \(5/8\): the high projected theorem is used only after exact divisor recombination. It makes no assertion for the near-equal positive triprime chamber (where the actual independent Jain slots are absent), the original complement's required upper bound, or the binary prime-pair term.

## Related reductions

[WholeReverseColumns.md](WholeReverseColumns.md) and [FactoredWholeReverseColumns.md](FactoredWholeReverseColumns.md) reassemble the high coefficient on the opposite side and use other actual modulus families. [Arneth's October preprint](https://zenodo.org/records/23504447) discusses exact Vaughan reassembly and the signed fixed-target problem, with the required balanced estimate left open. The [GoldbachResearch Lean project](https://github.com/TamakoHe/GoldbachResearch) also groups actual Vaughan coefficients before taking absolute values. The present bounds use the indicated three independently prime factors, and do not estimate the full fixed-target signed correlation.
