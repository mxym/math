# Affine reflected Möbius correlations and squarefree signs at polylogarithmic-radical targets

Write \(\rho(P)=\varphi(P)/P\). Fix \(B>0\) and a compact interval \(J\) of positive length inside \((0,1)\). For \(f\in\{\mu,\lambda\}\) and \(g\in\{\mu,\lambda,\mu^2,1\}\), uniformly at all individual integers \(P\) with \(\operatorname{rad}(P)\leq(\log P)^B\),
\[
  \sum_{n\in PJ}f(n)g(P-n)=o_{B,J}(P).
  \tag{1}
\]
In particular, writing \(L=\log P\), the four pairs of Liouville signs each occur \(|J|P/4+o_{B,J}(P)\) times in this interval. The four pairs of nonzero Möbius signs each occur
\[
 \frac{|J|P}{4} \prod_{\ell\ {\rm prime}}
 \left(1-\frac{2-1_{\ell^2\mid P}}{\ell^2}\right)+o_{B,J}(P)
 \tag{2}
\]
times. The results also hold over the whole interval \(1\leq n<P\), with \(|J|=1\), by trimming first and then taking the two limits in order. No zero-free hypothesis beyond the cited unconditional results is assumed, and the eventual thresholds may be ineffective.

Here is a useful affine unit version. Fix \(D_0>0\). Let \(a,b\leq L^{D_0}\) be positive coprime integers, \((ab,P)=1\), and let \(T\) be an integer with \(\operatorname{rad}(T)\leq L^{D_0}\). Then
\[
 \sum_{\substack{a m+b n=P,\ a m\in PJ\\(mn,P)=1}}
     f(m)g(n)\,1_{(m,T)=1}^{i}\,1_{(n,T)=1}^{j}
   =o_{B,D_0,J}\bigg(\frac{\rho(P)P}{ab}\bigg),\qquad i,j\in\{0,1\}.
 \tag{3}
\]
The power \(i=0\) or \(j=0\) means that the corresponding mask is absent. In particular this prices fixed small-cofactor slices of the actual additive double Möbius inversion. There is no claim at arbitrary targets or for summation over a growing polynomial range of \(a,b\), and no binary-prime lower bound.

The analytic input is the [full-target projected minor comparison](../target_slope_switch/Proof.md), the [small-radical projected major proof](../small_radical_projection/Proof.md), and their primary input [Jiang–Lau–Lü v2, §§5–6](https://arxiv.org/html/2611.12467v2). We explain exactly which modifications of the supports and rational arcs are needed. In particular the argument does not assume the existence of any prime pair at \(P\).

## 1. A reflected bilinear packet with one genuine prime slot

In this section \(X=P\) is the target and the products in a bilinear packet are in a fixed central interval inside \((0,X)\). Both factor lengths are \(\geq X^\delta\) and their product is \(\asymp X\), for fixed \(\delta>0\). Use the existing separated \(K\) bands of actual primes, with reciprocal masses \(V_\nu\in[1/4,1/2]\), union \(\mathcal B\), and one prime per band in each tag \(u\in\mathcal A\); put \(\mathcal V=\prod_\nu V_\nu\). All tag labels are units modulo \(X\), lie between \(\exp(cL^{.1})\) and \(\exp(2L^{.2})\), and their product at any retained shell \(u\asymp Y\) is smaller than \(X^\varepsilon\) for every fixed \(\varepsilon>0\) eventually.

Both bilinear factors are required to be units modulo \(X\) and to avoid **all** primes of \(\mathcal B\). In place of the usual full \(z\)-roughness of both slots, require one slot to consist of literal primes \(\geq X^\delta\), and the other to have the shape \(A v\) with a fixed \(A\leq L^{D_0}\), coefficient \(f(v)\) times the specified bank-avoidance, target-unit, possibly extra \((v,T)=1\), interval and bounded log-frequency factors. The prime slot may have any bounded (or fixed-polylogarithmically bounded) coefficient. Let \(H(h)\) be any separately specified function of modulus at most one. Then, for every fixed \(D>0\), with \(K\) sufficiently large after the requested saving and the fixed packet data,
\[
 \frac{1}{\mathcal V}\sum_{X-\ell_1\ell_2=u h,\ u\in\mathcal A}
 \alpha_{\ell_1}\beta_{\ell_2}H(h)=O(XL^{-D}).
 \tag{4}
\]
The bound is uniform in the admissible bank, including which bands are chosen in their allowed ranges, and in \(A,\operatorname{rad}(T)\leq L^{D_0}\). A polylogarithmic number of packet rectangles or smooth shell cutoffs is harmless, with the requested logarithmic saving enlarged first. No ordinary Bombieri–Vinogradov input is needed for (4).

**Minor comparison with the weaker support.** In a shell write \(k=c m n-u r s\) for the determinant expression, using \(u,c\) for the two selected tags. With shared label product \(D\), the physical endpoints remain \((D c m,s)\) and \((D u r,n)\). On the good part \(D u c\) is squarefree. The bank-avoidance on the actual four factors gives
\[
  (D c m,s)=(m,s),\qquad (D u r,n)=(r,n)
\]
where the left sides here denote the positive gcds of the displayed coordinate pairs. If \(k=0\), coprimality of \(c,u\) would give \(u\mid mn\), impossible by the same bank-avoidance. In the projected summation \(X\mid k\); also \(|k/X|\leq5Y\), and all four factors and label primes are units modulo \(X\). Each endpoint gcd divides \(k\), is coprime to \(X\), and consequently divides \(k/X\). In each gcd one of the two arguments is a literal prime \(\geq X^\delta>5Y\), irrespective of whether the prime slot is first or second after ordering the two factor lengths. Therefore both endpoint gcds are one. The possibility that the nonprime slot has small prime factors outside the bank causes no exception here. Primitivity and target units now give the canonical index-\(X\) lattice frames in the projected comparison exactly as before.

The input vector in JLL (5.14) is still constant on each physical tuple fibre: if dividing the first coordinate by the selected labels leaves a nonzero coefficient, the quotient avoids every bank prime, so the selected tuple contains exactly all bank factors of that coordinate, each to exponent one. The other tuples in that fibre are only reorderings of it. This reasoning uses avoidance of the **entire** bank, not just avoidance of the sampled tags. The norm in JLL (5.14)–(5.16) is bounded as before by summing over ordered tuples first and using the same reciprocal weights. JLL (5.5)–(5.10), the geometry, separation, moment transfer and real estimates only use this fibre-constancy, the endpoint primitivity and target-unit restrictions, labelled states and numeric packet sizes; thus the good part of the projected comparison is unchanged.

For the bad repeated-label part, there is no appeal to full roughness. For fixed tags the exact \(h\) estimates use the divisor-square moment in the actual progression \(X-u h\) (a reduced class modulo the tag), as in the final paragraph of the projected minor proof; dropping bank-avoidance only helps that upper bound. In the projected part \(X\mid k\) determines at most one product \(rs<X\) from \(mn<X\) and each fixed pair \(u,c\), since the tags are target units. Thus the same absolute divisor-square bound and the original small reciprocal mass of common or repeated labels apply. The geometric separation error uses the same primitive frames and weighted ordered state count. We still obtain \(Q_Y-\mathcal M_X=O(XY L^{-D'})\) for every fixed \(D'\), with \(K\) large enough, in the identical normalization.

**Rational major arcs without full roughness.** The major projection at an arc with denominator \(d\leq L^{A_0}\) is \(1_{X\mid k}e_d(b_0 k/X)\). Split \(d=d_0d_1\), where \(d_1\) is the part supported on primes dividing \(X\), so \((d_0,X)=1\). On \(X\mid k\) its phase is exactly
\[
 e_{d_0}\big(b_0\overline{d_1}\,\overline X k\big)\,
 e_{d_1}\big(b_0\overline{d_0}k/X\big).
 \tag{5}
\]
The first factor is determined by literal residues modulo \(d_0\) of the six variables \(u,c,m,n,r,s\); for a slot \(A v\) split instead by \(v\bmod d_0\). This costs at most \(d_0^6\) and does not assume the selected residues are units modulo \(d_0\). The second factor and the projector are handled on units modulo \(X d_1\), since every prime of \(d_1\) already divides \(X\). Splitting the appropriate product first modulo \(d_1\), multiplicative Fourier coefficients of the phase restricted to the coset \(w\equiv1\bmod X\) are at most \(1/\varphi(X)\), by the onto reduction from units modulo \(X d_1\) to units modulo \(X\). This is the exact normalization of the existing major proof; all costs of the literal residue partitions and any arc twists are fixed powers of \(L\). The real separation with cutoffs and \(m^{it}\) factors at fixed polylogarithmic heights is unchanged.

For clarity, the long multiplicative sum in each endpoint has \(f=\mu\) or \(\lambda\), not an arbitrary bounded coefficient. In a fixed progression \(v\equiv c_0\bmod d_0\), put \(e=(c_0,d_0)\) (including \(e=d_0\) if \(c_0=0\)). Write \(v=e v'\), expand the reduced class \(v'\equiv c_0/e\bmod d_0/e\) by character orthogonality (modulus one allowed), and take the inducing character of the resulting twist. With \(\lambda\) one simply removes \(\lambda(e)\); with \(\mu\) the term vanishes if \(e\) is not squarefree, and otherwise one removes \(\mu(e)\) and imposes \((v',e)=1\). The bank, extra and target unit masks remain exclusions of prime factors contained in \([2,\exp(2L^{.2})]\) for large \(X\). Every character needed after this splitting has conductor dividing \(X d\). The new interval still has polynomial length scale even if \(A\) and \(e\) have polylogarithmic size. Characters of the fixed small unit modulus \(d_1\) already appearing in the separation do not increase the conductor bound.

The reciprocal estimate and Perron contour of the companion small-radical proof therefore apply, using \(1/L(s,\chi^*)\) for \(\mu\) and \(L(2s,(\chi^*)^2)/L(s,\chi^*)\) for \(\lambda\); the numerator in the latter is bounded in the full strip by its absolutely convergent Dirichlet series. In particular the principal inducing character is treated by the classical zeta Mertens estimate. Removing the Euler factors at any of the excluded primes is the convolution with the local inverse coefficients supported there (all coefficients of absolute value at most one). At \(Z=\exp(2L^{.2})\), bounding their absolute sums by the \(Z\)-smooth indicator costs \(O(\log Z)\) in reciprocal mass, and the tail past \(\sqrt M\) at a polynomial length \(M\) is at most \(M^{-1/(2\log Z)} L^{O(1)}\) by the same Rankin argument. Allowing the primitive-character mask for excluded imprimitive primes thus does not hurt the arbitrary fixed log saving. Fixed log-frequency and scaling factors are paid by partial summation. This proves the same estimate \(M L^{-F}\) for arbitrary fixed \(F\) in the long \(f\) slot. On both endpoints it is this one slot which gains cancellation, while the plain prime slot is merely a bounded coefficient in the restricted Bessel step.

The remaining parts of the established high-tag moment proof are support independent. The high moments are taken on unit tag polynomials in the actual modulus \(X d_1\) with the fixed residue and archimedean factors; they cost no assumptions about individual short prime progression counts, only uniqueness of colored prime factorizations below the modulus. Off the \(X^{o(1)}\) exceptional characters use full-product Parseval; on the exceptional characters use the same distinct-character Iwaniec Gram bound on the arbitrary other slot and the cancellation just proved on the multiplicative slot. The elementary Parseval square bounds do not increase when the coefficients or intervals are restricted. This gives \(\mathcal M_X=O(XY L^{-D'})\) as before. Cauchy on \(h\ll X/Y\) yields (4), after a sufficiently strong \(D'\), summation of shells, and the harmless bounded coefficients noted there.

## 2. Log derivatives and genuine weights that can be removed

Write \(x=a m\). The unit sample in (3) is precisely
\[
 \mathscr X=\{x\in PJ:\ x\equiv0\bmod a,\ x\equiv P\bmod b,\ (x,P)=1\},
 \quad M=\frac{\rho(P)|PJ|}{ab}.
\]
Its size is \(M+O(2^{\omega(P)})\), since \(ab\) is coprime to \(P\); on it the correspondence \(m=x/a,n=(P-x)/b\) is exact and unique. Use the separable additional masks only in the coefficients, not in the weight-removal calculation. They are bounded by one.

We use the exact log-derivative identities
\[
 f(m)\log m=\sum_{p^e\mid m} k_e\log p\, f(m/p^e),\qquad
 k_e=-1\ (f=\mu),\quad k_e=(-1)^e\ (f=\lambda).
 \tag{6}
\]
These follow from the Euler products for \(1/\zeta(s)\) and \(\zeta(2s)/\zeta(s)\) by taking the negative logarithmic derivative; for \(\lambda\) one may also verify them term by term by complete multiplicativity. Since \(\sum_{p^e\mid m}\log p=\log m\), **any truncation** after dividing (6) by \(\log m\) is bounded by one absolutely, including for squareful \(m\). The interval has \(\log m=L+O_{D_0,J}(\log L)\).

Fix \(0<\varepsilon<1/4\) before \(P\) grows. Keep only \(e=1\) and \(P^\varepsilon\leq p\leq P^{1-\varepsilon}\) in (6), and write \(f_\varepsilon(m)\) for this divided expression. The omitted mass in the original, unmarked unit sum is \(O(\varepsilon M)+o_{B,D_0,J}(M)\), with the constant in the first term independent of \(\varepsilon\). Here are the separate endpoint counts.

* For \(p^e\mid m\), \(p\) is coprime to \(bP\), since \(a m+b n=P\) and \((ab,P)=1\). In the progression of \(m\) modulo the unit modulus \(b\), and on target units, the number of multiples of \(p^e\) is at most \(C_J\rho(P)P/(ab p^e)+2^{\omega(P)}\). The contribution of \(e\geq2\), after division by \(\log m\), is \(O(M/L)+O(P^{1/2+o(1)})\): \(\sum_{p,e\geq2}\log p/p^e\ll1\), and the number of proper powers up to \(P\) is \(P^{1/2+o(1)}\). This estimate is insensitive to the alternating signs for \(\lambda\). For \(p<P^\varepsilon\), the main upper bound uses \(\sum_{p\leq P^\varepsilon}\log p/p\ll\varepsilon L+1\) and the floor errors are \(P^{\varepsilon+o(1)}\).
* For \(p>P^{1-\varepsilon}\), write \(m=pv\); here \(v\leq P^\varepsilon\), \((v,bP)=1\), and \(p\) belongs to one reduced class modulo \(b\). Siegel–Walfisz with \(b\leq L^{D_0}\), applied at the polynomial scale \(P/(av)\), bounds the summed \(\log p\) for each \(v\) by \(O(P/(a v\varphi(b)))\) uniformly. For fixed \(\varepsilon\) and large \(P\), every prime dividing \(bP\) is at most \(P^\varepsilon\), by the radical assumption. The coprime harmonic bound
\[
 \sum_{\substack{v\leq P^\varepsilon\\(v,bP)=1}}\frac1v
 \leq \prod_{\substack{\ell\leq P^\varepsilon\\\ell\nmid bP}}(1-1/\ell)^{-1}
 \ll \varepsilon L\,\rho(P)\varphi(b)/b
\]
follows from Mertens and \((b,P)=1\). This gives the stated \(O(\varepsilon M)\) after division by \(\log m\). There is no need for a pointwise bound on shifted primes in a short interval here.

Thus for the \(o\)-claim we can work with \(f_\varepsilon\), multiply weight only after this truncation, and eventually let \(\varepsilon\) tend to zero after the fixed-\(\varepsilon\) limit. In particular the endpoint estimate is not applied on a rare set already conditioned on tags.

Use \(s\asymp_K\log L\) mutually disjoint admissible \(K\)-band families as in the existing small-radical parity proof. For family \(j\), write \(\mathcal B_j\) for its union, \(\mathcal A_j\) for its tag products, and define
\[
 D_j=\prod_{\ell\in\mathcal B_j}(1-1/\ell),\qquad
 U_j=\sum_{u\in\mathcal A_j}\ \prod_{\ell\mid u}\frac1{\ell-1},\qquad
 Z_j(x)=\frac{1_{(x,\prod_{\ell\in\mathcal B_j}\ell)=1}}{D_j U_j}
          \sum_{u\in\mathcal A_j,\ u\mid P-x}1 .
 \tag{7}
\]
These denominators are bounded above and away from zero in terms of fixed \(K\). The advertised two-sided restriction is explicit: tags on the residual, and avoidance of the very same bank on the source. All these primes are coprime to \(abP\). For large \(P\) the tag divisibility in (7) is equivalent to \(u\mid n\).

Here is the exact mean calculation in the uniform local CRT model on \(\mathscr X\). For any tag \(u\), requiring \(x\equiv P\bmod u\) already enforces avoidance of zero at every \(\ell\mid u\). The other bank primes contribute \(1-1/\ell\). Thus the expected unnormalized single tag-and-avoidance contribution is exactly \(D_j\prod_{\ell\mid u}1/(\ell-1)\). Two distinct families use disjoint primes, with mixed mean \(1\) after normalization. The model same-family second moment is
\[
 \frac{1}{D_j U_j^2}
 \sum_{u,v\in\mathcal A_j}\prod_{\ell\mid [u,v]}(\ell-1)^{-1}=O_K(1).
 \tag{8}
\]
Indeed in each color the reciprocal lcm factor is bounded by a constant times the mass of that color plus its square.

These model moments approximate the literal integer sums on \(\mathscr X\) with absolute error \(O_{A,B,D_0,K,J}(P L^{-A})\) for every fixed \(A\). To verify this without a huge CRT modulus, for each fixed tag or tag lcm skip its primes in the bank-avoidance expansion, and use upper and lower Bonferroni up to successive orders about \(r=\lfloor L^{.1}\rfloor\). The positive omitted reciprocal sum after a tag lcm has been fixed is at most \((C_K)^{r}/r!\), since only one or two fixed banks are involved. Summing over the selected tag obligations costs at most a constant for their reciprocal sums. The number of literal terms is \(\exp(O_K(L^{.3}))\), from all choices of at most \(r+O_K(1)\) bank primes, and the target-unit inclusion-exclusion costs at most \(2^{\omega(P)}\leq L^B\). The residue class modulo \(ab\), the target divisors, the tag lcm and the additional exclusion divisors after opening are pairwise coprime apart from overlaps already discarded; every term is a legitimate CRT count with an \(O(1)\) interval floor error. Summing all floor errors is still smaller than any \(P L^{-A}\). This gives the model mean, diagonal second moment bound and off-diagonal mean \(1\) with the stated errors.

Consequently, for \(\bar Z=s^{-1}\sum_{j=1}^s Z_j\),
\[
  \sum_{x\in\mathscr X}|\bar Z(x)-1|^2\ll_K M/s+O_A(PL^{-A}).
  \tag{9}
\]
Since both signed factors and the supplementary masks have modulus at most one after truncation, Cauchy removes \(\bar Z\) at cost \(O_K(M/\sqrt{\log L})+o(M)\). The order is essential: first \(\varepsilon\) and all desired logarithmic powers, then \(K\), then \(P\).

## 3. Application of the packet theorem

For a fixed family insert (6), truncated as above, in the sum with \(Z_j\). The prime slot is an actual \(p\in[P^\varepsilon,P^{1-\varepsilon}]\); the other physical slot is \(a v\) with \(m=pv\) and coefficient \(f(v)\) times the exact unit and extra masks on \(v\). For large \(P\), \(p\) is outside both the bank and the extra omitted primes, and \(a\) is coprime to the bank. Hence (7) applies bank-avoidance separably to the source slots, exactly as required in §1. The slot \(a v\) is at polynomial scale (after any fixed box shrinking). The masks on \(g(n)\) are applied to the residual below.

For \(g=\lambda\) the removal of a tag \(u\) always multiplies by \((-1)^K\), and for \(g=1\) it changes nothing. For \(g=\mu\) or \(\mu^2\) the same removal with factors \((-1)^K\) and \(1\), respectively, is exact once a marked repeated prime is omitted. A failure requires \(r^2\mid n\) for a bank prime \(r\); this costs \(O(P\exp(-cL^{.1}))\) integer rows before weights. The divisor weight in (7) is \(O_K(L^K)\) pointwise, and the truncated source weight is bounded by one, so this correction is negligible to every fixed log power. Since \(u\) and the extra omitted primes are coprime, their residual masks are unchanged. After removal, \(P-p(a v)=u h\) where \(h=b(n/u)\), and the bounded residual is exactly \(1_{b\mid h}g(h/b)\) with its extra mask; the constant tag sign is harmless. Thus no prime condition is imposed or assumed on the residual.

Use dyadic or log-fine rectangles for the product interval and partial summation (or log-fine freezing) for the smooth \(1/\log(pv)\) factor from (6). For the log-fine procedure a boundary strip in \(x\) has length \(O(PL^{-F})\). A given \(m\) has at most \(O_\varepsilon(1)\) prime divisors \(p\geq P^\varepsilon\); the coefficient \(\log p/\log m\) is bounded. This and the pointwise bank-weight bound give arbitrary log saving in discarded strips if \(F\) is sufficiently large. Within each packet \(\log p\) stays as a bounded-polylog prime coefficient, and the remaining product log and real endpoints contribute only bounded weights or negligible mesh errors. All actual source packets stay below \(P\). Now (4) gives \(O(PL^{-A})\) for any fixed prescribed \(A\) on the marked unit sample with \(K\) large. Choose \(A\) to dominate \(1/\rho(P)\) and \(ab\leq L^{2D_0}\). Formula (9) then gives \(o(M)\) for the truncated expression for every fixed \(\varepsilon\). The mass removed in §2 gives
\(\limsup |\text{left side of (3)}|/M\ll\varepsilon\); taking \(\varepsilon\downarrow0\) proves (3).

## 4. Ordinary sums and the exact sign counts

Partition by \(d=(n,P)\), put \(P'=P/d\) and \(n=d t\), and note \((t,P')=1\), \((P'-t,P')=1\). For \(\lambda\) use complete multiplicativity. For \(\mu,\mu^2\), if \(d\) has any squared prime factor the term is zero for that function; otherwise remove its own factor and impose the appropriate \((t,d)=1\) or \((P'-t,d)=1\). The value of \(1\) never needs such a mask. Apply (3) with \(a=b=1\), target \(P'\), and the optional masks with \(T=d\). For \(d\leq\sqrt P\), \(\operatorname{rad}(P'),\operatorname{rad}(d)\leq(\log P)^B\leq(\log P')^{B+1}\) for all sufficiently large \(P\), so the unit \(o\)-bound holds uniformly at scale \(\varphi(P')\). Exactly \(\sum_{d\mid P}\varphi(P/d)=P\); this is why the relative unit normalization was retained. Larger \(d\) contribute at most \(P^{1/2}\tau(P)=P^{1/2+o(1)}\) integer rows. This proves (1), including the mixed and single-factor cases.

For \(\lambda\) expand \(1_{\lambda(n)=\epsilon}=(1+\epsilon\lambda(n))/2\) and use (1), also reflecting the interval for single factors if necessary. For \(\mu\) use \(1_{\mu(n)=\epsilon}=(\mu^2(n)+\epsilon\mu(n))/2\) for \(\epsilon\in\{-1,1\}\). Two squarefree integers in reflection have the exact local variables \(n\not\equiv0,P\bmod \ell^2\); there is one exclusion if \(\ell^2\mid P\) and two otherwise. CRT for a fixed initial segment of primes and the \(O(P\sum_{\ell>H}\ell^{-2})\) bound for the omitted square divisors give their density uniformly, with \(H\) fixed first and \(P\) large, then \(H\to\infty\). All other mixed terms in the sign expansion are \(o(P)\) by (1) and its reflected version. This gives (2).

## Comparison and limitation

[Mangerel, IMRN 2024, arXiv:2404.12117v2, Theorem 1.2](https://arxiv.org/abs/2404.12117) rules out the two extreme values of the unrestricted reflected Liouville sum. [Mangerel, arXiv:2412.17199v1, Theorems 1.2–1.3 and Proposition 1.4](https://arxiv.org/abs/2412.17199) gives prescribed sign existence with a Dirichlet GRH (or a specified weaker zero-free hypothesis), with additional conclusions at large prime targets. The present count and cancellation have a narrow target restriction in exchange for the unconditional conclusion and positive limiting densities. The [September 24, 2026 ordinary two-point manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) concerns fixed affine forms with constants allowed to depend on them. [Guo, arXiv:2608.23500v4](https://arxiv.org/abs/2608.23500) treats growing shifts in logarithmic averages with exceptional sets; these are different from the present ordinary sums at a single target with displacement comparable to the whole operand. The relevant fixed-target projected estimate here is instead the companion [small-radical argument](../small_radical_projection/Proof.md), modified to admit a genuine prime slot and a nonrough other slot, with the actual avoidance weight subsequently removed. For the unweighted, unmasked full-interval Liouville special case, [Guo's October 8 *Goldbach-type representations with prescribed Liouville signs*](https://github.com/aster2024/openai-math-followups) reports a stronger log-saving error on **all** sufficiently large totals in the author's indexed repository description (attributions updated November 2). It lists a Lean formalization conditional on one published estimate and separately assigns the half-plane consequences to Part II. The repository and underlying PDF were unavailable on direct retrieval at this audit, so neither the exact scope of its auxiliary estimates nor any corresponding subinterval, masked affine, or Möbius statement is inferred. The restricted full-interval Liouville assertion here is included only as a consequence of the same method, not as a novelty claim. [Meng's Theorem A](https://lsmeng.github.io/pdf/Meng_Liouville_sign_patterns.pdf) gives unconditional all-four existence apart from seven explicit small exceptions. [Pouly's October 20 Hexagon preprint](https://hexagonmath.org/pdf/2610.00350) gives an unconditional quantitative existence bound of order at least \(N^{1-\epsilon}\) for each sign pair at all sufficiently large totals, not a positive-density cancellation theorem. No general priority claim is made.

For example the result allows both reflected integers to be odd-rank composites, and the error and the ambient sample scale are much larger than the binary prime-pair scale. A power-rough rare subset cannot be substituted into (9), because it may avoid every tag. In the exact double Möbius divisor expansion of the binary \(\Lambda\) correlation, this controls a fixed collection of affine unit slices of the long Möbius variables (and the corresponding gcd strata for equal unit slopes). It does not bound the sums over all growing divisor ranges or give a signed lower bound on the prime atom.
