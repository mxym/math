# Zero and negligible chambers of the actual translated high term

This uses the translated tags and exact prime-side selector of [the companion Type I paper](SmallRadicalTranslatedTagTypeI.md), but no claimed estimate for the remaining \(\Gamma\). The two new removals below are on the **source** \(n\) of the Vaughan expansion, not on the reflected \(m=P-n\). They retain actual shifted weights and do not imply cancellation on the aggregate unmatched chambers.

## 1. A smooth square-root-compatible Vaughan split

Keep \(P,L,I=PJ,m,y,M,K\) from the translated draft. Use its original source roughness
\(z=\exp(L^{.24})\), not \(z=\exp(L/(\log L)^2)\). Set
\[
H=L^{3/5},\quad U_-=P^{1/4}e^{-2H},\quad U_+=P^{1/4}e^{-H},\quad V=U_+,\quad R_+=P^{1/4}.
\]
Let \(G\) be a fixed smooth real function with values between zero and one, equal to one on \((-\infty,-2]\) and zero on \([-1,\infty)\). Define \(g(x)=G((x-L/4)/H)\) for real log argument \(x\), and \(a(d)=\mu(d)g(\log d)\). The exact Vaughan identity with this arbitrary truncated Möbius part is
\[
\Lambda=a*\log+\Lambda_{\le V}-a*\Lambda_{\le V}*1
                  +(\mu-a)*\Lambda_{>V}*1.
\]
This follows by expanding \(\Lambda=\mu*\Lambda*1\) and using \(\mu*1=1_{\{1\}}\). The support of \(a\) is \(d\le U_+\); the short supported term vanishes on \(I\).

The companion Type I proof works at these enlarged combined moduli using the full classical Liouville BV level \(\sqrt x/(\log x)^D\) with arbitrary requested log saving. To justify that input rather than silently replacing \(.46\), [Granville–Shao, Theorems 1.1(b), 2.1](https://arxiv.org/html/1706.05710v1) give Bombieri–Vinogradov for fixed \(\lambda\) after the usual Siegel–Walfisz verification and ordinary prime BV for its prime restriction. The uncentered absolute version follows by removing the coprime mean with the same elementary convolution/Rankin argument as [Parity.md §1](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/small_radical_projection/Parity.md), now at moduli \(q\le\sqrt x\) rather than \(.46\). That argument already bounds the coprime mean uniformly for \(q\le x\).

Specifically truncate every translated complete packet part at \(\exp(L^{.27})\); discard its Rankin tail as before. Use Bonferroni depth \(\lceil D_0\log L\rceil\) at each rough/packet test, with fixed \(D_0\) chosen after the desired logarithmic error. The reciprocal mass of the primes in each test is \(O(\log L)\); Stirling's lower bound on \(h_0!\) makes that depth's first omitted reciprocal sum \(O_A(L^{-A})\) for large fixed \(D_0\). Each sieve product has log \(O_{D_0}(L^{.24}\log L)\) or less. All additional moduli including the \(M\) fixed profile caps, target radical and the common remainder \(v\) are \(\exp(o(H))\), because \(M,D_0\) fixed and \(.27<.6\). This gives full modulus at most \(P^{1/2}\exp(-H+o(H))\) both for the ordinary short-side grouped \(d\le U_+^2\) and for the low-\(r\) slice \(V<r\le R_+\), where \(rd\le R_+U_+\). The actual Liouville progression endpoint is \(x\asymp_J P/v\); its square root loses only \(\exp(O(\log v))=\exp(o(H))\), and the \((\log x)^D\) loss is smaller again. Thus the actual modulus lies in the asserted BV range, including at partial-summation endpoints. The total floor bill is \(P^{1/2+o(1)}\), as every extra variable is subpower. All grouping by reduced classes is unchanged. The low-\(r\) slice follows from \(\sum_{d\mid k}(\mu-a)(d)=-\sum_{d\mid k}\mu(d)g(\log d)\) for \(k=n/r>1\), with \(\sum_{r\mid D}\Lambda(r)=\log D\) on grouped modulus \(D=rd\); it does not require \(r,d\) to be distinct primes. This refits the paid terms to a smooth near-quarter cutoff.

## 2. Pay proper prime powers and squareful source rows before evaluating the high coefficient

Restrict the unmatched high term to \(r>R_+\) in its \(\Lambda\)-slot. The marked weights can be summed at each fixed \(n\) by the exact first-cover partition, whose nonnegative mass is at most one. Thus pointwise coefficient bounds on a chamber of \(n\) can be accumulated over the whole collection of tags with **no tag-multiplicity loss**. The residual sign and complementary rough filter have modulus at most one.

If \(r=p^j>R_+\), \(j\ge2\), the high inner divisor sum at \(k=n/r\) is bounded by \(\tau(k)\). Consequently this entire contribution is at most
\[
O\left(PL\sum_{\substack{r>R_+\\r=p^j,\ j\ge2}}\frac{\log p}{r}\right)
=O(P^{7/8}L^3).
\]
Indeed cumulative proper-power log mass up to \(x\) is \(O(\sqrt x\log^2(2x))\) by counting all possible exponents and bases; a dyadic tail gives \(O(R_+^{-1/2}L^2)\). This is valid without treating \(r\) as a prime or applying a prime-distribution bound to its powers.

We may also discard squareful source \(n\) at arbitrary fixed log accuracy: the \(z\)-rough restriction puts any squared divisor \(q^2\) at \(q>z\), so there are \(O(P/z)\) such integers. The unmarked coefficient is at most \(L\tau(n)\) since the outer \(\Lambda\)-sum over divisors is \(\log n\). Cauchy using \(\sum_{n\le P}\tau(n)^2\ll P L^3\) gives an \(O(P L^{5/2}z^{-1/2})\) absolute bill. Do not use a pointwise divisor bound against this stretched exponential.

## 3. Exact coefficient and pointwise zero sector

Now \(n\) is squarefree and only genuine primes \(r>R_+\) remain in the high slot. If \(n=r\) is itself prime its high coefficient is zero, because \(k=1\) and \((\mu-a)(1)=0\). For composite \(n\), let \(b\) be its complete \(U_+\)-small part, the product of all primes \(p\le U_+\) dividing \(n\). For any large \(r>R_+>U_+\), the divisors \(d\) of \(n/r\) within the support of \(g(\log d)\) all come from \(b\), regardless of which \(r\) is chosen. The exact high coefficient becomes
\[
-\left(\sum_{\substack{r\mid n\\r>R_+}}\log r\right)D_g(b),\qquad
D_g(b)=\sum_{d\mid b}\mu(d)g(\log d).
\tag{1}
\]
In particular it vanishes pointwise on the entire sector \(1<b\le U_-\), since all \(g\)-values there are one. A profile with \(U_-<b\le U_+\) is **not** claimed zero. The outer log sum in (1) is always at most \(L\); there is no additional \(\log n\) weight after Vaughan expansion.

## 4. Two absolute savings that avoid the shifted \(\Gamma\)

**Rank four with \(b=1\).** On this sector all source primes exceed \(U_+\), hence \(n\le P\) has at most four factors (five would already exceed \(P\)). If there are exactly four, each lies in the narrow genuine-prime window
\[
\mathcal D=[P^{1/4}e^{-H},\,P^{1/4}e^{3H}],
\]
since the product of the other three is at least \(U_+^3\). By the prime number theorem and partial summation,
\(\sum_{q\in\mathcal D,\ q\ \mathrm{prime}}q^{-1}=O(H/L)\): the main term is the logarithm of the ratio of the endpoint logarithms and the exponential PNT error is negligible. Fix three ordered genuine primes with product \(d_0\). If a fourth is possible, its count is bounded by \(\pi(P/d_0)\ll P/(d_0 L)\), since \(P/d_0\ge P^{1/4}e^{-9H}\) after the fixed three windows. Thus an upper bound for all actual rank-four \(n\) in this case is
\[
\frac{P}{L}\left(\sum_{q\in\mathcal D,\ q\ {\rm prime}}\frac1q\right)^3
\ll P L^{-1}(H/L)^3 .
\]
We counted ordered choices and may omit distinctness in this upper bound. Multiplying the coefficient \(L\), and using exact first-cover mass at most one, gives \(O(P L^{-6/5})\) for the whole chamber, without even sieving \(m\).

**Ten very small distinct source primes.** If squarefree \(n\) has at least ten distinct factors \(p_i\le\exp(L^{.26})\), they all lie in \(b\) for large \(P\). Choose any ten (no sum over choices); write \(b=(\prod_i p_i)b_0\). In \(D_g(b)\), sum all allocations of those ten primes first. For each \(d\mid b_0\) the resulting ten-fold difference of \(g\) is bounded by
\[
\|g^{(10)}\|_\infty\prod_{i=1}^{10}\log p_i
 \ll (L^{.26}/H)^{10}=L^{-17/5}.
\]
This follows by ten applications of the fundamental theorem of calculus, or one iterated integral, and uses true smoothness of the chosen cutoff. Therefore \(|D_g(b)|\ll \tau(n)L^{-17/5}\). The high-slot log sum in (1) contributes at most \(L\), and \(\sum_{n\le P}\tau(n)\ll PL\), so this whole chamber costs at most \(O(P L^{-7/5})\) in the actual signed shifted sum. This again uses exact first-cover weight and no cancellation of the reflected Liouville sign. Both stated absolute savings survive multiplication by the external \(O(L)\) factor on the difficult \(a_y(m)=1,d=1\) channel, giving \(o(P)\) for their own contributions.

## 5. What is actually still unpaid

After the reductions above, the high source consists of squarefree composite \(n\) with at least one prime \(r>R_+\), and either \(b=1\) with rank two or three, or \(b>U_-\) with fewer than ten distinct source primes at most \(\exp(L^{.26})\), still carrying the coefficient (1). There may be other zeros of \(D_g\), but none are claimed here. The remaining shifted sign \(\lambda(P-n)\) with all first-cover conditions is not controlled. In particular this does not pay the whole translated Type II, the entire signed divisor kernel, or Goldbach positivity.

**Comparison with the relative rough scale.** Since \(V_y(P)\gg L^{-\delta}\) and \(0<\delta<.1\), the absolute costs \(O(P L^{-6/5})\) and \(O(P L^{-7/5})\) are both \(o(PV_y(P)/L)\), with ratios respectively \(O(L^{-1/5+\delta})\) and \(O(L^{-2/5+\delta})\).
