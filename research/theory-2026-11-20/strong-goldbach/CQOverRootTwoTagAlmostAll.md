# The genuine over-root two-tag prime remainder for almost all targets

Written research note. This proves an almost-all result for the [actual two-tag test](CQOverRootTwoTagPrimeHBRails.md). The target, tag windows, and prime interval retain their literal dependence on \(N\), and the residue is always \(N\) itself. This does not control a fixed target, powers of two, or any hypothetical exceptional target.

Fix a compact interval \(J\subset(0,1)\), \(\eta=.0002\), and the distinct prime tags \(N^{.246}<q\le N^{.249}\) and \(N^{.255}<r\le N^{.258}\). Let \(\lambda^\pm_d(N)\) be ordinary Rosser upper and lower linear sieve weights for cutoff \(N^\eta\), level \(N^{10\eta}\), and the usual strict or weak cutoff convention. For either sign and either orientation \(I_N=NJ\) or \(N(1-J)\), define
\[
 E_N=\sum_{\substack{q,r,d\\(qrd,N)=1}}\lambda^\pm_d(N)
  \left[
    \sum_{\substack{p\in I_N\\ p\ {\rm prime}\\ p\equiv N\bmod qrd}}\log p
    -\frac1{\varphi(qrd)}
         \sum_{\substack{p\in I_N\\p\ {\rm prime}\\(p,qrd)=1}}\log p
  \right].
\]
The tags run over their true windows. For every \(A>0\),
\[
 \sum_{\substack{X\le N\le2X\\2\mid N}}|E_N|^2\ll_{A,J} X^3(\log X)^{-A}.
\]
In particular the actual needed log-power remainder holds apart from \(O_B(X(\log X)^{-B})\) targets for any fixed \(B\), at any prescribed fixed log-power saving.

## 1. Exact weights and Fourier expansion

Work on \([X,2X]\) and write \(L_X=\log X\), \(K=(2X)^{.509}\). For every fixed \(k=qrd\le K\), the possible decomposition is unique, because the full two enlarged tag ranges on \([X,2X]\) are separated for large \(X\), and all prime factors of \(d\) lie below them. Write its weight \(w_k(N)\), zero off its support. For a fixed squarefree \(d\) with primes placed in decreasing order, the ordinary Rosser support tests are a largest-prime condition and fixed-parity prefix-product inequalities with upper threshold \(N^{10\eta}\). Each imposes a lower bound on \(N\); the sign \(\mu(d)\) is fixed. The two tag bounds impose intervals in \(N\). Thus \(w_k\) is a constant of absolute value at most one on an interval of integer targets, zero elsewhere. This argument also permits a fixed logarithmic number of intervals at the cost of logarithmic factors. For large \(X\), every central prime \(p\) in question exceeds \(k\). The condition \((N,k)=1\) is then automatic on the prime progression count, and can be kept only on the density term; if \(N\) is a nonunit, both terms vanish.

First take a fixed prime interval \(I\) at central scale \(X\). Put \(P_I(\alpha)=\sum_{p\in I}\log p\,e(-p\alpha)\). The exact Fourier expansion of the difference uses, at each reduced \(a/s\) with \(s\mid k\), the coefficient
\[
 \frac1k\left(P_I(a/s)-\frac{\mu(s)}{\varphi(s)}P_I(0)\right).
\]
Indeed the coefficient of \(1_{(N,k)=1}/\varphi(k)\) is \(\varphi(k)^{-1}\sum_{s\mid d\mid k}\mu(d)/d=\mu(s)/(k\varphi(s))\). The zero frequency \(s=1\) cancels. No upper bound on the actual residue \(N\) or approximation to it is used.

## 2. Two uses of the additive large sieve

Let \(S<s\le2S\) be a denominator block and let \(F_I(a/s)\) be the prime difference in parentheses. Decompose the support interval of each \(w_k\) into canonical dyadic integer blocks on a grid covering \([X,2X]\); at most two blocks occur at each scale. At one scale, the target blocks \(B\) are disjoint and the coefficient for a fixed \(s,B\) is \(C_{s,B}=\sum_{s\mid k}w_{k,B}/k\), where \(w_{k,B}\) vanishes if \(B\) is not a block of its support decomposition on this scale. Positivity after absolute values gives
\[
 \sum_B |C_{s,B}|^2
 \le \left(\sum_B\sum_{s\mid k}\frac{|w_{k,B}|}{k}\right)^2
 \ll L_X^2/s^2.
\]
Apply the dual [Montgomery–Vaughan additive large sieve](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf) to the resulting rational frequency sum on every target block. The reduced fractions in the denominator block have spacing \(\gg S^{-2}\). Summing over the disjoint target blocks gives
\[
 \ll (X+S^2)L_X^2 S^{-2}
       \sum_{S<s\le2S}\ \sum_{a\bmod s}^{*}|F_I(a/s)|^2 .
\]
Apply the ordinary additive large sieve to the prime part at the same family of reduced fractions, with input weights \(1_p\log p\) and support of length \(O(X)\). Its squared sum is \(\ll (X+S^2)X L_X^2\). For the centering component, its squared sum is at most \(|P_I(0)|^2\sum_{S<s\le2S}1/\varphi(s)\ll X^2L_X^{O(1)}\). Combining and summing dyadic target scales by the triangle inequality in \(\ell^2\), the bound for this denominator block is
\[
 \ll L_X^{O(1)}\, X\frac{(X+S^2)^2}{S^2}.
\]
For \(L_X^D<S\le\sqrt X\) this is \(\ll X^3 L_X^{O(1)-2D}\); for \(\sqrt X<S\le K\) it is \(\ll X^{2.018}L_X^{O(1)}\). Choose \(D\) large and combine the \(O(L_X)\) denominator blocks by the same triangle inequality.

For \(s\le L_X^D\), Siegel–Walfisz summed against the \(s\) actual reduced phases yields \(|F_I(a/s)|\ll_{B,D} XL_X^{-B}\) for arbitrarily large \(B\). Indeed the residue-class main from summing the prime logarithms is \(|I|/\varphi(s)\) and the character sum of the additive phase over units is \(\mu(s)\); the total prime term agrees to the same required accuracy. The bound \(|\sum_{k:s\mid k}w_k(N)/k|\ll L_X/s\) then directly makes these denominators \(O_A(XL_X^{-A})\) pointwise. This completes the squared mean with a fixed central prime interval, uniformly in its endpoints. Keeping only even targets can only decrease this squared sum.

## 3. Restore the actual moving prime interval

Partition \([X,2X]\) into \(O(L_X^T)\) target slabs of length at most \(X L_X^{-T}+1\). On each slab replace the two endpoints of \(I_N\) by their values at one endpoint of the slab. They move by \(O(H)\), where \(H=XL_X^{-T}+1\). For any one \(N\) the absolute change in the prime progression terms is bounded by dropping primality in the two actual endpoint strips and summing
\[
 \ll L_X\sum_{k\le K}(H/k+1)\ll (H+K)L_X^{O(1)} .
\]
The density terms change by at most \(O(HL_X^{O(1)})\) by \(\sum_{k\le K}1/\varphi(k)\ll L_X^{O(1)}\). The tag and sieve weights were not frozen in this step. Take \(T\) large enough relative to \(A\). The summed squared error from moving the endpoints is then \(\ll_A X^3 L_X^{-A}\); separately use the fixed-interval squared mean with an arbitrarily strong logarithmic exponent on each slab and sum over their number. This proves the stated bound for \(NJ\) or its reflection. Chebyshev gives the indicated exceptional set, and taking the union of the four sets gives both signs and both orientations.

**Consequence and limitation.** On these targets the ordinary ratio-10 upper and lower sieve tests for the actual squarefree rough two-tag score have the same local main evaluation as in the [below-root calculation](CQPrimeTaggedRoughAxisObstruction.md); the only change was the remainder at \(qrd>N^{1/2}\). Thus the explicit test in the [over-root note](CQOverRootTwoTagPrimeHBRails.md) works against the specified relaxed angular transport for almost all targets. The transport has not been realized arithmetically. Nothing here takes the maximum over \(N\), improves the genuine fixed-target signed exterior, or shows a Goldbach pair in any target left exceptional.
