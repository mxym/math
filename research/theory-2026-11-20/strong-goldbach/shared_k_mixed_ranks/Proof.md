# Higher ranks compensate a genuine semiprime block at the same short index

This is an unconditional fixed-target statement about actual prime factors in the balanced shared-index statistic of [Pham, Appendix D](https://www.preprints.org/manuscript/202610.3061). It uses the actual long divisor score of the [above-root shared-index calculation](../overroot_shared_k/Proof.md). The result is a cancellation on a specified mixed-rank block, **not** a bound on the overall covariance, and does not give a representation as two primes.

Let \(N=2x\) be even and sufficiently large, \(Y=\sqrt x\), \(L=\log x\), \(\ell=\log L\), \(z=\exp(L/\ell^2)\). Write \(E=[.65Y,.8Y]\), \(I=[Y,1.1Y]\), \(H_E=.15Y\), \(H_I=.1Y\). Indices \(d,e\in E\) and \(k\in I\) are integers coprime to \(N\). Each reflected integer \(N-dk\) or \(N-ek\) is in \((x,3x/2)\). The tagged side uses the actual multiplicity
\[
 \beta(d)=\sum_{\substack{p_2p_3\mid d\\
          p_2\ {\rm prime},\ x^{.029}\le p_2\le x^{.031}\\
          p_3\ {\rm prime},\ x^{.075}\le p_3\le x^{.078}}}1 .
\]
Both tags and the residual part of \(d\) are automatically units modulo \(N\). The **opposite \(e\)-leg is untagged**. Define, with \(R=x^{.505}\),
\[
 K(y)=1_{P^-(y)>z}\!\sum_{\substack{r\mid y\\r>R}}\mu(r)\log(y/r),\qquad
 V(y)=(\log s)\,1_{\substack{y=sq,\ s,q\ {\rm prime}\\
                  x^{.02}\le s\le x^{.08},\ (sq,N)=1}} .
\]
Here \(s\) is the unique small factor on the indicated support; \(V=0\) off it. Both factors exceed \(z\) for large \(x\), and \(q>R>s\). Consequently the indicated part of \(K(y)\) is exactly \(-V(y)\). This is a true semiprime band, not an almost-prime sieve majorant.

For every \(A>0\), uniformly at the fixed target,
\[
 \sum_{d,e,k}\beta(d)K(N-dk)V(N-ek)=O_A(x^{3/2}L^{-A}).               \tag{1}
\]
Let \(P_{22}=\sum_{d,e,k}\beta(d)V(N-dk)V(N-ek)\), and let \(D_N=\sum_{d\in E,(d,N)=1}\beta(d)d/\varphi(d)\). Write \(c=\log(.98/.92)\) and
\[
 {\cal E}_N(d)=\prod_{p\nmid N}
       \left(1+\frac{\varphi(d)}{(p-1)\varphi(dp)}\right).
\]
This is absolutely convergent and bounded between 1 and a fixed absolute constant. Then
\[
 P_{22}=(c^2+o(1))\,H_EH_I
           \sum_{\substack{d\in E\\(d,N)=1}}\beta(d)
                    \frac{d}{\varphi(d)}{\cal E}_N(d)
      \ \ge\ (2\cdot 10^{-8}+o(1))x^{3/2}\frac{\varphi(N)}{N}.       \tag{2}
\]
The negative contribution on the exact same \(k\)'s has the following stronger *signed* form:
\[
 \sum_{\substack{d,e,k\\
          y=N-dk\ {\rm squarefree},\ \omega(y)\ge3}}
       \beta(d)K(y)\big(-V(N-ek)\big)
 \ \le\ -P_{22}+O_A(x^{3/2}L^{-A}).                                \tag{3}
\]
In particular the higher-rank population really compensates at natural scale; (3) is not merely an upper bound on its absolute weight. These conclusions remain valid with \(d=e\) deleted. If the same tag is also placed on \(e\), the positive rank-two square still has an unconditional natural-scale lower bound by Cauchy as detailed below, but (1) and (3) are **not** asserted for that two-tag geometry.

## 1. Semiprime column means with true short and long primes

At full product size \(x\), use the actual short prime \(s\) at exponent \(u\in[.02,.08]\) and actual long prime \(q\). [Fouvry, *Autour du théorème de Bombieri–Vinogradov II*, Corollaire 1](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf) applies on independent dyadic rectangles after dividing the short \(\log s\) weight by \(O(L)\). The short sequence satisfies the uniform Siegel–Walfisz condition (1.3), including auxiliary coprimality: for logarithmic moduli use the prime count in intervals and partial summation, and charge the removed primes to the auxiliary divisor bound; for larger moduli use the trivial class and principal bounds. The long coefficient is the indicator of a genuine prime on its rectangle. All reduced progression tests use the ordinary fixed integer \(N\bmod m\), allowed at the local box scale \(X_0=4M_0N_0\) since the box product anchors are \((1+o(1))\) the actual subinterval of \((x,3x/2)\), and \(N=2x\le X_0\). Both rails \(.5+u/2,\ 4/7-6u/7\) exceed \(.5028\) throughout the short band. Thus the asserted sum of absolute errors applies to all \(m\ll YL^D\) with fixed \(D\), including \(m=k\), \(m=d\), and \(m=dj\) for \(j\le L^D\). The principal retains the actual \((sq,m)=1\) mask, divided by \(\varphi(m)\). Arbitrary order-\(K\) modulus weights in this corollary allow taking the sign of the discrepancy; fixed divisor powers are absorbed directly or by Cauchy against a trivial error bound. No well-factorability is used.

For moving endpoints, cut the positive product coordinate \(v=sq\in[x,3x/2]\) into a fixed log-fine mesh, and approximate each product step by independent rectangles in the two factor coordinates of relative width \(L^{-B}\). This is legitimate for the absolute error: each \(v\) is represented at most once, since exactly one of its two prime factors is in the small band. The error at a physical endpoint for each modulus is at most \(O(L)(x/(mL^B)+1)\) by counting integers of class \(N\), with the same bound with \(m\) replaced by \(\varphi(m)\) for the principal. At any fixed mesh endpoint the needed product-boundary rectangles are confined to stripes of that same thickness, again by uniqueness of the small factor. Summing these estimates and using fixed divisor-harmonic moments spends only logarithms. The number of independent rectangles and mesh endpoints is a fixed power of \(L\); request sufficiently high accuracy from Fouvry after the mesh. As usual one can choose \(B\) after the desired final exponent in every use. This supplies interval maxima in the weighted absolute mean estimate. Arbitrary smooth functions of the index with uniformly bounded variation may then be inserted by partial summation.

Let the exact smooth prime-density function on \([x,3x/2]\) be
\[
 m_x(v)=\sum_{\substack{x^{.02}\le s\le x^{.08}\\s\ {\rm prime},\ (s,N)=1}}
                         \frac{\log s}{s\log(v/s)}.
\]
For a \(v\)-interval \([v_0,v_1]\) in this range the true long-prime PNT main, for each \(s\), is \(\int_{v_0/s}^{v_1/s}dt/\log t\) times \(\log s\). Changing variables to \(v=st\) gives precisely \(\int_{v_0}^{v_1}m_x(v)\,dv\), to arbitrary inverse-log total error by ordinary PNT and the bounded reciprocal mass of the short primes. A short prime dividing \(m\) or \(N\) costs \(O(L^{O(1)}x^{-.02})\) relatively, using at most \(O(L)\) such primes; the long \(q\gg x^{.92}\) cannot divide any tested modulus. An actual \(q\mid N\) contributes a power-small total: there is at most one such long prime, and for each of at most \(x^{.08}\) choices of \(s\), the fixed integer \(N-sq\) has only \(x^{o(1)}\) factorizations into the physical slopes and common index. At the model level its deletion is negligible by the same count. With both \(s,q\) units modulo \(N\) and the modulus-slope a unit, the other physical index must be a unit as well. These checks are why there is no extra factor \(\varphi(N)/N\) in an individual unit-modulus principal.

By partial summation over genuine \(s\) and \(\log(v/s)=L(1-\log s/L)+O(1)\),
\[
 m_x(v)=c+O(1/L),\qquad
 \sup_{x\le v\le3x/2}|x m_x'(v)|\ll 1/L,
 \qquad
 c=\int_{.02}^{.08}\frac{du}{1-u}.
\]
In particular these are smooth uniform bounds, but we will **not** discard the \(O(1/L)\) in a signed test against \(K\). For unit \(k\), put \(U(k)=\sum_{e\in E,(e,N)=1}V(N-ek)\), and
\[
 \Psi_x(t)=\frac1{.15}\int_{.65}^{.8}m_x(N-xvt)\,dv .
\]
The progression main for \(U(k)\) is exactly the smooth expression
\[
 U(k)=H_E\frac{k}{\varphi(k)}\Psi_x(k/Y)+\Delta(k), \qquad
 \sum_{\substack{k\in I\\(k,N)=1}}|\Delta(k)|\ll_A xL^{-A}.           \tag{4}
\]
This uses \(v\in[N-.8Yk,N-.65Yk]\) and modulus \(k\), not modulus \(k\) multiplied by the two tags from the other side. We have \(\Psi_x=c+O(1/L)\) and uniformly bounded first derivative. For any other fixed divisor-envelope row on the tagged side the aggregate errors in (4) stay \(O_A(x^{3/2}L^{-A})\): at a fixed unit \(k\), the other row's absolute sum is \(O(YL^{C})\) by Shiu's upper bound in the actual class \(N\bmod k\) and Hölder for fixed divisor powers of the slope. The genuine \(K\) weight is at most \(L\tau(y)\); the stated range remains a fixed gap from modulus size \(x\). This proves the promised transfer against an actual other row, not just a mean over all \(k\).

## 2. The exact cancellation with the entire tagged row

Write \(b(y)=1_{P^-(y)>z}/V_z\) with \(V_z=\prod_{p\le z}(1-1/p)\), and \(a(y)=\log y\,1_{y\ {\rm prime}}\). From the above-root calculation, \(K\) differs from \(a-b\) by an averaged arbitrary-log error when tested on the genuine \(\beta(d)\) rows against any bounded-log weight depending on \(k\). This follows from the signed \(F_R-b\) transfer there with the opposite weight chosen independent of its row index; alternatively one obtains it directly before that row index is summed in its proof. There is only a power-small proper-power correction in \(a\). Use this with the exact function \((k/\varphi(k))\Psi_x(k/Y)\); it has a fixed bounded-log envelope.

To test \(a-b\), expand \(k/\varphi(k)=\sum_{j\mid k}\mu^2(j)/\varphi(j)\) and truncate to \(j\le L^D\), choosing \(D\) after the error budget. The discarded sum is \(O_A(xL^{-A})\) because for each \(j\le 1.1Y\) there are \(O(Y/j)\) eligible \(k\), and \(\sum_{j>L^D}1/(j\varphi(j))\ll_\epsilon L^{-D(1-\epsilon)}\); the remaining weights are bounded by \(L^C\) after divisor moments. For the genuine \(a\)-row in \(k\equiv0\bmod j\), use the earlier [Maynard wedge transfer](https://github.com/mxym/math/commit/bafa9b8f) on the physical \(d\) side: the exact prime class is \(N\bmod dj\), \((dj,N)=1\), including possible overlaps of \(d,j\), with the physical interval endpoints. Its principal on each \(k\)-prefix of real length \(H\) is \(dH/\varphi(dj)\). The true prime already forces \(k\) to be a unit, since a prime divisor of \(N\) is \(\le x\) and the prime coordinate is \(>x\). The rough count in the same class has exactly one forbidden residue per \(p\le z\) not dividing \(dj\), giving the matched principal up to \(O(L/z)\) relatively, and deterministic arbitrary-log precision by finite Bonferroni and floors. If \(k\) shares a prime \(r\mid N\), the rough row is already zero for \(r\le z\); for \(r>z\) there are only \(O(Y/(jr)+1)\) potential rows and the sum over \(r,j\) is negligible. Partial summation with the **actual** bounded-variation \(\Psi_x\) and its moving endpoints preserves these estimates. Thus
\[
 \sum_{d,k}\beta(d)\frac{k}{\varphi(k)}\Psi_x(k/Y)K(N-dk)
       \ll_A xL^{-A}.
\]
Using (4) yields (1). No sign, uniform smallness, or statistical independence of individual \(K\) rows is assumed.

## 3. Measured positive block and forced higher-rank sign

To evaluate \(P_{22}\), first use (4) on the untagged row. On the tagged \(d\) side make the same short harmonic expansion of \(k/\varphi(k)\). For each retained \(j\), apply Section 1 to modulus \(dj\) and genuine semiprimes \(N-dk\) after \(j\mid k\), now weighted by \(\Psi_x(k/Y)\). This yields the principal
\[
 \frac{d}{\varphi(dj)}
      \int_I m_x(N-dt)\Psi_x(t/Y)\,dt
\]
for that \(d,j\), with the total weighted error arbitrary-log at the \(x\)-scale. The semiprime model again only excludes the power-small short primes of \(djN\). The integral equals \((c^2+o(1))H_I\) uniformly in \(d\). Completing the harmonic sum multiplies \(d/\varphi(d)\) by \({\cal E}_N(d)\); the uniform tail is
\[
 \sum_{j>L^D}\frac1{\varphi(j)^2}\ll_\epsilon L^{-D(1-\epsilon)}
\]
using \(\varphi(dj)\ge\varphi(d)\varphi(j)\). This proves the full first equality in (2).

For an explicit lower, \(D_N\ge\sum_{d\in E,(d,N)=1}\beta(d)\).
Opening the two genuine tags in \(d\), then counting their free cofactor by inclusion–exclusion with \((h,N)=1\), gives
\[
 \sum_{d\in E,(d,N)=1}\beta(d)
   =(1+o(1))H_E\frac{\varphi(N)}{N}
                 \log(31/29)\log(78/75).
\]
The floor loss summed over the prime pair labels is \(O(x^{.109}\tau(N))\), a power saving even after comparison with \(Y\varphi(N)/N\). The reciprocal mass of any discarded target factors is \(O(Lx^{-.029})\). Since \(c>.06\), \(\log(31/29)>.066\), \(\log(78/75)>.039\), as follows from the first two alternating terms for \(\log(1+t)\), one has \((.15)^2(.1)c^2\log(31/29)\log(78/75)>2\cdot10^{-8}\). This yields the second part of (2), with both slope unit restrictions and the common unit \(k\) already accounted for in the actual progression mains.

At a squarefree prime \(y\), \(K(y)=0\). At a squarefree semiprime it is \(-\log(\min(p,q))\) if the larger prime exceeds \(R\), and zero otherwise. In particular every such rank-two weight is nonpositive, and the selected rank-two band is exactly \(-V(y)\). Rough nonsquarefree \(y\) may be deleted with arbitrary-log errors from (1): there are \(O(x/z+\sqrt x)\) such \(y\) with a repeated prime \(>z\), each with at most \(\tau(N-y)\) physical row representations. Cauchy with ordinary divisor moments pays the \(\tau(y)\log y\) factor, and the other row weight is \(O(YL)\). Now (1) and nonpositivity of the entire semiprime score prove (3); no hypothesis on the sign of any individual higher rank is used. Terms with \(d=e\) always cost \(O(x^{1+o(1)})\) and may be removed as asserted.

If both legs use tags, Section 1 with physical modulus \(d\), summed over \(\beta(d)\), gives
\(\sum_{d,k}\beta(d)V(N-dk)=(c+o(1))H_I D_N\).
There are \((1+o(1))H_I\varphi(N)/N\) actual unit \(k\), by inclusion–exclusion with error \(O(\tau(N))\). Cauchy on the same \(k\)'s therefore gives the genuine positive two-tag rank-two square lower bound
\((c^2+o(1))H_I D_N^2 N/\varphi(N)\), again with a negligible diagonal correction. This does not yield the higher-rank compensation for two tags, because that would require the semiprime column mean at modulus \(k p_2p_3\), outside the Fouvry range used here.

The present cancellation is specific to a true semiprime in one physical leg, with an ordinary untagged slope on that leg. The complementary signed rank blocks and the full two-tag covariance remain unevaluated.
