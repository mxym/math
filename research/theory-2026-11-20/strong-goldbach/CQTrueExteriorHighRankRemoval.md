# Paying a true high-rank negative sector in the cubic–quintic signed exterior

Based on [the sharp cubic–quintic detector](cubic_quintic_sharp/CubicQuinticSharp.md) at reference commit `989aea5`. Maintain the actual fixed even target \(N\), same reflected pairs \(x+y=N\), \((x,N)=1\), fixed \(x/N\in J\Subset(1/3,2/3)\), \(L=\log N,\ M=|J|N\mathfrak S(N)\), and the exact sharp \(H=V_{\rm raw}-\Pi\) in CubicQuinticSharp. The convention for pair brackets throughout is on this literal target, not an ordinary product or CRT relaxation. The existing transfer and signed identity give \(R_J=\langle H,H\rangle+o(M)\).

Let \(w(n)=\max_{p\mid n}\log p/\log n\) be the own-log largest genuine angle and \(r=\omega(n)\). Define the genuine nonnegative composite source
\[
 W=[-H]_+1_{P^->N^{.040}}1_{\{r\in\{10,12,\dots,24\}\ {\rm or}\ (r=8,\ w\ge .36)\}}.
\]
The smaller optional choice \(W_{10}\) omits \(r=8\). Both vanish on nonsquarefree inputs. Let \(\mathcal W\) be the actual pair union where either arm has \(W>0\). Keep the original \(\mathcal P\) (both positive rank 2/3, floor .123), \(\mathcal A\) (some negative high arm with true floor .105), and \(\mathcal I\) (some tiny arm with least \(P^-\le N^{1/5000}\)) of ExplicitTinyNegativeOverlap. The constituent one-arm supports of \(\mathcal W,\mathcal A,\mathcal I\) are pairwise disjoint. In fact rank \(\ge10\) forces least angle in target logs \(\le1/10<.105\), and \(r=8,w\ge.36\) forces some other own angle \(\le.64/7<.105\); the target-log angle is at most that own angle since \(n<N\). Thus all \(W\) are inside the genuine receiver band
\[
I=1_{\{N^{.04}<P^-\le N^{.105}\}}.
\]
\(\mathcal W\) is disjoint from \(\mathcal P\) by the actual signs. The other two pairwise overlaps are nonempty in principle; no pair can hit **all three** \(\mathcal A,\mathcal I,\mathcal W\) since they use three pairwise disjoint one-arm types.

**Claim, combined version.** The contribution of \(\mathcal W\setminus(\mathcal A\cup\mathcal I)\) is \(>-.0995M+o(M)\). Hence
\[
R_J\ \ge\ .0304 M
 +\sum_{\substack{x+y=N,\ x/N\in J,\ (x,N)=1\\
                  (x,y)\notin\mathcal P\cup\mathcal A\cup\mathcal I\cup\mathcal W}} H(x)H(y)+o(M).
\]
If one omits the rank-8 sector, replace .0995 by .04905 and .0304 by .0809. These are unconditional residual decompositions. Neither the sign nor a sufficient bound on the new exterior is claimed.

## 1. Ordinary angular mass and squared-mass certificate

Write \(a=.04\), \(\mathbf u=(u_1,\dots,u_r)\) for literal own prime angles, \(H(n)/\log n=h_r(\mathbf u)\) on squarefree composites, and let \(b_r\) be the density at zero and nearby of the sum of centered independent uniforms with the *given widths* \(u_i\). This is an analytic finite-difference representation only; it is not a distribution assumption on integer arguments. If the largest width \(w\ge1/2\), terms containing that factor vanish on the actual truncated profile; all remaining subsets stay in its polynomial branch of degree five. The sum is then a finite difference of order \(r-1\ge7\), hence exactly zero. If \(w\le1/2\), the exact even-rank formula of NegativeArmUnion expands the \(r\) integral differences on the centered cube. The fourth derivative of \(16(1/2-t)_+^3\) is \(96\delta_{1/2}\) and the sixth of \(-32(1/2-t)_+^5\) is \(-3840\delta_{1/2}\). It follows that
\[
 h_r(\mathbf u)=\left(\prod_i u_i\right)
          [96 b_r^{(r-4)}(0)-3840 b_r^{(r-6)}(0)] .
\]
These derivatives are well defined for the positive fixed widths (the convolution of \(r\) interval densities is \(C^{r-2}\)); one can also smooth the truncated powers first. Only \(r=8,10,\dots,24\) occur in this proof; physical strict floor .04 and central \(n<N\) imply \(r\le24\).

For \(j\in\{4,6\}\), let \(k=r-j\), \(U_k\) the product of the \(k\) *longest* widths, \(S_j\) the sum of the remaining shortest \(j\), and \(b_j\) their box density. Differentiate the \(k\) longest uniform convolutions once each to obtain \(2^k\) signed translates of \(b_j\), divided by \(U_k\). There are \(2^{k-1}\) positive and \(2^{k-1}\) negative translates, each between zero and \(\|b_j\|_\infty\). Therefore
\[
 |b_r^{(k)}(0)|\le \frac{2^{k-1}}{U_k}\|b_j\|_\infty,\quad
\|b_j\|_\infty\le\frac{\sqrt2}{\sqrt{\sum_{\rm short}u_i^2}}\le\frac{\sqrt{2j}}{S_j}.
\]
The second inequality uses [Ball's codimension-one unit-cube slice theorem](https://doi.org/10.1090/S0002-9939-1986-0840631-0) and Cauchy; the density is the cube slice divided by the Euclidean norm of the width vector. In a largest-angle bin \(\ell\le w\le b\), use \(S_j\ge ja\) for the mass bound after cancelling the harmonic \(\prod u_i^{-1}\). For the pointwise amplitude bound instead cancel the longest widths in \(h_r\), via \(\prod_{\rm short}u_i\le(S_j/j)^j\) and \(S_j\le j(1-\ell)/(r-1)\) by averaging the \(j\) smallest of the \(r-1\) other widths. Thus a bin mass bound is its sorted coordinate volume times
\[
 G_r(\ell,b)=\sum_{j=4,6} c_j 2^{r-j-1}\sqrt{2j}/(ja\,\underline{U}_{r-j}),
 \qquad (c_4,c_6)=(96,3840),
\]
and multiply that by
\[
 C_r(\ell)=\sum_{j=4,6} c_j 2^{r-j-1}\sqrt{2j}\,
              [j(1-\ell)/(r-1)]^{j-1}/j^j
\]
for a bin bound on the ordinary squared score. This only uses \([{-h_r}]_+^2\le C_r(\ell)[{-h_r}]_+\); the actual negative score is used in the subsequent pairing.

### A finite exact \(\underline U_k\) for each bin

Write \(n=r-1\). The other \(n\) genuine widths are sorted in \([a,b]\) and sum to \(1-w\ge1-b\). They can be decreased coordinatewise to sum exactly \(1-b\) (interpolate all coordinates toward \(a\)), since the upper bin endpoint never exceeds \(1-na\). This operation cannot increase the product of the \(k-1\) longest among them, and \(w\ge\ell\). On the resulting fixed-sum sorted polytope the log of this named product is concave, so its minimum occurs at a vertex. Every vertex has a block equal to \(a\), a block equal to \(b\), and at most one other constant middle block: two different interior levels could be perturbed in opposite directions, balancing their multiplicities and preserving strict gaps and the sum, contradicting extremality. A vertex confined to endpoints is captured by allowing the middle level to equal an endpoint. Therefore try every multiplicity pair \(i,j'\ge0,\ i+j'<n\), fill the middle \(n-i-j'\) values with \((1-b-ia-j'b)/(n-i-j')\) if in \([a,b]\), take the minimum consistent product of the \(k-1\) largest, and multiply by \(\ell\). This minimum is positive and a valid lower \(\underline U_k\) for the original bin. Actual order/gcd conditions have only been relaxed for an upper.

### Exact enclosing volume

Permit all other coordinates to be \(\le b\) rather than \(\le w\), still requiring \(u_i\ge a\) and their sum \(1-w\). At fixed \(w\) the \((n-1)\)-dimensional coordinate volume is computed by shifting by \(a\) and using inclusion–exclusion for the independent caps \(b-a\). Integrate over \(w\in[\ell,b]\) and divide by \(n!\) to restore the \(n\) interchangeable other angles, while retaining the marked largest slot (ties have zero angular volume). The resulting enclosing volume is
\[
 \frac1{(n!)^2}\sum_{h=0}^{n}(-1)^h {n\choose h}
 \left[(1-na-h(b-a)-\ell)_+^{n}-(1-na-h(b-a)-b)_+^{n}\right].
\]
One factorial comes from integrating the truncated simplex over \(w\), the other from sorting the \(n\) other angles; no further \(r!\) is allowed. In ordinary arithmetic the actual ordered prime angular measure is \(du_1\cdots du_{r-1}/\prod_i u_i\). The \(G_r\) formula already cancels that denominator. The finite target-log floor \(P^->N^a\) implies each own angle \(>a\) for central \(n<N\); log-weight normalizations differ by \(1+O_J(1/L)\). The limiting ordinary coefficients can thus be upper bounded by these genuine compact integrals, with usual Jordan collar argument.

The exact checker takes largest-angle bins of width \(1/200\), clipped below by \(1/r\) (also .36 at rank 8) and above by \(1/2,1-na\). It uses \(\sqrt8<2.829,\sqrt{12}<3.465\), both rational squared checks. All computed volumes, exponents, vertex comparisons and amplitude estimates are rational, evaluated by BigInt with no binary floating point on any decision. The certified ordinary bounds are:
\[
\begin{array}{c|cc|cc}
 &m(W)\ \text{strict cap}&q_W=m(W^2/L)\ \text{strict cap}
 &\text{computed upper (approx.) on }m(W)&\text{computed upper (approx.) on }q_W\\
r\ge10&.000514&.000777&.0005136606314&.0007763783568\\
\text{combined}&.002380&.001459&.0023781782159&.0014575061002.
\end{array}
\]
Run the [exact rational checker](check_cq_true_exterior_high_rank.js) with Node.js. Ordinary integration here is the squarefree compact product PNT of the pinned files; no paired independence enters.

## 2. Every overlap bound is on the same physical target

The lower linear sieve at true \(.105\) cutoff and level \(N^{.42}\) gives normalized coefficient \(K_h=2\log3/.42>5.231\) on any genuine nonnegative compact product source. The upper at \(.04\) cutoff and level \(N^{.499(.04/.123)}\) gives \(U_l<4.651445(.123/.04)=14.303193375\). The two inequalities constrain the actual opposite argument of the very same source, so subtract the high rough subset from the low rough set:
\[
 \langle Z, L I\rangle,\ \langle L I,Z\rangle
 \le \mathcal J m(Z)M+o(M),\qquad \mathcal J=9.072193375.
\]
These are the genuine product-BV/linear bounds documented in WiderPositiveBlock §2 and the actual middle-overlap note, with strict level, no new distribution hypothesis. Likewise the standalone true .105-rough upper at level \(N^{.499(.105/.123)}\) is \(U_h=4.651445(.123/.105)\). Both compact \(W\) and \(W^2/L\) meet the positive marginal sieve conditions; the sharp signed \(H\) transfer uses only \(W\), which is bounded by \(|H|\) as required by NegativeArmUnion §1.

* **Own signed union.** Pointwise \(H=-W\) when \(W>0\). The exact total on \(\mathcal W\) is therefore \(-\langle W,H\rangle-\langle H,W\rangle-\langle W,W\rangle\). By the signed compact transfer, the first two terms together are \(-4m(W)M+\langle W,\Pi\rangle+\langle\Pi,W\rangle+o(M)\). Drop the two nonnegative prime rebates, spending neither elsewhere. Since \(W\) lives inside \(I\), actual pointwise AM–GM, \(2W(x)W(y)\le W(x)^2 I(y)+I(x)W(y)^2\), gives \(\langle W,W\rangle\le \mathcal J q_W M+o(M)\). Thus debit at most \(4m(W)+\mathcal J q_W\).
* **Previously paid high negative union.** In \(\mathcal W\cap\mathcal A\) the two types are necessarily on different arms. Hence the intersection is exactly \(\langle W,A\rangle+\langle A,W\rangle\), with \(A=[-H]_+1_{P^->N^{.105}}\). The pinned NegativeArmUnion bounds \(A\le1.2L1_{\{P^->N^{.105}\}}\) (its only candidate ranks are 3,4,5,6,8; cap \(1.2\) covers rank 8 too). The actual high rough cap gives intersection at most \(2(1.2)U_h m(W)M+o(M)\).
* **Previously paid tiny union.** Use \(T=H1_{P^-\le N^{1/5000}}\), \(\beta=1/5000\), and the same literal \(T=C+E+V_{\rm tiny}-D_{\rm tiny}\) quantities in ExplicitTinyUnion, not the raw \(V_{\rm raw}\). On \(\mathcal W\cap\mathcal I\) the two types are on opposite arms, so intersection is exactly \(-\langle W,T\rangle-\langle T,W\rangle\). For either orientation with \(W\) the true compact source, the stopped mean \(m_\beta\), vanishing signed defect \(E\), and genuine \(D_{\rm tiny}\) receiver bound give upper \((-m_\beta+U_D)m(W)M+\langle|V_{\rm tiny}|,W\rangle+o(M)\), or the reflection. Here \(-m_\beta<.0063885,\ U_D<.0111568\) from the original rational checker. For the remaining real intersection, use the certificate identity \(|V_{\rm tiny}|\le L\sqrt{XY}\) on the actual tiny arm, but choose a Cauchy split different from pricing \(XW,YW\):
\[
 \langle |V_{\rm tiny}|,W\rangle^2
 \le \langle LX,LI\rangle\ \langle LY,W^2/L\rangle .
\]
Pointwise square roots multiply to \(L\sqrt{XY}\,W\) on the actual support of \(W\) because \(I=1\) there, and vanish off it. The first genuine capacity is at most \(\mathcal J B_X^2 M+o(M)\) with \(B_X<.0033960\): apply the *band* upper above with \(LX\) on each original artificial compact rank/floor truncation, \(m(LX)\le B_X^2\) from the explicit tiny checker, and send the artificial inner floor to zero in the same order as ExplicitTinyNegativeOverlap. At fixed inner floor all certificate slots and \(LX\) are genuine nonnegative finite-rank angular tests; the established phase/tail limit passes the tiny intersection itself after applying the inequality there. The second capacity is at most \((.678/\beta)q_WM+o(M)\), applying the pinned actual marked-certificate \(LY\) bound of ExplicitTinyNegativeOverlap to the true nonnegative compact source \(W^2/L\). The certified ratio, real modulus at level \(N^{.499}\), squarefree conditions and genuine prime labels in that generic receiver estimate are unchanged. Therefore the two tiny orientations together contribute upper
\[
2(-m_\beta+U_D)m(W)M
   +2 B_X\sqrt{\mathcal J(.678/\beta) q_W}\,M+o(M).
\]
There is no term assuming a typical paired distribution and no use of an untruncated interval uniform in a floor depending on \(N\).

The physically new contribution is the whole signed \(\mathcal W\) union minus these **two** intersections, exactly: the triple intersection is empty, and \(\mathcal W\cap\mathcal P=\varnothing\). Thus with \(m=m(W),q=q_W\) the one increment to debit the previously proved reserve is
\[
 4m+\mathcal J q+2(1.2)U_hm
   +2(.0063885+.0111568)m+2(.0033960)\sqrt{\mathcal J\cdot3390 q}.
\]
For the combined rational caps the runner checks this is \(<.0995\), for rank \(\ge10\) alone \(<.04905\), moving the nonnegative rational terms to the right and squaring once. The pinned ExplicitTinyNegativeOverlap result already charges \(\mathcal A\cap\mathcal I\) itself and leaves \(+.130M\). Do not charge that overlap again; only this one incremental debit is applied to the canonical signed residual. No prior positive block is substituted or added a second time; no new copy of \(R_J\) enters the right side.
