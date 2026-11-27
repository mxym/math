# A sharp relative-entropy bound for one-way mixtures

All logarithms are natural. For \(K>1\), let
\[
g_K(t)=
\begin{cases}
h(t)+t\log(K-1),&0\le t\le 1-K^{-1},\\
\log K,&1-K^{-1}\le t\le1,
\end{cases}
\qquad h(t)=-t\log t-(1-t)\log(1-t),
\]
and set \(g_1=0\). This note gives a sharp general bound for one-way Loewner domination, applies it to quantum mutual information, and distinguishes this from an unresolved trace-distance-only question.

## 1. State-dependent sharp relative-entropy bound

Let \(\sigma,\omega,Q\) be finite-dimensional density operators and assume
\(\omega\ge(1-t)\sigma\), \(0\le t\le1\). Write \(a=D(\sigma\Vert Q)\), with \(D\) the Umegaki relative entropy. For finite \(a\),
\[
\boxed{
D(\omega\Vert Q)\ \ge\
\begin{cases}
d_{\rm bin}(1-t\Vert e^{-a}), & 0\le t\le1-e^{-a},\\
0,&1-e^{-a}\le t\le1,
\end{cases}}
\tag{1}
\]
where \(d_{\rm bin}(p\Vert q)=p\log(p/q)+(1-p)\log((1-p)/(1-q))\) in its usual extended sense. Equivalently, \(D(\sigma\Vert Q)-D(\omega\Vert Q)\le g_{\exp a}(t)\) when \(a\) is finite. Both branches are sharp for every finite \(a\) and \(t\). Unlike an upper bound on \(D_{\max}(\sigma\Vert Q)\), the input to (1) is the actual Umegaki relative entropy.

### An elementary classical splitting

Put \(k=1-t\) and first assume \(0<k<1\). For probability measures \(P,R,Q_0\) with \(R\ge kP\) and finite \(a=D(P\Vert Q_0)\), the result is immediate if \(R\not\ll Q_0\). Otherwise let \(p,r\) be their densities with respect to \(Q_0\). Add a binary flag to both measures \(R,Q_0\), with the **same** conditional flag probability \(kp/r\) given the original sample, taken as zero when \(r=0\). Denote the lifted measures by \(\widetilde R,\widetilde Q\). Then \(D(\widetilde R\Vert\widetilde Q)=D(R\Vert Q_0)\). Under \(\widetilde R\) the flag has weights \(k,t\), and the first conditional sample law is \(P\). Denote the two conditional laws including their flags by \(P_1,P_0\), respectively. In the first flag,
\[
a'=D(P_1\Vert\widetilde Q)=\int p\log(r/k)\,dQ_0\ \ge \int p\log p\,dQ_0=a.
\]
The inequality uses \(r\ge kp\) on the support of \(p\); if \(a'=\infty\) the chain rule already gives an infinite left-hand side. Write \(q_1=\widetilde Q(\text{first flag})\). Binary data processing gives \(a'\ge-\log q_1\) and \(D(P_0\Vert\widetilde Q)\ge-\log(1-q_1)\). In particular \(D(P_0\Vert\widetilde Q)\ge-\log(1-e^{-a'})\). The disjoint-flag identity therefore gives
\[
D(R\Vert Q_0)
=k a'+tD(P_0\Vert\widetilde Q)-h(t)
\ \ge\ \phi_t(a'),\qquad
\phi_t(s)=ks-h(t)-t\log(1-e^{-s}).
\]
If \(a\ge-\log k\), \(\phi_t'(s)=k-t/(e^s-1)\ge0\) for \(s\ge a\). Thus the last expression is at least \(\phi_t(a)=d_{\rm bin}(k\Vert e^{-a})\). If \(a<-\log k\), nonnegativity suffices.

### From quantum testing curves to the classical comparison

It suffices to treat \(Q\) faithful: if \(a<\infty\) then \(\sigma\) is supported on \(\operatorname{supp}Q\), and either \(\omega\) is also so supported or its relative entropy is infinite. For \(u\ge0\) set \(F_X(u)=\operatorname{Tr}(X-uQ)_+\). The positive part trace is the supremum of \(\operatorname{Tr}E(X-uQ)\) over effects \(0\le E\le I\). In particular, \(F_\sigma\) is convex, nonincreasing, equal to 1 at 0, has slopes in \([-1,0]\), and vanishes for all sufficiently large \(u\).

For such a curve there is a probability measure \(\mu\) on \([0,\infty)\) with mean 1 and
\[
F_\sigma(u)=\int (x-u)_+\,d\mu(x).
\tag{2}
\]
Indeed, set \(\mu((u,\infty))=-F'_{\sigma,+}(u)\) for \(u\ge0\) and use an atom at zero for the remaining mass. Integration of the right derivative gives (2), and \(F_\sigma(0)=1\) is the mean. This is a classical representation of **one test curve**, not an assertion that there is a single physical measurement jointly realizing all its optimal tests.

The integral formula from [Frenkel](https://doi.org/10.22331/q-2023-09-07-1102) and its [hockey-stick formulation](https://arxiv.org/html/2408.15226v2#S1) give, for natural logarithms,
\[
D(X\Vert Q)=\int_0^\infty\frac{F_X(u)-(1-u)_+}{u}\,du.
\tag{3}
\]
For \(u\ge1\) this is the first term of the usual integral from 1 to infinity; for \(u<1\), use
\(\operatorname{Tr}(X-uQ)_+-(1-u)=u\operatorname{Tr}(Q-u^{-1}X)_+\)
and substitute \(u^{-1}\). The same identity holds for a classical density by integrating the scalar positive part, with Tonelli's theorem for the nonnegative remainder. In particular, the relative entropy of the density \(x\) with respect to \(\mu\) is \(a\).

By domination and the variational formula,
\[
F_\omega(u)\ge \max\{(1-u)_+,\,kF_\sigma(u/k)\}.
\]
Choose \(b\in[0,1]\) so that \(r(x)=\max(kx,b)\) integrates to 1 against \(\mu\); existence follows by continuity, since the integrals at \(b=0,1\) are respectively \(k\) and at least one. For \(u\le b\), the test curve of \(r\) is exactly \(1-u\); for \(u\ge b\), it is \(kF_\sigma(u/k)\). It is therefore pointwise no greater than \(F_\omega\). Equation (3) implies \(D(\omega\Vert Q)\ge D(r\mu\Vert\mu)\). The classical argument applies to \(r\ge kx\), proving (1). The cases \(t=0,1\) are immediate.

For each \(a\ge0\), take the two-point reference \(Q=(e^{-a},1-e^{-a})\) and \(\sigma=(1,0)\). When \(k\ge e^{-a}\), use \(\omega=(k,1-k)\); otherwise use \(\omega=Q\). This proves sharpness, including the transition.

## 2. Mutual information: one-way noise and exact equal-marginal cases

Let \(I(X)=I(A:B)_X\), and let \(d=\min(\dim A,\dim B)\). When \(d=1\), all mutual informations below are zero; take \(d\ge2\) for the nontrivial formulas. Under the same one-way order \(\omega\ge(1-t)\sigma\),
\[
\boxed{I(\sigma)-I(\omega)\le g_{\exp I(\sigma)}(t)\le g_{d^2}(t).}
\tag{4}
\]
No common marginal is needed for this **signed** inequality. To prove it for \(0<t<1\), use \(Q=\omega_A\otimes\omega_B\), which supports both joint states by domination. Then
\[
D(\omega\Vert Q)=I(\omega),\qquad
a=D(\sigma\Vert Q)=i+\ell,\quad i=I(\sigma),\quad
\ell=D(\sigma_A\Vert\omega_A)+D(\sigma_B\Vert\omega_B)\ge0.
\]
If \(i\le-\log(1-t)\), the plateau \(g_{\exp i}(t)=i\) and nonnegativity of \(I(\omega)\) suffice. If \(i>-\log(1-t)\), (1) yields
\[
I(\sigma)-I(\omega)\le h(t)+t\log(e^{i+\ell}-1)-\ell.
\]
The right side is nonincreasing in \(\ell\ge0\), because its derivative is \(t/(1-e^{-(i+\ell)})-1\le0\). Set \(\ell=0\). Finally \(i\le2\log d\) and \(g_K(t)\) is nondecreasing in \(K\).

If one marginal, say \(A\), is fixed, write \(\omega=(1-t)\sigma+tZ\). For \(t>0\) the density \(Z\) has the same \(A\)-marginal. Mutual information is convex on this fiber, by joint convexity of \(D(X\Vert X_A\otimes X_B)\), so the opposite difference is at most \(2t\log d\le g_{d^2}(t)\). The latter inequality follows from concavity of \(g_{d^2}\) and its endpoint values. In particular, the two-sided proposed modulus holds for equal-marginal pairs whenever the one-way order holds at the parameter \(t\), in either orientation. It is sharp in this class: on a \(d\times d\) subspace use a maximally entangled pure state \(\Phi\) and \(\omega=(1-s)\Phi+s(I-\Phi)/(d^2-1)\), where \(s=\min(t,1-d^{-2})\). The marginals are unchanged, \(T(\Phi,\omega)=s\), and \(I(\Phi)-I(\omega)=g_{d^2}(t)\).

In general, \(T(\sigma,\omega)\le t\) does **not** imply \(\omega\ge(1-t)\sigma\). Even two nonidentical rank-one states have no such domination for \(t<1\). Thus (4) is not a trace-distance-only bound; it applies with the actual distance for an orthogonal contamination mixture, but an overlapping mixture may have strictly smaller actual distance than the mixture fraction.

## 3. The classical fixed-one-marginal question and classical–quantum subcases

For classical tables with one common marginal, the exact uniform modulus is \(g_d(t)\), with \(d=\min(|A|,|B|)\). To see this, take \(A\) to be the common marginal and let the actual variation distance be \(u\le t\).

* If \(|A|\le|B|\), the mutual-information difference is the difference of conditional entropies \(H(A\mid B)\), bounded by [Alhejji–Smith](https://arxiv.org/abs/1909.00787).
* If \(|B|<|A|\), conditionally on \(A=a\) maximally couple the two output distributions as \(B,B'\). Then their overall error probability is exactly \(u\), and
\[
 I(A:B)-I(A:B')=I(A:B\mid B')-I(A:B'\mid B)\le H(B\mid B').
\]
Fano's elementary error-indicator argument bounds the latter by \(h(u)+u\log(|B|-1)\); reverse the two outputs for the other sign and use the increasing capped function \(g_{|B|}\). A uniform noiseless diagonal channel on \(d\) symbols and its \(d\)-ary symmetric crossover version achieve equality, including the plateau using \(u=1-1/d\).

For quantum states with one common marginal and **both** states block diagonal in the same local basis on either register, even without the one-way order the proposed, less restrictive bound \(g_{d^2}(t)\) holds. Here is a trace-distance proof. Write \(\sigma-\omega=u(U-V)\) for the normalized Jordan parts; they retain the same classical register and \(U_A=V_A\). Both pairs \((\sigma,V)\) and \((\omega,U)\) have the same mixture \(\eta=(\sigma+uV)/(1+u)=(\omega+uU)/(1+u)\). In either associated binary flagged state, the chain rule is
\[
I(A:B)_\eta
= \frac{I(A:B)_{\rm first}+u I(A:B)_{\rm second}}{1+u}
+I(A:F)-I(A:F\mid B).
\]
The two \(I(A:F)\) terms are equal because the corresponding \(A\)-marginals are equal. Each \(I(A:F\mid B)\) lies in \([0,h(u/(1+u))]\), since \(F\) is classical. All four endpoints and Jordan states have mutual information in \([0,\log d]\) by the classical–quantum Holevo bound. Subtracting gives the bound
\[
|\Delta I|\le
\min\big\{\log d,\ u\log d+(1+u)\log(1+u)-u\log u\big\}.
\tag{5}
\]
This is the usual fixed-marginal mixing argument, compare [Shirokov](https://arxiv.org/abs/1512.09047). To check that (5) implies \(g_{d^2}(u)\), set \(f(u)=(1+u)\log(1+u)+(1-u)\log(1-u)\), which is convex with \(f(0)=0\). For \(d=2\) and \(u\le1/4\),
\[
f(u)/u\le 4 f(1/4)=\log(84375/65536)<\log(3/2).
\]
For \(d\ge3\) and \(u\le1/2\), \(f(u)/u\le 2f(1/2)=\log(27/16)<\log(8/3)\le\log((d^2-1)/d)\). At the respective cutoffs \(g_4(1/4)=\log(4/\sqrt3)>\log2\) and \(g_{d^2}(1/2)=\log(2\sqrt{d^2-1})>\log d\), so the first term in (5) handles the rest. Monotonicity extends to the upper distance parameter \(t\).

## Scope and comparison with the literature

[Berta, Lami and Tomamichel, Eq. (106)](https://arxiv.org/html/2408.15226v2#S4) ask about a \(g_{d^2}\) mutual-information modulus; the unrestricted formulation has an earlier [ternary counterexample in this repository](https://github.com/mxym/math/blob/codex/mutual-information-written-v1-20261009/notes/mutual-information-continuity-counterexample/paper.md). [Berta et al., Thm. 1.1 and Prop. 3.1](https://arxiv.org/html/2607.24687v2) already furnish the exact \(g_{d^2}\) bound when the common marginal belongs to a smaller (or equal-sized) register, by applying conditional entropy to that register. They do not by this argument cover the opposite ordering. General quantum states with the **larger** marginal fixed and only a trace-distance hypothesis are not resolved here.

The [semicontinuity theorem of Berta, Lami and Tomamichel](https://arxiv.org/html/2408.15226v2#S2) accommodates general trace-distance perturbations using an operator bound \(\sigma\le K Q\); (1) instead assumes one-way domination by the perturbed state and uses \(K=\exp D(\sigma\Vert Q)\), which need not bound \(\sigma\) from above. Neither hypothesis is substituted for the other. The hockey-stick representation and information-ordering framework are prior tools; see [Dasgupta, Warsi and Hayashi](https://arxiv.org/abs/2511.01467) and [Hiai, Mosonyi and Tomamichel](https://arxiv.org/abs/2607.08760). [Gao and Zhao](https://arxiv.org/html/2608.19685v1) give related relative entropy ratios for different mixture classes, in particular interpolation toward the fixed reference. A targeted search of these and related works did not locate the exact fixed-\(D\) envelope (1); this is not a priority claim. This AI-assisted research note is neither externally peer-reviewed nor Lean-verified.

The [standard-library verifier](verify_one_way_relative_entropy.py) replays the classical clipping and flag identities, independent rational logarithm enclosures in a nontrivial finite test family, and the isotropic sharpness construction. The general proof is the analytic argument above, not an extrapolation from these tests.
