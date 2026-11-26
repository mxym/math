# Every nontrivial fifth- or tenth-root norm quotient admits four colors

**Yongxian Zhang.** AI-assisted proof development and internal verification; no external review or priority claim.

Let \(\zeta=e^{2\pi i/5}\), \(t=\zeta+\zeta^{-1}\), so \(t^2+t-1=0\). For any nonzero nonunit \(\beta=A+Bt\in\mathbb Z[t]\), the Cayley graph of the additive quotient
\[
R=\mathbb Z[\zeta]/\beta\mathbb Z[\zeta]
\]
with steps all signed powers of \(\zeta\) has a proper four-coloring. Thus in [Davidson's monomial Cayley framework](https://arxiv.org/html/2610.09474v1), any trace polynomial \(F\) with \(|N(F(t))|>1\) or \(|N(F(-t))|>1\) gives four colors, for **arbitrary algebraic degree**. Evaluation at \(-\zeta\) corresponds to order ten and has the same signed steps. See his Theorem 2.9 for the earlier norm bound at fixed order with an unspecified threshold, and Lemma 2.10 for the explicit order-eight theorem. This is a separate improvement at orders five and ten, not the general monomial conjecture.

The [degree-sixteen companion proof](MonomialFourColorsDegreeSixteen.md) shows by dual-lattice rounding that norm \(D=|A^2-AB-B^2|\ge1600\) suffices. That argument uses only that \(\beta\) lies in the real quadratic ring, and thus applies directly here. It starts with the 1/3-separated character on the fifth-root directions and rounds it to a character on the quotient while moving each label by at most \(2\varphi/\sqrt D<1/12\), where \(\varphi=(1+\sqrt5)/2\).

For \(2\le D<1600\), use the same balancing by a power of the unit \(t\). The absolute ratio of the two embeddings can lie in \([\varphi^{-2},\varphi^2]\), so each conjugate has size at most \(\varphi\sqrt D<65\), using \(\varphi<13/8\). Their difference is \(B\sqrt5\), which gives \(|B|<60\) by \(\sqrt5>11/5\). Also \(|t|<2/3\) in the first embedding, so \(|A|<105\). All real ideals that can occur therefore appear among \(-104\le A\le104,\ |B|\le60\) with \(2\le D<1600\).

To give explicit finite replay, multiplication by \(\beta\) on the basis \(1,t\) has matrix
\[
M=\begin{pmatrix}A&B\\B&A-B\end{pmatrix}.
\]
Rather than checking every associate repeatedly, use a key for the image lattice \(M\mathbb Z^2\). Its image under projection to the second coordinate is \(g\mathbb Z\), \(g=\gcd(B,A-B)>0\). Its horizontal direction is \((D/g,0)\) up to sign because the full index is \(D\). Bézout for \(g\) gives one lattice vector \((r,g)\), with \(r\) well-defined modulo \(D/g\). Thus \((D,g,r\bmod(D/g))\) determines the lattice, and the corresponding real ideal, exactly. A change of generators with the same ideal does not change the complex quotient or step set.

There are **685** distinct keys in this finite screen. For 684 of them the [integer verifier](verify-monomial-order-five-quotients.js) supplies a character with all five positive labels, and hence all signed labels, at circular distance at least \(1/4\) from zero. This gives a proper coloring by quarter arcs. The character numerator has rows \((a,b)\) and \((c,d)\) for the two real coordinates \(1,t\) and \(\zeta,t\zeta\) modulo \(D\), each in the left kernel of \(M\). This kernel is enumerated by the adjugate rows modulo \(D\). Indeed a lift \(x\in\mathbb Z^2\) of a kernel row satisfies \(xM=Dz\), and \(x=(D/\det M)z\operatorname{adj}(M)\). Conversely every adjugate row is in the kernel. The five labels are \(a,c,d-a,-b-d,b-c\); these expressions follow from \(\zeta^2=t\zeta-1\) and \(t^2=1-t\). The checker recomputes both kernel equations and all five label inequalities on every successful certificate.

The only remaining key has \(D=4\) and ideal \((2)\) (the checked generator has both coefficients even and index four). In the additive quotient modulo two the four powers \(1,\zeta,\zeta^2,\zeta^3\) are a binary basis. Send the first three to \((1,0)\) and the fourth to \((0,1)\) in \(\mathbb F_2^2\). Then \(\zeta^4\) maps to \((1,1)\) by the fifth-root relation. This proper additive four-coloring finishes the unique exception.


For Davidson's named degree-twenty \(f_*\), the trace factors satisfy \(Q_*(t)=1\) and \(Q_*(-t)=-1\) by \(t^2+t-1=0\). Hence \(F(t)=F(-t)=1-t\), of norm 1. That example is not covered by the new criterion.
