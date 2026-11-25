# Rectangular spoke witnesses for alternating cycles

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Use the single-shared-tensor periodic model of [Gesmundo–Landsberg–Walter](https://arxiv.org/abs/1801.09106) over \(\mathbb C\). Let \(F_s(p,D)\) be the maximum odd/even flattening rank on the \(2s\)-cycle with \(p\) physical symbols and bond \(D\).

**Theorem.** If \(p=ab\) and \(D\ge a+b\), then \(F_s(p,D)=p^s\) for every odd \(s\). In particular, at **equal physical and bond dimension**, all composite dimensions have full alternating rank on every cycle of length \(2\bmod 4\). As a lower bound for any \(s\), the same slices have rank exactly \(p^s-\dim\ker(R+I)\), where \(R\) is ordinary rotation on words of length \(s\). With independent reverse weights they admit the exact monomial-balance formula below. This does not assert full rank for odd cycles at all prime dimensions, or for general even \(s\).

For square \(p\), the earlier matrix-unit example in [GLW, Remark I.6](https://arxiv.org/html/1801.09106#S1) attains full rank at a smaller bond for every \(s\). The interest here is a rectangular witness for nonsquare composite \(p\), e.g. \(p=6,10,12,14\), sharp in rank for odd \(s\).

## Two directed matchings

Index the physical letters by \(U\times V\), with \(|U|=a, |V|=b\); use a disjoint copy \(U\sqcup V\) as virtual states. Put \(A_{uv}=E_{u,v}+E_{v,u}\). For a word \(w=(u,v)\), write \(u=(u_0,\ldots,u_{s-1})\) and \(v=(v_0,\ldots,v_{s-1})\), and denote by \(\rho\) a left rotation. Let \(P_U e_{(u,v)}=e_{(\rho u,v)}\) and \(P_V e_{(u,v)}=e_{(u,\rho v)}\).

In a closed virtual walk all moves alternate between \(U\) and \(V\). If all odd slices go from \(U\) to \(V\), a fixed odd word \((u,v)\) forces the even word \((\rho u,v)\) and gives one trace term. If all odd slices go from \(V\) to \(U\), it forces \((u,\rho v)\) and gives one term. Coincident even words contribute twice. Thus the flattening is \(M=P_U^{-1}+P_V^{-1}\).

Multiplying on the left by \(P_U\) gives \(I+S\), where \(S=P_U P_V^{-1}\) has order dividing \(s\). In fact \(S\) is conjugate to ordinary rotation \(R\): reverse the positions of the \(V\) letters and \(S\) rotates both halves forward. Thus \(\operatorname{rank} M=p^s-\dim\ker(R+I)\), full for odd \(s\). Zero-padding increases \(D\) without changing entries. For any composite \(p=ab\) with \(a,b\ge2\), \(a+b\le ab=p\), giving the equal-dimension consequence.

## Exact generic rank in the weighted witness

More generally set \(A_{uv}=E_{u,v}+c_{uv}E_{v,u}\), with independent nonzero \(c_{uv}\). Put \(C_{w,w}=\prod_{j=0}^{s-1}c_{u_jv_j}\). The same walk count shows \(M=P_U^{-1}C+CP_V^{-1}\); multiplying on the left by \(C^{-1}P_U\) gives \(I+T\) with
\[
T e_w=\frac{C_{P_V^{-1}w,P_V^{-1}w}}{C_{Sw,Sw}}e_{Sw}.
\]
Each orbit \(\mathcal O\) of \(S\) is a separate weighted cyclic block. Its characteristic polynomial is \(\lambda^{|\mathcal O|}-\prod_{w\in\mathcal O} C_{P_V^{-1}w,P_V^{-1}w}/C_{w,w}\). Over the rational function field of the weights, it contributes one missing dimension precisely if its length is even and the ratio is identically 1, and otherwise none. Thus at generic numerical weights the defect equals the number of these even monomial-balanced orbits. In positional terms, for \(w_t=(\rho^t u,\rho^{-t}v)\), the denominator pairs \(u_j\) with \(v_{j-2t}\), and the numerator pairs \(u_j\) with \(v_{j-2t-1}\); multisets of pairs must agree over \(j\) and one full orbit. No equality with the true flow is asserted for even \(s\).

This witness is independent of the [rotation determinant and sufficiently large bond theorem](https://github.com/mxym/math/blob/a4586826b9eea5f400aafc2f37aeb998d8f6b495/research/euclidean-tensor-geometry/AlternatingCycleRotationDeterminant.md); it supplies a much smaller sufficient bond in an infinite family of exact cases.

For example, at \(s=2\) this weighted witness has defect \(a\binom b2+b\binom a2\): an orbit of length two is balanced exactly when at least one of its two coordinate words is constant. If neither is constant, the two distinct \(U\) letters and two distinct \(V\) letters give opposite diagonals of a \(2\times2\) product and independent weights, so the ratio is not 1. More generally every even orbit with a constant coordinate word is automatically balanced; diagonal weights of this form alone therefore cannot always reach the symmetry bound for even \(s\).
