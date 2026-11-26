# Frobenius rigidity of bounded nontrivial shifts for the Paley two-localized dual

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review or priority claim.

This is an unconditional identity and a conditional asymptotic restriction on the explicit family in [PaleyFourierLaplacianDual.md](PaleyFourierLaplacianDual.md). It neither verifies nor refutes [the full two-localization theta conjecture](https://arxiv.org/abs/2603.29571).

In the notation of that family, \(p\equiv1\pmod4\), \(B\) its square torus of order \(m=(p-1)/2\), \(f(u)=\chi(1-u)\), \(g_t(u)=(f(tu)+f(t^{-1}u))/2\), \(\Delta_t=\Delta_{g_t}\), \(C\) the localized zero-diagonal Seidel matrix on \(n=(p-5)/4\) vertices. Index shifts by one representative \(t\) per inversion orbit in \(B\setminus\{1\}\); thus \(-1\) is a possible shift. For \(R=\sum b_t\Delta_t\) and \(L=\sum |b_t|\) one has uniformly
\[
\frac{\operatorname{tr}(R^2)}{np}
=\frac12\sum_{t\ne\pm1} b_t^2+b_{-1}^2+O(L^2/\sqrt p),\qquad
\frac{\operatorname{tr}(CR)}{np}=O(L/\sqrt p).
\]
This is unconditional, including a number of shifts growing with \(p\).

Let \(P\) project off the all-ones direction, \(X=PCP/\sqrt p\), \(Y=PRP/\sqrt p\). The preceding equations hold also with the corresponding normalized traces of \(Y^2\) and \(XY\), since the operator norm bounds \(\|C\|\le\sqrt p\) and \(\|R\|\le L(4\sqrt p+2)\) bound the deleted terms by \(O((L^2+L)/p)\). Also \(\operatorname{tr}Y/n=O(L/p)\). In particular the nontrivial shifts add a squared coefficient penalty to the compressed second moment and are asymptotically orthogonal to the Seidel matrix.

## Exact torus counting

Define \(E_t(z,w)=(f(u)-f(v))(g_t(u)-g_t(v))\) where \(u=w/z,\ v=wz\). The map \((z,w)\mapsto(u,v)\) from \(B^2\) has exactly two preimages for pairs in the same coset of \(B^2\subset B\) (solve \(z^2=v/u\)). All \(z,w=\pm1\) rows/columns vanish, and the map to physical matrix entries has four lifts for each, except the discarded fixed points which already contribute zero. Therefore \(\operatorname{tr}(\Delta_t\Delta_s)\) equals one half the sum over same-coset ordered pairs \(u,v\) of
\((f(u)-f(v))^2(g_t(u)-g_t(v))(g_s(u)-g_s(v))\), up to \(O(p)\) from deleting the diagonal. The single zero \(f(1)\) contributes \(O(p)\) also. For each coset let \(B_\pm\) be its two sign classes; their sizes are \(m/4+O(\sqrt p)\). In the main sum only opposite signs contribute, giving
\[
4\sum_{\mathrm{cosets}}\!\left(
|B_-|\sum_{u\in B_+}g_tg_s+
|B_+|\sum_{v\in B_-}g_tg_s
-\Big(\sum_{B_+}g_t\Big)\Big(\sum_{B_-}g_s\Big)
-\Big(\sum_{B_+}g_s\Big)\Big(\sum_{B_-}g_t\Big)\right).
\]
For \(t\ne1\) each sum of \(g_t\) over a sign class is \(O(\sqrt p)\): expand the sign indicator and coset indicator using a quartic multiplicative character; products involve \(u,1-u,1-tu\) or \(1-t^{-1}u\), with the nonzero roots distinct. The Weil bounds are uniform. The same calculation with \(f\) alone estimates the class sizes. Thus the main expression is \(m\sum_{u\in B}g_t(u)g_s(u)+O(p^{3/2})\).

For translates \(f(au),f(bu)\), the latter inner product without inversion averaging is \(m+O(1)\) when \(a=b\), and \(O(\sqrt p)\) otherwise (ordinary Weil applied after inserting the square indicator). After inversion averaging this is \(m/2+O(\sqrt p)\) for \(t=s\ne-1\), \(m+O(1)\) for \(t=s=-1\), and \(O(\sqrt p)\) otherwise. Since \(m^2/(np)=1+O(1/p)\), this gives the first formula. Finally \(\operatorname{tr}(C\Delta_t)=-\sum_{x,y}(\Delta_t)_{xy}\), since the correction is supported on localized nonedges. The same lift counts and the \(O(\sqrt p)\) sign-class sums of \(g_t\) give \(O(p^{3/2})\) for this pairing.

## Conditional consequences for the leading constant, using only the weak bulk law

Assume Kunisky [Conjecture 1.8, degree 2](https://arxiv.org/abs/2303.16475). The independent-anchor common nonneighbor and clique-anchor common neighbor versions differ by multiplication by a nonsquare, reversing the Seidel sign. Since the law is symmetric, the ESD of \(X\) converges to \(\mu\), the KM(4) law divided in its argument by 4 (law of \(Z/4\) for \(Z\sim\mathrm{KM}(4)\)); use a rank-one interlacing argument to convert adjacency to Seidel and to compress. The density of \(\mu\) is \(2\sqrt{3/4-x^2}/(\pi(1-x^2))\) on \([-\sqrt3/2,\sqrt3/2]\), with mean zero and variance \(1/4\). No strong edge convergence is needed.

Consider a family of duals \(M=I+C+\alpha\Delta_f+R\), with bounded \(L\). If \(\lambda_{\max}(M)=O(\sqrt p)\), its all-ones Rayleigh quotient forces \(\alpha\le O(p^{-1/2})\), using \(\Delta_f=2(J-I-C)\) and the operator bounds. The weak positive bulk edge on the compression forces \(\alpha\) to be bounded below as well: on an eigenvector of \(X\) with positive eigenvalue at least some fixed \(x_0>0\), the normalized Rayleigh quotient is \((1-2\alpha)(x_0+O(p^{-1/2}))+O(L)\) or larger when \(\alpha<0\), so \(\alpha\to-\infty\) is impossible. Thus compression of the scaled dual equals \((1-2\alpha)X+Y+o(1)I\) as operators, and \(1-2\alpha\ge1-o(1)\).

If the shift weights are diffuse, i.e. \(\max_t|b_t|\to0\) while \(L=O(1)\), then the normalized Frobenius norm of \(Y\) goes to zero. Hoffman–Wielandt with the weak bulk law implies \(\liminf \lambda_{\max}(M)/\sqrt p\ge\sqrt3/2\): any constant positive distance below that would require moving a positive density of eigenvalues by a positive constant. This is a barrier for diffuse bounded shift coefficients, not for localized/atomic coefficients, unbounded \(L\), or the entire span (which need not have a diffuse bounded representative).

More quantitatively let \(0<c<\sqrt3/2\) and suppose the leading dual upper bound is \(c\). Put \(h(x)=(x-c)_+\), \(I_j=\int h^j\,d\mu\) and \(J_1=\int xh(x)\,d\mu\). Testing the matrix upper bound with the positive semidefinite \(h(X)\) gives \(\operatorname{tr}(h(X)Y)/n\le-I_2+o(1)\), since \(h(x)\) is supported on \(x\ge c>0\) and \(1-2\alpha\ge1-o(1)\). By the two orthogonality estimates one may subtract from \(h\) its \(L^2(\mu)\) projection \(I_1+4J_1x\) without changing the limit pairing. Cauchy–Schwarz and the Gram formula therefore force
\[
\liminf_p\left(\frac12\sum_{t\ne\pm1} b_t^2+b_{-1}^2\right)
\ge \frac{I_2^2}{I_2-I_1^2-4J_1^2}.
\]
The denominator is strictly positive since \(h\) is not affine on the support. At \(c=2/3\) the right side is about \(0.00180254\) (numerical quadrature only; the expression is exact). Hence under the weak bulk law, reaching the conjectured constant with bounded dictionary mass requires nonvanishing coefficient energy, despite the freedom to use more and more character shifts. This does not show existence of such an upper bound or a barrier against every atomic direction.


## Intrinsic decomposition and an energy test for the entire correction span

There is an exact version of the parity/sign decomposition, without a dictionary coefficient bound. For an arbitrary real even \(g\), and the coset \(c=\pm1\) of the quadratic character \(\epsilon\) of the cyclic group \(B\), let \(m_{c,\sigma}(g)\) be the mean of \(g\) over the \(f=\sigma\) class in that coset, \(\sigma=\pm1\). These classes are nonempty for sufficiently large \(p\) by their sizes \(m/4+O(\sqrt p)\). The value at \(u=1\), the only point with \(f=0\), can be ignored entirely: any pair with \(u=1\) or \(v=1\) represents a physical diagonal. Likewise an opposite-sign pair cannot have \(u=v\) or \(u=v^{-1}\), so it does not come from a removed \(z,w=\pm1\) point. Write \(g^\circ\) for the sign-centered \(g-m_{c,\sigma}(g)\) on these classes, and \(n_{c,\sigma}\) for their sizes. The exact Gram formula is
\[
\operatorname{tr}(\Delta_g\Delta_h)=4\sum_c\bigg[
n_{c,-}\sum_{c,+}g^\circ h^\circ+
n_{c,+}\sum_{c,-}g^\circ h^\circ+
n_{c,+}n_{c,-}\,\big(m_{c,+}(g)-m_{c,-}(g)\big)\big(m_{c,+}(h)-m_{c,-}(h)\big)
\bigg].
\]
It is just the preceding lift identity, with the diagonal and fixed points excluded exactly rather than estimated. Let \(D_0\) be the diagonal sign matrix of vertex parities \(\epsilon(z)\) at the quotient vertex \(q(z)\). Since \(\epsilon(w/z)=\epsilon(wz)=\epsilon(w)\epsilon(z)\), the class means give the decomposition
\[
\Delta_g=\alpha\Delta_f+\beta D_0\Delta_fD_0+R,\qquad R=\Delta_{g^\circ},
\]
where \(a_c=(m_{c,+}(g)-m_{c,-}(g))/2\), \(\alpha=(a_++a_-)/2\), \(\beta=(a_+-a_-)/2\), with per-coset constants in the kernel. In this formula \(\operatorname{tr}(CR)=\operatorname{tr}(D_0 C D_0 R)=0\), because on every opposite-sign pair \(C=-1\) and \(D_0CD_0=-c\) while the sign-centered sum within each coset is zero. Equally, \(\boldsymbol1^\top R\boldsymbol1=(D_0\boldsymbol1)^\top R(D_0\boldsymbol1)=0\) exactly. The parities on the physical vertices satisfy \(\sum_x (D_0)_{xx}=-(1+\epsilon(-1))/2\), bounded by 1 in absolute value, so \(\operatorname{tr}(C D_0 C D_0)=(\sum_x (D_0)_{xx})^2-n\).

Under the same weak bulk law as above, let \(I+C+\Delta_g\) have leading upper constant \(c\in(0,\sqrt3/2)\). Then **for any sequence of corrections in the span**, without any representation-dependent \(\ell^1\) assumption,
\[
\liminf_{p\to\infty}\left(\beta^2+\frac{\operatorname{tr}(R^2)}{np}\right)
\ge \frac{I_2^2}{I_2-I_1^2-4J_1^2}.
\]
To prove it, it suffices to work along a subsequence of bounded energy; otherwise the bound is automatic. Thus \(\beta=O(1)\) and \(\|R\|\le\|R\|_F=O(p)\). Let \(P\) now omit both \(\boldsymbol1\) and \(D_0\boldsymbol1\), \(X=PCP/\sqrt p\), \(X_2=PD_0CD_0P/\sqrt p\), and \(Y=PRP/\sqrt p\). We write normalized traces as \(\operatorname{tr}(\cdot)/n\). Finite-rank loss in cross pairings with \(X,X_2\) is \(O(p^{-1/2})\) since \(C,D_0CD_0\) have operator norm at most \(\sqrt p\), and loss between them is \(O(p^{-1})\). Likewise \(\operatorname{tr}(Y)/n=O(p^{-1/2})\). The exact raw all-ones cancellation for \(R\), together with \(|\sum D_0|\le1\) and bounded \(\beta\), forces \(\alpha\le O(p^{-1/2})\) as before. On the compressed space the scaled witness is
\[
(1-2\alpha)X-2\beta X_2+Y+(1-2\alpha-2\beta)P/\sqrt p .
\]
Testing it against \((X-x_0 P)_+\) for any fixed \(0<x_0<\sqrt3/2\) also forces \(\alpha\) bounded below: the trace pairing of the \(X\)-term grows linearly in negative \(\alpha\) by the positive weak bulk mass, the scalar term is nonnegative once \(\alpha\) is sufficiently negative, and the \(X_2,Y\) pairings stay bounded by Frobenius Cauchy–Schwarz. Thus the scalar identity coefficient is \(o(1)\).

Use \(Y'=-2\beta X_2+Y\) in the previous positive spectral test. It is asymptotically orthogonal to \(I,X\) by the exact trace identities and the finite-rank estimates, and
\[
\operatorname{tr}((Y')^2)/n\ \le\ \beta^2+\operatorname{tr}(R^2)/(np)+o(1).
\]
Here \(\operatorname{tr}(X_2^2)/n=1/4+O(1/p)\), the squared compressed norm of \(R\) is at most its raw squared norm, and its cross term with \(X_2\) is \(o(1)\). This proves the intrinsic energy test. It is a necessary quantitative condition, not an exclusion of every dual in the span.


## Best scalar regression bound from these orthogonalities, at the 2/3 target

For \(c=2/3\) a sharper exact integral follows by using \(h_t(x)=(x-t)_+\) with \(0<t<c\). Define \(I_j(t)=\int h_t^j\,d\mu\), \(J(t)=\int xh_t(x)\,d\mu\), and choose \(t\) to satisfy
\[
c=\frac{t+I_1(t)}{1-4J(t)}.
\]
A root exists: the denominator is at least \(1/2\) for \(t\ge0\), the right-hand side at zero is \(2I_1(0)=\int |x|\,d\mu\le1/2<c\), and at \(t=c\) it exceeds \(c\). The test with \(h_t(X)\) rather than \(h_c(X)\) gives negative pairing of magnitude at least \(I_2(t)+(t-c)I_1(t)\), since \(t>0\). In either energy estimate above, this yields the sharpened bound
\[
\frac{I_2(t)-I_1(t)^2-4J(t)^2}{(1-4J(t))^2}.
\]
In fact in the scalar relaxation with a function \(r\) of the bulk eigenvalue, \(r(x)\le c-x\) and \(\int r=\int xr=0\), this is optimal. Define \(r_*=-(h_t-I_1(t)-4J(t)x)/(1-4J(t))\); it is orthogonal to \(1,x\), equals \(c-x\) for \(x\ge t\), and lies below \(c-x\) for \(x<t\). Test any such \(r\) with \(h_t\), which gives \(\langle h_t,r\rangle\le\langle h_t,r_*\rangle\), and project off \(1,x\). Since \(r_*\) is a negative multiple of the projected test, Cauchy–Schwarz proves \(\|r\|_2\ge\|r_*\|_2\). Numerically \(t\approx0.61421131\) and the bound is approximately \(0.0019018572\); these decimals are numerical quadrature, not part of the exact proof. The optimization is of the scalar relaxation only, not realizability of this profile by the Fourier dual family.


Run the [exact parity checker](verify-paley-parity-gram.js) with Node.js. It checks the quotient signs, Gram identity and centered cancellations on 42 primes, totaling 95,656 ordered nonedge entries. The asymptotic claims follow from the proof rather than the finite checks.
