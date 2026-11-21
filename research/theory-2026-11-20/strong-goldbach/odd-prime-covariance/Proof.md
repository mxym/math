# Polarization at the Pan cutoff and a bounded-rank true-prime row

Let \(P\) tend to infinity through even integers, \(I=[P/3,2P/3]\), \(X=P/3,\ L=\log P,\ Q=\sqrt P/L^{20}\), and \(S=\mathfrak S(P)=2C_2\prod_{\ell\mid P,\ell>2}(\ell-1)/(\ell-2)\), \(C_2=\prod_{\ell>2}(1-1/(\ell-1)^2)\), with primes indexed by \(\ell\). All additive sums here are over \(n+r=P,\ n,r\in I\); the two orientations are **not** added in a prime-versus-composite sum. Set
\[
 B(r)=-\sum_{d\mid r,\ d\le Q}\mu(d)\log d,\quad K(r)=\sum_{d\mid r,\ d\le Q}\mu(d),
 \quad V(r)=(\log r)1_{r\ {\rm prime}},\quad G_I=\sum V(n)V(r).
\]
Write \(\bar f=X^{-1}\sum_{n\in I}f(n)\) and \(C(f,g)=\sum f(n)g(r)-XS\bar f\bar g\). These empirical centers are used even for signed composite weights. Fix \(\eta=1/20000,\ \kappa=333/4000,\ Z=P^\kappa,\ z=P^\epsilon\), \(0<\epsilon\) sufficiently small. Put \(R_t=1_{P^->t}\) and
\[
 W_t=L K\mu^2R_t,\qquad J_t=B1_{\mu=-1}R_t,\qquad J_H=J_Z,\qquad J_L=J_z-J_Z.
\]
The \(H\) in \(J_H\) is a mnemonic, not a prime cutoff. All \(J\)'s vanish on primes; \(J_H\) is supported on squarefree ranks \(3,5,7,9,11\) only.

**Theorem.** If \(y=P^{\sqrt\epsilon}\) and \(J_M=J_y-J_Z\), then
\[
 G_I=XS+4\{C(J_M,J_M)-C(J_H,J_H)+C(V,J_H)\}
       +XS\,O(e(\epsilon))+o_\epsilon(XS),\qquad e(\epsilon)\longrightarrow0 .
 \tag{1}
\]
One may use \(J_L\) in place of \(J_M\). The limits mean first \(P\to\infty\), then \(\epsilon\downarrow0\). The two composite covariances in (1) need not factor. There is no prime-versus-even-rank composite term or mixed light–hard composite covariance in the formula.

Write \(D_j=\sum_{\Omega(r)=j} V(n)J_H(r)\), \(D_j^\pm=\sum_{\Omega(r)=j} V(n)[\pm J_H(r)]_+\). At the fixed critical cutoff, with normalization **\(XS\)**, not \(PS\),
\[
 \begin{array}{ll}
 \limsup D_5^-/(XS)<.835,\quad &D_3^-=o(XS),\\
 \limsup\sum_{j\ge7}D_j^-/(XS)<.0067,\quad&
 \limsup\sum_{j\ge7}D_j^+/(XS)<.037 .
 \end{array} \tag{2}
\]
All are unconditional for arbitrary even targets, not averages or the opposite Pan sign. In particular the sole reflected-prime covariance in (1) is
\[
 C(V,J_H)=D_3+D_5-XS\bar J_H +\mathcal E,\quad
 -.0067<\liminf\mathcal E/(XS)\le\limsup\mathcal E/(XS)<.037 .
\]
Also \(.490<\bar J_H<.502\) eventually. Equations (1)–(2) isolate the balanced triprime and signed five-prime terms, but do **not** give the sign of (1); even the total raw adverse prime-side bound \(<.842 XS\) is before the outer factor 4.

## 1. Two actual dispersion inputs

We detail the changes to [the critical parity transfer proof](../PanCriticalParityTransfer.md). Write \(u_t=L/(2\log t),\,s_t=\eta L/\log t\). For \(t=z,y\) we only use \(s_t\) large. The squarefree moving-wall identity in its §1 is
\[
 V(m)=(1-\mu(m))B_{\sqrt m}(m)+(\log m)K_{\sqrt m}(m).
\]
Consequently replacing either occurrence of \(V\) by \(W_t+2J_t\), *on the \(t\)-rough set*, has \(o_\epsilon(X)\) ordinary summed absolute error and \(o_\epsilon(XS)\) summed absolute error against any \(O_\epsilon(L)\) mate rough to \(z\). For the additive estimate sieve \(m/d\) and its reflected linear form to the smaller cutoff \(z\), as \(d\) at the moving wall is \(t\)-rough and thus \(z\)-rough. Sum reciprocals over rough wall divisors to get \(O_\epsilon(\log L/L)\); the two-form upper sieve, endpoint and \(\log m-L\) costs are spelled out in the cited §1. Outside the \(t\)-rough set all three weights vanish (all central true primes exceed \(t\)). Squareful rough inputs and inputs having a shared target prime can be dropped on either side with cost \(P^{1-\epsilon+o(1)}+P^{1/2+o(1)}\), even with fixed divisor powers. The estimate is valid against any weights or masks dominated by the indicated absolute envelopes.

First,
\[
 C(W_z,W_z)=O(XS u_z^4s_z^{-s_z/2})+o_\epsilon(XS).                         \tag{3}
\]
Use [critical composite dispersion](../PanCriticalCompositePolynomialSieve.md) and §2 of the parity transfer, now with signed coefficients \(L\mu(d),L\mu(e)\) on both inputs and envelope \(L\mu^2(d),L\mu^2(e)\). They are independent bounded coefficients of precisely the same lengths. For every compatible rough divisor pair the two linear forms have the small-prime product \(V_2=(1+o_\epsilon(1))S V_0^2,\ V_0=\prod_{\ell\le z}(1-1/\ell)\); each one-variable sieve has product \(V_0\). Writing \(H_z=\sum_{R_z(d),d\le Q}\mu(d)/d\), these give \(X V_2(LH_z)^2\) and \(V_0 LH_z\) for the two-variable sum and normalized one-variable mean respectively, before their beta-sieve widths. Common rough primes or target primes in a short divisor give negligible normalized cost. Each absolute normalized one-variable mass costs \(O(u_z^2)\) by the rough Euler upper bound. The one-variable width is \(O(u_z^2s_z^{-s_z/2})\); so replacing the product of model means by the empirical centers in (3) preserves its stated error. Signed beta bounds here and below use separately the positive-envelope upper-minus-lower width, not pointwise ordering after multiplying signed divisors.

Second, if \(f\) is any one of \(J_L,\ J_z-J_y,\ J_y-J_Z\), then for \(t=z,y\)
\[
 C(W_t,f)=O(XS u_z^2u_t^2s_t^{-s_t/2})+o_\epsilon(XS).                       \tag{4}
\]
For clarity, the dispersion input §3 of the parity transfer applies to the actual supported \(f\), not only a model. On squarefree arguments \(1_{\mu=-1}=(\mu^2-\mu)/2\). Tag one prime \(\ell\) in the actual window \((z,Z],(z,y]\), or \((y,Z]\) with weight reciprocal to the number of distinct primes in that window, imposing the corresponding lower roughness cutoff on \(m\) in \(r=\ell m\). For \((\ell,m)=1\) that weight is \(1/(1+\omega_{\rm window}(m))\). Both \(\mu^2\) and \(\mu\) separate there, and \(B(\ell m)=B(m)+\sum_{d\mid m,\,d\ell\le Q}\mu(d)(\log d+\log\ell)\). The same independent fine meshes in \(\ell,m,d\), divisor-moment cost of product boundaries and discarded squares as in the cited proof give arbitrary-log total discrepancy to \(q\le QP^\eta,\ (q,P)=1\), also for \(F=L\tau\mu^2\) restricted to the same window and support. For the upper short-prime segment of exponents \([.002,\kappa]\) the strict Fouvry limits are \((1+.002)/2>.50005\) and \(4/7-6\kappa/7>.50005\). Below .002 the unchanged macroscopic Fouvry–Radziwiłł proof uses \(36(.002)+33(.50005)<17,\ 15(.002+.50005)<8\), with fixed-power short-prime Siegel–Walfisz. On smaller \(q\) Fouvry again applies. Each cited estimate uses one common moving residue \(P\), rather than an estimate just at fixed small residue.

Now open \(W_t\) in \(t\)-rough divisors \(d\le Q\) and sieve the residual for primes \(\le t\). Small target primes dividing the reflected variable are removed by the negligible shared-target case, for physical and summed progression rows (on the latter use \(\tau(P-r)\) and harmonic moduli in the means). For other small primes the excluded density on the reduced classes is \(1/(\ell-1)\). A beta divisor \(w\le P^\eta\) is small-prime supported and coprime to \(dP\), so \(q=dw\) has at most one split. If \(f\) is only rough to \(z<t\), the coprime main at \(dw\) can still remove \((w,r)=1\) at negligible cost. For each \(r\) all its prime factors exceed \(z\), and
\[
 \sum_{\substack{w\le P^\eta\\(w,r)>1}}\mu^2(w)/\phi(w)
 \ll L^{O(1)}\sum_{\ell\mid r,\ell>z}1/\ell \ll L^{O(1)}/z .
\]
The harmonic \(d\)-sum with absolute coefficients is also log bounded. The positive envelope has \(\sum F\ll Xu_z^2\) by the divisor hyperbola on two rough factors in the cited §4. For the signed main, \(\sum_{d\le Q,R_t(d),(d,Pr)=1}\mu(d)/\phi(d)=H_t+o_\epsilon(L^{-A})\) for any fixed \(A\), by \(d/\phi(d)=1+O_\epsilon(1/t)\) and marking a prime dividing \(Pr\). The local product is \((1+o_\epsilon(1))S\prod_{\ell\le t}(1-1/\ell)\), as in the cited proof. Thus the difference from \(XS\bar W_t\bar f\) is covered by the signed/absolute beta widths above. This proves (4).

## 2. Exact polarization modulo the controlled errors

By the ordinary PNT, \(C(V,V)=G_I-XS+o(XS)\). Replacing \(V\) on both sides gives \(C(W_z,W_z)+4C(W_z,J_z)+4C(J_z,J_z)+o_\epsilon(XS)\). Use (3) and (4) to replace \(C(W_z,J_z)\) by \(C(W_z,J_H)\). The latter is \(C(V,J_H)-2C(J_z,J_H)+o_\epsilon(XS)\). Because \(C\) is symmetric, the mixed light–hard terms cancel identically. This proves (1) with \(J_L\). On the light band \((z,y]\), the moving-wall estimate gives \(2(J_z-J_y)=W_y-W_z\) up to the same summed errors, since the two prime functions agree everywhere. By (4), \(C(J_z-J_y,J_z-J_y)\) and \(C(J_z-J_y,J_y-J_Z)\) are therefore controlled by the widths for \(t=z,y\). This proves (1) as stated, with
\[
 e(\epsilon)=u_z^4s_z^{-s_z/2}+u_z^2u_y^2s_y^{-s_y/2}.
\]
The implied constant is absolute for sufficiently large \(s_y\). This double-light deletion uses actual tagged dispersion against a short-divisor sum; it does not assume joint equidistribution of two independent prime tags.

## 3. The ordinary hard center

On \(R_Z\) the same one-dimensional moving wall (fixed \(\kappa\)) gives \(2\bar J_H=1-\bar W_Z+o(1)\). Open \(LK\), temporarily omitting squarefreeness, which costs \(o(1)\). For fixed \(d\le Q,\ R_Z(d)\), the count \(m\in I/d\) of \(Z\)-rough numbers is
\[
 (X/d)(\log Z)^{-1}[\omega(1/\kappa-\log d/\log Z)+o(1)] .
\]
This follows uniformly by differencing the classical rough-number asymptotic ([de Bruijn, explicit treatment by Fan](https://arxiv.org/abs/2306.03347)): both endpoints have parameters in a compact subset of \((1,\infty)\) and differ by a bounded ratio. The rough-divisor harmonic measures \(\sum\mu(d)/d\,\delta_{\log d/\log Z}\) on the compact cutoff converge weakly to \(d\rho\), with the atom \(+1\) at 0, by the signed prime-simplex expansion [here](../PanGlobalRoughTransfer.md); total variation is bounded at fixed \(\kappa\). Thus
\[
 \bar W_Z=A_\kappa+o(1),\qquad
 A_\kappa=\kappa^{-1}\int_{[0,1/(2\kappa)]}\omega(1/\kappa-v)\,d\rho(v).
\]
The signed mass after its initial atom is nonpositive, its magnitude \(1-\rho(1/(2\kappa))\). For \(a\) a positive integer at least 2 and \(t\in[a,a+1]\), Buchstab's equation makes \(\omega(t)\) the convex combination of \(\omega(a)\) and the average of \(\omega(s-1)\) over \(a<s<t\), with the latter coefficient \((t-a)/t\le1/(a+1)\). The image interval is within the preceding unit interval's value hull, and its diameter is at most the preceding diameter divided by \(a+1\) (contract toward \(\omega(a)\), using the maximal contraction coefficient). On \([1,2]\) the diameter is \(1/2\); hence for all \(t\ge6\) values lie in one interval of diameter at most \(1/5040\). All \(\omega\)-arguments here exceed 6. From \(t\rho(t)=\int_{t-1}^t\rho(s)\,ds\), monotonicity gives \(\rho(1/(2\kappa))\le 1/720\). Since \(0\le\omega\le1\),
\[
 -1/(5040\kappa)\le A_\kappa\le (1/720+1/5040)/\kappa .
\]
This proves the stated ordinary mean bounds, not a prime-reflected mean. For (2) see [the physical envelope and exact cells](PrimeEnvelope.md).

This criterion concerns actual primes at each large target. Classical [Pan–Huang–Li](https://arxiv.org/abs/2005.03811) and the earlier linked transfer and dispersion results are inputs/antecedents. No Goldbach asymptotic, eventual positivity, or priority for the generalized distribution theorem is claimed.

## Comparison with 2026 work

[Arneth's 19 October cubic minorant](https://zenodo.org/records/23477014) also separates the semiprime part but retains a different long signed operator. [Pham's 30 October v1](https://www.preprints.org/manuscript/202610.3061) treats other rough comparisons and covariance criteria. [Calzado, 7 October](https://math.colgate.edu/~integers/aa117/aa117.pdf), uses distribution of a different weighted sifted sequence and additional conditions in a prime-detecting sieve. Here the polarization is for the actual original Pan cutoff; the certified upper bounds pertain only to one true-prime side and do not settle the two composite covariances.
