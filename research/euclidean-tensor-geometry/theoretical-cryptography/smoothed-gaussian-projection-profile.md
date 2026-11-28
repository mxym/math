# A uniform total-variation profile for smoothed projections of lattice Gaussians

A projection of a discrete Gaussian onto an irrational subspace may have a dense *countable* support rather than a lattice. Nevertheless, adding continuous Gaussian noise can make its projected law close to its continuous counterpart. We give an exact asymptotic total-variation profile, uniformly over the projection and noise width, through an ordinary heat kernel on a transformed dual lattice. In the critical volume window, the answer depends on the evolving lattice shape, not just on the volume. In two dimensions even a fixed quadratic irrational direction can produce nonconstant periodic dependence on logarithmic scale.

This is a theorem about centered, standalone Gaussian measures. We do not implement a sampler, apply it to any scheme, or draw a conclusion about an actual security reduction. [Genise–Micciancio–Peikert–Walter, §3 and footnote 8](https://web.eecs.umich.edu/~cpeikert/pubs/gaussians.pdf) note explicitly the dense projected-support obstruction and restrict their discrete transformation theorem to a lattice-subspace kernel. The completion of squares and Poisson summation used here are standard. Our new statements concern the *full total-variation profile with continuous padding*, including the critical and under-smoothed windows. For the generic trajectory statement below, we use [Kleinbock–Shi–Weiss, Theorem 1.1](https://arxiv.org/pdf/1505.06717), not a new homogeneous equidistribution theorem.

## 1. Setup and main result

Fix a full lattice \(\Lambda\subset\mathbb R^d\), \(d\ge2\), with Euclidean dual \(\Lambda^*\). Let \(X_s\) be the lattice Gaussian with masses proportional to \(e^{-\pi\|x\|^2/s^2}\), \(x\in\Lambda\). For any \(r\)-plane \(U\), \(1\le r<d\), let \(P\) be its orthogonal projection, and let \(P^\perp=I-P\). Independently put continuous Gaussian noise \(Z_h\) of density \(h^{-r}e^{-\pi\|y\|^2/h^2}\) on \(U\), with \(h>0\). Denote by \(p_{s,h,U}\) the law of \(P X_s/s+Z_h\), and by \(q_{h,U}\) the continuous Gaussian of width \(\sqrt{1+h^2}\) on \(U\). The latter is what one gets with a continuous width-\(s\) input in place of \(X_s\).

For a full lattice \(L\), put
\[
 H(L)=\operatorname{TV}\big(\rho_1\bmod L^*,\ {\rm Haar}_{\mathbb R^d/L^*}\big),
 \qquad \rho_1(dx)=e^{-\pi\|x\|^2}\,dx .
\]
The name refers to the heat kernel at the one fixed width. Define
\[
 A_{s,h,U}=sP^\perp+\frac{s h}{\sqrt{1+h^2}}P,\qquad
 L_{s,h,U}=A_{s,h,U}\Lambda^* .
\]
As \(s\to\infty\), uniformly in all \(h>0\) and \(U\),
\[
 \left|\operatorname{TV}(p_{s,h,U},q_{h,U})-H(L_{s,h,U})\right|
      =O_\Lambda(s^{-1/(9d)}).
 \tag{1}
\]
The exponent in this uniform error is not claimed optimal. If \(\ell_s=\lambda_1(L_{s,h,U})\), then along arbitrary paths,
\[
 \operatorname{TV}(p_{s,h,U},q_{h,U})\to0
     \quad\Longleftrightarrow\quad \ell_s\to\infty,\qquad
 \operatorname{TV}(p_{s,h,U},q_{h,U})\to1
     \quad\Longleftrightarrow\quad \ell_s\to0.                         \tag{2}
\]
In particular if \(s^d h^r\to0\), total variation tends to one. The condition \(s^d h^r\to\infty\) *alone* does not imply convergence to zero, even for a fixed irrational line in dimension two; see §4.

## 2. Exact density and uniform averaging

On the torus \(\mathbb R^d/L^*\), the density of \(\rho_1\bmod L^*\) relative to Haar is
\[
 F_L(z)=\sum_{v\in L}e^{-\pi\|v\|^2}e^{2\pi i\langle v,z\rangle}.
 \tag{3}
\]
It is positive (by periodization) and has Haar mean one. Set \(D_s=\sum_{k\in\Lambda^*}e^{-\pi s^2\|k\|^2}=1+O_\Lambda(e^{-\gamma_\Lambda s^2})\) with some positive \(\gamma_\Lambda\). Completion of squares in the conditional density of \(P X_s/s+Z_h\), followed by Poisson summation over \(\Lambda\), gives the exact identity
\[
 \frac{p_{s,h,U}(y)}{q_{h,U}(y)}
   = D_s^{-1} F_{L_{s,h,U}}\left(\frac{y}{h\sqrt{1+h^2}}\right).
 \tag{4}
\]
Indeed the square in the primal integral is centered at \(s y/(1+h^2)\); its squared width is \(A_{s,h,U}^2\), and its normalizing real Gaussian factor leaves the width-\(\sqrt{1+h^2}\) output. The Poisson phase at \(v=A_{s,h,U}k\) in (4) is \(2\pi i\,s\langle Pk,y\rangle/(1+h^2)\). Integration against \(q_{h,U}\) multiplies each term by \(e^{-\pi s^2\|Pk\|^2/(1+h^2)}\), so the exact expectation of \(F_L\) on the right is \(D_s\). Positivity therefore shows that replacing \(D_s^{-1}\) by \(1\) inside the absolute value in the variation integral changes the result by at most \((D_s-1)/2\).

If \(h\ge1\), all singular values of \(A_{s,h,U}\) are at least \(s/\sqrt2\). The nonzero terms of (3) then have total uniformly exponentially small, which gives (1) in this range. Hereafter take \(0<h\le1\). Write \(\delta=s^{-1/(6d)}\) and \(L=L_{s,h,U}\).

**Case \(\lambda_1(L)\ge\delta\).** Disjoint balls of radius \(\delta/2\) about lattice points give \(\#(L\cap B_R)\le(1+2R/\delta)^d\). In particular \(\sum_{v\in L}e^{-\pi\|v\|^2/2}=O_d(\delta^{-d})\). Cut (3) off at \(R=\sqrt{\log s}\) to obtain \(F_{L,R}\); the uniform absolute tail is \(O_d(s^{1/6-\pi/2})\). Let \(B=C_d s^{1/6}\) be a bound for the sum of the absolute Fourier coefficients of \(G=F_{L,R}-1\), with \(C_d\) sufficiently large. Thus \(G/B\) is real and in \([-1,1]\).

Use the degree-\(M\) Bernstein polynomial for \(|x|\) on \([-1,1]\) with \(M=\lfloor \sqrt{s}\rfloor\). For \(x\in[-1,1]\), let \(J\sim{\rm Bin}(M,(1+x)/2)\); this polynomial is \(\mathbb E|2J/M-1|\). It differs uniformly from \(|x|\) by at most \(M^{-1/2}\) by Cauchy–Schwarz. Its ordinary coefficient sum in absolute value is at most \(2^M\): in each Bernstein summand the coefficient sums of \((1+x)/2\) and \((1-x)/2\) equal 1, and the binomial multiplicities sum to \(2^M\). After substitution \(x=G/B\), the total absolute Fourier coefficient sum is still at most \(2^M\), because \(G/B\) has Fourier coefficient sum at most one and Fourier sums multiply submultiplicatively in that norm. All its frequencies \(v=A_{s,h,U}k\) have length at most \(MR=o(s)\).

For any nonzero such \(v\), \(\|P^\perp k\|\le MR/s=o(1)\), whereas \(\|k\|\ge\lambda_1(\Lambda^*)>0\). Thus \(\|Pk\|\ge\lambda_1(\Lambda^*)/2\) for all large \(s\), *uniformly in \(U,h\)*. Its Haar expectation vanishes, and its expectation against the Gaussian line or plane in (4) is at most \(e^{-\gamma s^2}\) for a fixed \(\gamma=\gamma(\Lambda)>0\). The zero frequency has equal expectation. Therefore the two expectations of the Bernstein approximant differ by at most \(2^M e^{-\gamma s^2}\). Undoing the scaling, approximation and truncation bounds the difference of the two \(|F_L-1|\) expectations by
\[
 O_d(s^{1/6-\pi/2})+\frac{2B}{\sqrt M}+B2^M e^{-\gamma s^2}
 =O_\Lambda(s^{-1/12}).
\]

**Case \(\lambda_1(L)<\delta\).** Choose \(v=A_{s,h,U}k\in L\) nonzero with \(\|v\|<\delta\). Put \(b=s Pk/(1+h^2)\). Since \(\|P^\perp k\|<\delta/s\), \(\|Pk\|\ge\lambda_1(\Lambda^*)/2\). Under \(q_{h,U}\), the real phase \(\langle b,y\rangle\bmod1\) is within \(O_\Lambda(e^{-\gamma s^2})\) of uniform on the circle by its Gaussian Fourier series. Under \(p_{s,h,U}\), it has real first Fourier coefficient at least \(e^{-\pi\|v\|^2}/D_s\): insert the phase factor in (4), take the expectation under \(q_{h,U}\), and retain the \(v\)-frequency cancelling it. Every other contribution is a nonnegative real term. If \(w=\delta^{2/3}\), the inequality \(1-\cos(2\pi u)\ge8\,\operatorname{dist}(u,\mathbb Z)^2\) gives at most \(O_\Lambda(\delta^{2/3})\) probability outside the circular interval of radius \(w\) at zero under \(p_{s,h,U}\). This interval has probability at most \(2w+O_\Lambda(e^{-\gamma s^2})\) under \(q_{h,U}\), so their variation distance is \(1-O_\Lambda(\delta^{2/3})\). The same argument for the character \(z\mapsto e^{2\pi i\langle v,z\rangle}\) in (3) compares \(\rho_1\bmod L^*\) to Haar: their first coefficients are \(e^{-\pi\|v\|^2}\) and 0 and the Haar character is uniform on the circle. It too gives \(H(L)=1-O_d(\delta^{2/3})\). The two estimates, with \(\delta^{2/3}=s^{-1/(9d)}\), finish (1).

## 3. Endpoint criteria and the generic critical-volume law

For any nonzero \(v\in L\), (3) and boundedness of the phase function give \(H(L)\ge e^{-\pi\|v\|^2}/2\). Packing shows \(H(L)\to0\) uniformly as \(\lambda_1(L)\to\infty\), by bounding the nonzero sum in (3). The preceding circular-interval argument gives \(H(L)\to1\) uniformly when \(\lambda_1(L)\to0\). In the reverse direction, if \(\lambda_1(L)\ge\eta>0\), the packing bound gives \(F_L\le B_{\eta,d}<\infty\) uniformly, so \(\int \min(1,F_L)\,d{\rm Haar}\ge1/B_{\eta,d}\); thus \(H(L)\le1-1/B_{\eta,d}\). This proves both equivalences in (2). Since
\[
 \det L_{s,h,U} = \det(\Lambda^*)\,s^d
                  \left(\frac{h}{\sqrt{1+h^2}}\right)^r ,
\]
Minkowski's convex body bound on the shortest vector proves the stated vanishing-volume criterion.

Here is a more complete answer at the critical width \(h=c s^{-d/r}\), for fixed \(c>0\). Set \(s=e^t\), \(\alpha=(c^r\det\Lambda^*)^{1/d}\) and let \(\mu_d\) be Haar probability on the space \(X_d\) of unimodular lattices. For almost every \(r\)-plane \(U\) (in the rotation-invariant measure on the Grassmannian), the empirical probability law over logarithmic time of \(\operatorname{TV}(p_{e^t,c e^{-dt/r},U},q_{c e^{-dt/r},U})\) converges to
\[
              (M\mapsto H(\alpha M))_\#\mu_d.                          \tag{5}
\]
In particular the subsequential limit set is the entire interval
\([m_\alpha,1]\), where \(m_\alpha=\min_{M\in X_d}H(\alpha M)\) satisfies \(0<m_\alpha<1\). This is a law of deterministic profile values along a single generic plane, not an average of output laws over random planes. A single full-measure set of planes works for all \(c>0\).

To see this, first note uniform stability under a small linear change \(B\) of \(L\):
\[
 |H(BL)-H(L)|\le \operatorname{TV}(B^{\mathsf T}_\#\rho_1,\rho_1).
 \tag{6}
\]
Indeed \(B^{\mathsf T}\) maps \(\mathbb R^d/(BL)^*\) onto \(\mathbb R^d/L^*\) and preserves Haar probability, and wrapping is a contraction for total variation. The right side tends to zero as \(B\to I\). This also proves continuity of \(H\) on full lattices.

Rotate the \(r\)-plane to the first \(r\) coordinates by an oriented orthogonal matrix \(O_U\). In these coordinates \(L_{s,h,U}\) differs by a linear \(I+o(1)\) from
\[
 C g_t O_U\Lambda^*,\qquad
 C=\operatorname{diag}(c I_r,I_{d-r}),\qquad
 g_t=\operatorname{diag}(e^{-(d-r)t/r}I_r,e^t I_{d-r}).
\]
Normalize covolume to one: writing \(\Lambda_0=(\det\Lambda^*)^{-1/d}\Lambda^*\), this lattice divided by \(\alpha\) is \(c^{-r/d} Cg_t O_U\Lambda_0\). The fixed left factor \(c^{-r/d}C\) has determinant one and preserves \(\mu_d\).

The forward trajectory \(g_t O_U\Lambda_0\) is Birkhoff generic for almost every \(U\). Here are the assumptions in the application of Kleinbock–Shi–Weiss. In the usual full-measure graph chart, write \(O_U=\begin{pmatrix}A&B\\C'&D\end{pmatrix}\) with \(D\) invertible. It factors as
\[
 \begin{pmatrix}I&BD^{-1}\\0&I\end{pmatrix}
 \begin{pmatrix}A-BD^{-1}C'&0\\0&D\end{pmatrix}
 \begin{pmatrix}I&0\\D^{-1}C'&I\end{pmatrix}.
\]
The first factor is contracted by \(g_t\), and the middle factor commutes with it and preserves \(\mu_d\). The last factor's coordinate \(D^{-1}C'\) is (up to sign) the graph coordinate of \(U\); the Grassmannian measure has smooth density there. After exchanging expanding and contracting blocks and rescaling time by \(d-r\), Theorem 1.1 of Kleinbock–Shi–Weiss applies with uniform positive weights in each block to the lower-unipotent orbit of the fixed base lattice \(\Lambda_0\). A countable dense family of compactly supported smooth functions gives simultaneous convergence for all continuous compactly supported tests. The first factor does not affect these averages because for such a test the change under left multiplication near identity is uniformly small on all of \(X_d\) (use a compact enlargement of its support). The middle factor need not be fixed across planes; for each generic orbit all compactly supported tests already converge, so left translation by that orbit's fixed factor is allowed. The resulting vague convergence of probability measures to \(\mu_d\), itself a probability, is weak convergence. Now use the continuous observable \(H(\alpha\,\cdot)\) together with (1) and (6) to prove (5).

Minkowski gives a fixed finite upper bound on \(\lambda_1(\alpha M)\), so the earlier Fourier lower bound implies \(m_\alpha>0\). Any fixed \(M\) has \(H(\alpha M)<1\) since the density is positive; in a cusp sequence \(\lambda_1(\alpha M)\to0\) the limit is 1. Mahler compactness thus gives attainment of the minimum. The space \(X_d\) is connected, and \(H\) is continuous, so the closure of its range is \([m_\alpha,1]\). Haar has full support; all neighborhoods of every value in this closed range have positive limiting time frequency. This proves the limit-set statement, and the limiting law is nonconstant.

## 4. Explicit two-dimensional consequences without a metric theorem

Take \(\Lambda=\mathbb Z^2\) and \(U=\operatorname{span}(1,\xi)\) for irrational \(\xi\). When \(\xi\) is badly approximable, the equivalent lattice inequality \(\|P^\perp k\|\ge a/\|k\|\) for \(0\ne k\in\mathbb Z^2\) holds with \(a>0\), directly from the definition \(\inf_{j\ge1}j\,\operatorname{dist}(j\xi,\mathbb Z)>0\) and norm comparability near \(U\). If \(\|P^\perp k\|\ge\|k\|/2\), the transformed norm is at least \(s/2\); otherwise \(\|Pk\|\ge\|k\|/2\). In the latter case the sum of the two squared components and AM–GM give \(\|A_{s,h,U}k\|^2\ge a s^2 h/\sqrt{1+h^2}\). Thus \(s^2h\to\infty\) suffices for convergence to zero at any badly approximable slope.

For a slope not badly approximable, take integer approximants \(k_j\) with \(p_j=\|Pk_j\|\to\infty,\ q_j=\|P^\perp k_j\|>0,\ a_j=p_j q_j\to0\). (Take \(k_j\) of the form \((j,\operatorname{round}(j\xi))\) along a suitable subsequence.) Set \(h_j=q_j/p_j\) and \(s_j^2=a_j^{-1/2}p_j/q_j\). Then
\[
 s_j^2 h_j=a_j^{-1/2}\to\infty,\qquad
 \|A_{s_j,h_j,U} k_j\|^2\le2\sqrt{a_j}\to0.
\]
By (2), the total variation tends to **one**, not zero, along this divergent-volume sequence.

For a concrete nonconstant critical profile take \(U\) to be the expanding eigenline of the symmetric determinant-one integer matrix
\[
 M=\begin{pmatrix}2&1\\1&1\end{pmatrix},\qquad\lambda=(3+\sqrt5)/2 .
\]
If \(O\) sends \(U\) to the first coordinate, \(O M O^{-1}=\operatorname{diag}(\lambda,\lambda^{-1})\). The unimodular lattice trajectory \(g_\tau O\mathbb Z^2\), \(g_\tau=\operatorname{diag}(e^{-\tau},e^\tau)\), is therefore periodic with period \(\log\lambda\). With \(h=c/s^2\), (1) and (6) give the profile
\[
 \operatorname{TV}(p_{s,c/s^2,U},q_{c/s^2,U})
      = H\!\left(\sqrt c\,g_{\log(s/\sqrt c)}O\mathbb Z^2\right)+o(1).
 \tag{7}
\]
At phase \(\tau=0\) the lattice is a rotated square and \(H\le C e^{-\pi c}\) for \(c\ge1\) by summing its Fourier series. At a suitably small fixed \(\tau>0\) the first rotated coordinate vector has squared length \(b<1\): at zero its squared length has derivative \(-2|\langle e_1,u\rangle|^2+2|\langle e_1,u^\perp\rangle|^2<0\) for a unit expanding eigenvector \(u\) of \(M\). The matching Fourier lower bound is \(\tfrac12 e^{-\pi c b}\), which is strictly larger than the phase-zero upper bound for all sufficiently large **fixed** \(c\). Hence even this fixed periodic direction need not have a pointwise critical limit; the critical volume alone does not specify the variation profile.

## Reproduction

Run \(\texttt{python3 verify-smoothed-projection-profile.py}\) (standard library). The script checks algebraic exponent identities, low-frequency polynomial averaging and representative Gaussian integrals using deliberately small synthetic dimensions, as well as the periodic-line comparison. It is a check on the proof's identities, not a theorem by numerical integration or a sampling tool.
