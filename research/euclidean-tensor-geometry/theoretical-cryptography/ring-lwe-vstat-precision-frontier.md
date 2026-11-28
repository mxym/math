# Variance-sensitive statistical queries for broad wrapped ring learning

An adaptive statistical-query lower bound for independent random ring coefficients with continuous product noise. The oracle may answer arbitrary bounded functions of a growing block, not just unary tests. For variance-sensitive precision \(\exp(vd)\), a clipped-likelihood argument gives an explicit rate frontier; the relevant centered spectral exponent is optimal over all dominated retained densities at exponentially small discarded mass. This is an adversarial-oracle result, not a time lower bound for ordinary access to samples or an inference algorithm.

## 1. Statement

Fix an odd integer \(q\ge3\), \(\beta>0\), \(t>0\). Let \(d\) be dyadic, \(b=\beta/d<1\), \(k=\lfloor t/b^2\rfloor\), and \(R=(\mathbb Z/q)[X]/(X^d+1)\), \(N=q^d\). Given one secret label \(s\in R\), a block consists of \(k\) independent rows
\[
 A_i\sim U_R,\qquad Y_i=A_i s/q+E_i,\qquad
 f_b(y)=\sum_{j\in\mathbb Z}b^{j^2}e^{2\pi i j y}
\]
with the usual coefficient grid embedding in the torus and independent scalar errors of density \(f_b\). Write \(P_s\) for the joint block law and \(\nu\) for a reference with the same independent uniform \(A_i\)'s and independent scalar responses with density \(g_b(y)=f_{b^{q^2}}(qy)\). These are positive probability densities on their torus spaces.

Consider the standard \(\mathrm{VSTAT}(n)\) oracle applied to this entire block as one statistical observation. A query is any measurable \(F\) from the block to \([0,1]\); an answer \(\widetilde p\) is admissible at the true block distribution \(P\) if
\[
 |\widetilde p-p|\le \max\{1/n,\sqrt{p(1-p)/n}\},\qquad p=\mathbb E_P F.
 \tag{1}
\]
All public coefficients are available to the **query function** as part of its input. There is no separate access to a realized block, no ability to specify its public coefficients, and no requirement that queries or their adaptive selection be efficient. Answers are adversarial within (1), not actual empirical means; different queries do not reveal raw samples.

Put
\[
 \alpha_q=\min_{p\text{ prime},\,p\mid q}2^{\,2-v_2(p^2-1)}\log p,\qquad
 \mathcal F_t(v)=
 \begin{cases}
 t+2\sqrt{tv}-v,&0\le v\le t,\\
 2t,&v\ge t
 \end{cases}
\quad\text{and}\quad
 \mathcal R_q(t,v)=\min\{\alpha_q-v,\log q-v-\mathcal F_t(v)\}.
 \tag{2}
\]
Here \(v_2\) is the \(2\)-adic valuation. Take \(n=n_d\ge1\) with \(\log n/d\to v\ge0\). Suppose \(\mathcal R_q(t,v)>0\). If an algorithm makes at most \(J_d\) adaptive queries with \(\limsup d^{-1}\log J_d<\mathcal R_q(t,v)\), then there is a valid oracle for each \(P_s\) such that, for a uniform \(s\), the joint law of \(s\) and the complete randomized view is at distance \(e^{-\Omega(d)}\) in TV from the view obtained using exact answers from \(\nu\) and an independent uniform label. In particular:

* Against these admissible oracles, success in returning a list of size at most \(L\) is at most \(L/q^d+e^{-\Omega(d)}\), and the advantage in predicting any fixed balanced binary label feature is at most \(e^{-\Omega(d)}\).
* Distinguishing the reference \(\nu\) from an unknown fixed \(P_s\) has exponentially small average advantage for this choice of admissible oracles, and hence cannot succeed uniformly over all labels and admissible oracles.
* At subexponential precision \(v=0\) the exponent is \(\min\{\alpha_q,\log q-t\}\). At exponential precision the full-ideal term is \(\log q-t-2\sqrt{tv}\) while \(0\le v\le t\), then becomes \(\log q-2t-v\). This is a certified lower-bound region, not a matching characterization of the oracle model. In particular we make no boundary assertion when the strict rate margin vanishes.

The dependence on \(v\) is not obtained by simply treating a VSTAT answer as a fixed number of transmitted bits. At very small query expectations the tolerance is on the scale \(1/n\); the proof aligns truncation loss with that floor and uses a query-variance factor for the remaining discrepancy.

## 2. A centered comparison for all label modes

Write \(M=kd\), \(G=\prod_{j=1}^M g_b\), \(L(y)=\prod_j f_b(y_j)/g_b(y_j)\) for the unshifted residual likelihood, and \(\langle\cdot,\cdot\rangle_\nu\) for the \(L^2\) pairing under the reference. Let \(0\le U\le L\) be any dominated retained density and put \(\eta=\int(L-U)G\,dy\). A subscript \(s\) means shifting the residual by \(A s/q\), so \(P_s\) has likelihood \(L_s\) under \(\nu\). The zero-frequency sector \(m\) of \(U\) is its average over the entire finite coefficient grid; it is also its conditional expectation under \(G\) given all within-cell positions \(q y_j\bmod 1\). In particular \(0\le m\le1\), by averaging \(U\le L\), and \(m\) is unchanged by every shift \(A s/q\). Its mass is \(1-\eta\).

For \(h:R\to\mathbb C\) with uniform label norm, consider the operator
\[
 \mathcal C_U h(A,y)=\mathbb E_s h(s)\{U_s(y)-m(y)\}.
\]
Unlike centering only the label distribution, this subtraction removes the same response sector even when \(h\) is constant. Let \(U_w\) be the sector of \(U\) with residue-frequency vector \(w\in R^k\), \(\Gamma_w=\|U_w\|^2_{L^2(G)}\), and \(J(w)=\sum_i w_iR\). The exact identity is
\[
 \|\mathcal C_U h\|_{L^2(\nu)}^2
   =\sum_{z\in R}|\widehat h(z)|^2
      \sum_{w\ne0}\Gamma_w\,
         \frac{\mathbf1_{\{z\in J(w)\}}}{|J(w)|}.
 \tag{3}
\]
Indeed the sectors are orthogonal for every \(A\), since \(G\) is invariant under grid translations. The sector \(w\) after averaging \(h(s)U_s\) is multiplied by \(\widehat h(\sum_i\overline{A_i}w_i)\), where \(\overline a=a(X^{-1})\) is the adjoint in the coefficient pairing. The sum in this argument is uniform on \(J(w)\) over \(A\), by equal fibers and independent additions. The \(w=0\) sector is exactly \((\mathbb E h)m\), canceled even for constant \(h\).

For all sufficiently large \(d\), every nonzero ideal of \(R\) has size at least \(e^{\alpha_q d}\), and there are only a bounded number of maximal ideals. To verify this, reduce modulo each prime \(p\) dividing \(q\). Since \(p\) is odd, \(X^d+1\) has distinct roots of exact order \(2d\), so every irreducible factor has degree \(\operatorname{ord}_{2d}(p)\). The valuation identity \(v_2(p^{2^j}-1)=v_2(p^2-1)+j-1\) for \(j\ge1\) gives the ratio in (2) eventually. In a CRT prime-power component any nonzero ideal contains a nonzero submodule in its highest \(p\)-layer: multiply an element with coefficient valuation \(r\) by \(p^{e-1-r}\). The layer is isomorphic as a module to the ring modulo \(p\), so the ideal has size at least the minimum residue field size. This proves the asserted lower bound, and the maximal ideals themselves correspond to those finitely many factors modulo the primes.

The following proper-ideal bound is uniform in \(U\) as long as \(0\le U\le L\). For a maximal ideal \(J_0\subsetneq R\), the projection onto sectors with every row frequency in \(J_0\) is averaging over its annihilator in the finite grid-group action. It is positive and hence its squared norm on \(U\) is no larger than that on \(L\). For one row of \(L\), sector weights factor with scalar \(\tau_0=1\), \(\tau_{\pm1}=O(b^2)\), and \(\tau_a=O_q(b^8)\) for all other residues; see direct Parseval with \(g_b=1+O_q(b^{q^2})\). A singleton of residue \(+1\) or \(-1\) is a unit monomial, and cannot belong to \(J_0\). The remaining singletons contribute \(O(db^8)\) and the terms of weight at least two contribute \(O((db^2)^2)\); thus the one-row projected norm squared is \(1+O(d^{-2})\). Raising to the \(k=O(d^2)\) power gives \(e^{O(1)}\) for the whole block. Summing over the bounded number of maximal ideals covers all \(w\ne0\) with \(J(w)\) proper; this can overcount, which is harmless for an upper bound. Full-ideal terms have exactly \(1/N\) in (3). Therefore there is a fixed constant \(C\) such that
\[
 \|\mathcal C_U\|_{\mathrm{op}}^2
 \le \Lambda(U):=N^{-1}\|U\|^2_{L^2(G)}+C e^{-\alpha_q d}.
 \tag{4}
\]

## 3. From the comparison to legal VSTAT answers

Fix a query \(F\), set \(p_0=\mathbb E_\nu F\), and \(\tau_0=\max(1/n,\sqrt{p_0(1-p_0)/n})\). Whenever \(|p_s-p_0|\le\tau_0/4\), the reference answer \(p_0\) is admissible for \(p_s=\mathbb E_{P_s}F\). When \(\tau_0=1/n\) this is immediate from the additive floor. Otherwise \(p_0(1-p_0)\ge1/n\) implies \(\tau_0\le p_0(1-p_0)\). The inequality \(|p_s(1-p_s)-p_0(1-p_0)|\le|p_s-p_0|\) gives \(p_s(1-p_s)\ge3p_0(1-p_0)/4\), hence legality from its variance term. This step compares to the **true-mean** tolerance (1), not a tolerance whose center has already been changed.

By positivity,
\[
 p_s-p_0=\langle F,U_s-m\rangle_\nu+
             \langle F,L_s-U_s\rangle_\nu-\langle F,1-m\rangle_\nu .
\]
Both last pairings belong to \([0,\eta]\). If \(\eta\le1/(8n)\), then a nonadmissible reference answer requires
\(|\langle F,U_s-m\rangle_\nu|>\tau_0/8\). Also \(U_s-m\) has integral zero. The dual form of (4), applied to \(F-p_0\), gives
\[
 \mathbb E_s|\langle F,U_s-m\rangle_\nu|^2
 \le\Lambda(U)\operatorname{Var}_\nu(F)
 \le\Lambda(U)p_0(1-p_0).
\]
Consequently
\[
 \Pr_s[p_0\text{ inadmissible for this }F]\le64n\,\Lambda(U).
 \tag{5}
\]
There is no loss of an extra factor of \(n\) for small \(p_0\). The true-mean variance and the additive floor are both needed for this conclusion.

Define a deterministic valid oracle for \(P_s\) by returning \(p_0\) when admissible and \(p_s\) otherwise. The reference oracle returns \(p_0\) exactly and is valid for \(\nu\). Freeze the algorithm's random tape and consider its sequence of queries along the *reference* transcript, where these queries are independent of the uniform label. Until a first nonadmissible reference answer, the \(P_s\) path is the same. The union bound using (5) on this reference path gives distance at most \(64 J_d n\Lambda(U)\) for the joint views, with the same tape coupling. This is an explicit version of the standard adversarial-SQ transcript argument; it does not treat adaptive queries as independent.

## 4. Exact precision exponent of dominated trimming

For a vector of independent scalar residual observations under density \(G\), write \(X_d=\log L(Y)\). Uniformly for any fixed bounded real \(a\),
\[
 \log\mathbb E_G[e^{a X_d}]
       =t\,a(a-1)d+O_{q,t,\beta,a}(d^{-1}).
 \tag{6}
\]
The analogous formula under the true residual density \(LG\) is \(t a(a+1)d+O(d^{-1})\). For (6), the scalar integral is \(\int f_b(y)^a g_b(y)^{1-a}\,dy=1+a(a-1)b^2+O(b^4)\): Taylor expansion of \(1+2b\cos(2\pi y)+O(b^4)\) gives zero odd integrated terms through order three, and \(g_b-1=O(b^9)\). The integral and its first two derivatives in \(a\) have uniform expansions over each real compact interval, by smooth Taylor expansion in \(b\) with the scalar densities bounded away from zero near \(b=0\). Multiplying the log by \(M=kd\) gives \(M b^2=td+O(d^{-1})\), \(M b^4=O(d^{-1})\). These estimates also justify the tilted mean and variance used below.

Under \(LG\), the Chernoff exponent for \(X_d>x d\), \(x>t\), is at least \(I_t(x)=(x-t)^2/(4t)\), by \(a=(x-t)/(2t)>0\) in its moment formula. With \(x=t+2\sqrt{t(v+\varepsilon)}\), choose the hard trim \(U=L\mathbf1_{\{X_d\le x d\}}\). Then \(\eta\le\exp(-(v+\varepsilon)d+O(d^{-1}))\), which is at most \(1/(8n)\) eventually. For \(a\le2\),
\[
 \|U\|_2^2=\mathbb E_G[e^{2X_d}\mathbf1_{\{X_d\le x d\}}]
         \le e^{(2-a)x d}\mathbb E_G e^{a X_d}.
\]
Minimizing the exponent for \(a\le2\) gives \(a=(x+t)/(2t)\) for \(x\le3t\) and \(a=2\) otherwise. The corresponding value is \(x-I_t(x)\) for \(x\le3t\), and \(2t\) otherwise, which is \(\mathcal F_t(v+\varepsilon)\). Therefore
\[
 \limsup \frac1d\log(n\Lambda(U))
 \le\max\{v-\alpha_q,\ v+\mathcal F_t(v+\varepsilon)-\log q\}.
\]
A fixed sufficiently small \(\varepsilon>0\) preserves any strict rate margin in (2), by continuity. This proves Section 1, including its two regimes in \(v\).

There is an exact sense in which this precision cost is intrinsic to the **dominated residual** method. Let \(\eta_d>0\) tend to zero and \(-d^{-1}\log\eta_d\to v<\infty\). Among all nonnegative \(U_d\le L\) with \(\int(L-U_d)\,G\le\eta_d\),
\[
 \lim_{d\to\infty}\frac1d
    \log\inf_{U_d}\|U_d\|^2_{L^2(G)}=\mathcal F_t(v).
 \tag{7}
\]
For an exact finite-dimensional minimizer, choose \(c\) with \(\int\min(L,c)\,G=1-\eta_d\), which exists by continuity in \(c\). For \(U_*=\min(L,c)\) and any admissible \(U\), pointwise \(U^2-U_*^2\ge2c(U-U_*)\): if \(L<c\), both \(U-U_*\) and \(U+U_*-2c\) are nonpositive; otherwise \(U_*=c\). Integrating gives optimality of \(U_*\). The hard trim already proves the upper exponent in (7) by taking \(\varepsilon\downarrow0\), with \(v+\varepsilon\) calibrated to \(\eta_d\).

For the lower exponent when \(v>0\), choose \(x>t\) with \(I_t(x)<v\). For a small fixed \(r>0\), the band \(B_x=\{|X_d/d-x|\le r\}\) has true residual mass at least \(\exp[-d(I_t(x)+O_x(r)+o(1))]\). To see this, tilt \(LG\) by \(e^{aX_d}\) with \(a=(x-t)/(2t)\). Its mean of \(X_d/d\) tends to \(x\) and its variance tends to zero by the differentiated formula (6). Undoing the tilt on this band gives the claimed lower bound with rate loss at most \(a r\). Choose \(r\) small enough that this mass is exponentially larger than \(\eta_d\). Hence \(\int_{B_x} U_d\,G\) is at least \((1-o(1))\Pr_{LG}(B_x)\). Also \(G(B_x)\le e^{-d(x-r)}\Pr_{LG}(B_x)\). Cauchy–Schwarz on the band yields
\[
 \liminf_d d^{-1}\log\|U_d\|_2^2
       \ge x-I_t(x)-O_x(r).
\]
Let \(r\downarrow0\), and maximize over \(x>t\) with \(I_t(x)<v\). The unconstrained optimum is \(x=3t\); the constraint puts its boundary at \(x=t+2\sqrt{tv}\). This gives \(\mathcal F_t(v)\), including the case \(v=t\) by approaching the boundary. For \(v=0\) use the ordinary high-probability band \(X_d/d\in[t-r,t+r]\) and \(\eta_d=o(1)\), to get \(t-r\), then \(t\). This proves (7). The same infimum is obtained if the pointwise constraints are replaced by \(\int|L-U|G\le\eta_d\) and \(U\) real: clipping \(U\) to the pointwise interval \([0,L]\) does not increase either norm. This only concerns minimization of the residual \(L^2\) norm, not of a signed comparison operator.

## 5. Sharpness for the centered spectral comparison

For any fixed \(v>0\), under the same dominated trimming constraint as (7),
\[
 \lim_{d\to\infty} d^{-1}\log
   \inf_{U_d}\|\mathcal C_{U_d}\|_{\mathrm{op}}^2
 =\max\{\mathcal F_t(v)-\log q,-\alpha_q\}.
 \tag{8}
\]
This statement is about the positive comparison method, not a matching VSTAT algorithm or a lower bound outside that oracle model.

For the lower bound, the largest Fourier eigenvalue in (3) is exactly the constant-label eigenvalue \(z=0\), because every ideal contains zero and all weights are nonnegative. Its full sum is at least \(N^{-1}(\|U\|_2^2-\|m\|_2^2)\ge N^{-1}(\|U\|_2^2-1)\). Since \(\mathcal F_t(v)>0\), (7) yields the full-size exponent in (8).

To see the other exponent, we only need one low-coefficient-weight representative generating a minimal nonzero ideal; its support will have bounded size, independent of \(d\). Fix a prime \(p\mid q\) attaining \(\alpha_q\) and let \(p^e\Vert q\). Fix a dyadic \(d_0\) large enough that all Frobenius degrees have already stabilized to their ultimate proportions. Factor \(X^{d_0}+1=\prod_i F_i(X)\) over \(\mathbb F_p\). For each \(d\ge d_0\) dyadic, all \(F_i(X^{d/d_0})\) are irreducible: they divide \(X^d+1\), and have exactly the degree of a single irreducible factor in that ring by the stabilized degree ratio. Choose a fixed index \(i_0\). The element \(\prod_{i\ne i_0}F_i(X^{d/d_0})\) generates the ideal consisting of only the \(i_0\)-coordinate in the product of residue fields, a field of size \(e^{\alpha_q d}\). Lift those finitely many coefficient values and put the element in the top layer of the prime-power component by multiplication by \(p^{e-1}\), with all other prime-power components zero by the ordinary coefficient CRT. This gives \(r_d\in R\) with \(|r_d R|=e^{\alpha_q d}\) and boundedly many nonzero coefficients. The layer isomorphism in Section 2 identifies the ideal and preserves its cardinality.

Use the single-row sector \(w=(r_d,0,\ldots,0)\) and choose a bounded integer representative \(u\) for its nonzero scalar coefficients. For the corresponding pure torus character \(\chi_u\), \(\|\chi_u\|_{L^2(G)}=1\). Its Fourier coefficient in the original likelihood is of magnitude \(b^{\|u\|_2^2}\), since \(L G\) is the unshifted product density \(f_b\). The exponent \(C_q'=\|u\|_2^2>0\) is fixed as only the support positions move. Removing nonnegative mass at most \(\eta_d\) changes that coefficient by at most \(\eta_d\). For \(v>0\) this is \(o(b^{C_q'})\). Thus \(\Gamma_w\ge b^{2C_q'}(1-o(1))\) by Cauchy–Schwarz within its sector, and its term at \(z=0\) is at least \(e^{-\alpha_q d}b^{2C_q'}(1-o(1))\). This proves the proper-size lower exponent. The upper bound in (8) follows from (4) and the trim used for (7).

The same reasoning gives (8) at \(v=0\) when the allowed discarded mass is \(o(b^{C_q'})\); irrespective of this extra hypothesis it gives the equality at \(v=0\) if the full-size exponent dominates the proper-size one. We do not claim equality at general \(v=0\) without either condition. Also (8) concerns the largest spectral mode, which is the constant-label mode; it does not prove that bounded real queries achieve that spectral norm or that the full oracle frontier is sharp.

## 6. Prior work and scope

* The exact oracle (1) is [Feldman, COLT 2017, Def. 2.2](https://proceedings.mlr.press/v65/feldman17c/feldman17c.pdf), following [Feldman, Grigorescu, Reyzin, Vempala and Xiao](https://www.levreyzin.com/assets/pdf/FeldmanGRVX13.pdf). Feldman's Sec. 6.2 explicitly relates the spectral discrimination norm to the VSTAT lower-bound method. The oracle and transcript argument are not new. [Blum, Kalai and Wasserman](https://arxiv.org/abs/cs/0010022) study the distinction between sample access and SQ learning for parity and discuss \(t\)-wise queries; their \(O(\log n)\) weak-learnability simulation is not the growing \(\Theta(d^2)\)-row block analyzed here.
* Our [previous batch communication note](https://github.com/mxym/math/blob/9c7c903b1aa999d663b8bc4f5b48ad499beb738e/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-batch-communication-entropy-scale.md) already computes the ideal-sector spectrum and uses positive truncation at the Shannon scale for bit messages. The new statements here are a variance-sensitive oracle bound with exponential precision, including the exact nuisance-sector comparison against the reference even in the constant label mode, the sharp exponent of dominated trimming, and optimality of that global centered spectral comparison for positive exponential trimming rates. This does not claim the basic ideal Fourier diagonalization anew.
* The block laws use fixed odd \(q\), continuous independent wrapped noise \(b=\beta/d\), uniform random designs and a uniform label in the lower bound. No actual parameter set, generic running-time statement, algorithm for label recovery, or attack is inferred. The checker tests only synthetic algebra, clipping and tolerance identities.
