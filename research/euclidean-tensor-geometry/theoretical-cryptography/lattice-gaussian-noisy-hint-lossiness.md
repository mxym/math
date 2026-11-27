# Sharp smooth conditional min-entropy of a lattice Gaussian with a noisy linear hint

For a wide lattice Gaussian observed through independent Gaussian noise, the smooth conditional min-entropy is determined by a posterior lattice covolume and an explicit dimension-dependent constant. The leading constant is optimal even if the smoothing step is allowed to alter the marginal law of the hint, rather than keeping that marginal fixed. With exact unwrapped **discrete** noise, the posterior support lattice must also be accounted for; the same ambient width matrix alone can give the wrong entropy.

This is a statistical assurance result in a standalone Gaussian model. No instance of a cryptographic learning problem, parameter assessment, or recovery algorithm is considered.

## 1. Model and result

Let \(X\) be a discrete Gaussian on the affine full-rank lattice \(c+L\subset\mathbb R^d\), with mean parameter \(m\) and positive definite width matrix \(A\). Thus its weights are proportional to \(\exp[-\pi(x-m)^T A^{-1}(x-m)]\); a continuous counterpart would have covariance \(A/(2\pi)\). Observe \(Y=TX+N\), with fixed real matrix \(T\), and independent, centered continuous Gaussian noise of width \(B\succ0\), or discrete Gaussian noise of the same width on any full-rank affine lattice \(b+M\) of the output space with center parameter zero. Width matrices are not covariances.

For the continuous-noise case set \(L_0=L\). For the discrete-noise case set
\[
 L_0=\{v\in L:Tv\in M\}.
\]
Let \(r=\operatorname{rank}L_0\), \(V=\operatorname{span}_{\mathbb R}L_0\), and take a matrix \(J\) with orthonormal columns spanning \(V\). For \(r\ge1\) define
\[
 C=(A^{-1}+T^T B^{-1}T)^{-1},\quad
 C_V=(J^TC^{-1}J)^{-1},\quad
 \Gamma=C_V^{-1/2}J^TL_0,\quad
 \beta=\det\Gamma=\frac{\det_r L_0}{\sqrt{\det C_V}},
\]
and write \(h\) for the Euclidean covering radius of \(\Gamma\). The theorem requires small \(h\) for accurate asymptotics, not necessarily isotropic widths or an injective hint map \(T\).

For a joint probability law \(P\) on the specified countable \(X\) alphabet and the hint space put
\[
 G(P)=\mathbb E_{Y}\max_x P(X=x\mid Y),\qquad
 G^\epsilon(P)=\inf_{Q:\,d_{\rm TV}(P,Q)\le\epsilon}G(Q).
\]
The competitors \(Q\) are **normalized** laws on the same alphabets with no fixed-marginal requirement. The smooth average conditional min-entropy is \(\widetilde H_\infty^\epsilon(X\mid Y)=-\log_2G^\epsilon(P)\). Define the scalar profile
\[
 \mathcal F_r(a)=\int_{\mathbb R^r}(e^{-\pi\|z\|^2}-a)_+\,dz,\qquad
 \mathcal F_r(a_u)=u\quad(0<u<1),\quad a_0=1.
\]
The function is convex; on \(0<a<1\) it decreases strictly from one to zero. For \(0<a\le1\), set \(R=\sqrt{\log(1/a)/\pi}\), with a natural logarithm. Then \(\mathcal F_r(a)=\Pr(\chi_r^2\le2\log(1/a))-a v_rR^r\), where \(v_r\) is unit-ball volume.

**Theorem.** For \(r\ge1\) there is an explicit finite constant \(K_r\), depending only on \(r\) and given below, such that if \(h\le1\), \(\delta=2K_rh^2<\min(\epsilon,1-\epsilon)\), then
\[
 \beta a_{\epsilon+\delta}\ \le\ G^\epsilon(P)\ \le\ \beta a_{\epsilon-\delta}.
 \tag{1}
\]
Consequently, for fixed \(0<\epsilon<1\) and \(r\), the entropy for \(h\to0\) is
\[
 \widetilde H_\infty^\epsilon(X\mid Y)
 =\tfrac12\log_2\det C_V-\log_2\det_r L_0-\log_2 a_\epsilon+O_{r,\epsilon}(h^2).
 \tag{2}
\]
At \(\epsilon=0\), the same statement holds with \(a_0=1\) and \(O_r(h^2)\). If \(r=0\) in the discrete model, the full unwrapped hint uniquely fixes the \(X\) label on the support; under the stated normalized smoothing convention \(G^\epsilon(P)=1-\epsilon\). This last assertion reflects a change of support rank, not a narrow limit of a full-rank covariance formula.

Common width scaling \(A=\lambda A_0,B=\lambda B_0\) at any fixed lattice, maps, dimensions and shifts gives \(h^2=O(\lambda^{-1})\). If \(L_0\) has finite index in \(L\) and all other ingredients are fixed, the exact discrete-noise model instead of continuous noise subtracts \(\log_2[L:L_0]\) from the leading result. This loss is absent in the compatible case \(T L\subseteq M\). For reference, if \(r=d\), subtracting (2) from the corresponding no-hint entropy gives the leading smooth entropy drop
\[
 \tfrac12\log_2\det(I+A^{1/2}T^TB^{-1}TA^{1/2})+\log_2[L:L_0].
\]
The profile constant cancels in this difference when the same fixed smoothing budget is used. The continuous-noise formula sets the index term to zero. If instead \(r<d\) at fixed shape, the no-hint and conditional leading logarithms differ by \((d-r)\log_2\lambda/2+O(1)\). Several independent hints of the same noise type can be stacked with block-diagonal noise width; with both types present the compatibility lattice only uses the discrete observations. All assertions compare specified laws, not the difficulty of any computational problem.

## 2. Posterior support and a uniform clipping estimate

When the noise is continuous, all \(x\in c+L\) remain possible at each hint \(y\). When it is discrete, a compatible \(x_y\) obeys \(y-Tx_y\in b+M\). The compatible set is precisely \(x_y+L_0\) by subtraction. Given \(y\), multiply the prior weight and the noise weight. Their log-quadratic in \(x\) has precision \(C^{-1}\) and center \(C(A^{-1}m+T^TB^{-1}y)\) before restriction. Restriction to the affine posterior span changes the precision to \(J^TC^{-1}J\) and translates the center. Hence after normalization every posterior is a Gaussian weight on some translate \(\Gamma+v_y\), with labels in bijection with that translate. No assumption on the distribution of \(v_y\) is used.

Write \(f(z)=e^{-\pi\|z\|^2}\). We prove the estimate, for every \(v\) and \(a\ge0\),
\[
 \left|\beta\sum_{z\in\Gamma+v}(f(z)-a)_+ - \mathcal F_r(a)\right|\le K_r h^2.
 \tag{3}
\]
Use the translated Voronoi cells of \(\Gamma\), each centered at its grid point, of volume \(\beta\), centrally symmetric and contained in its radius-\(h\) ball. For \(0<a<1\) the clipping boundary is the sphere of radius \(R\). Cell centers at norm less than \(R-h\) have all their cells inside the ball; there clipping subtracts precisely the constant \(a\), and the first-order Taylor term of \(f\) integrates to zero by symmetry. Outside radius \(R+h\) both the sampled value and cell integral vanish. For interior cells, summing the second-order Taylor estimate gives error at most
\[
 \frac{h^2}{2}\int_{\mathbb R^r}
 (2\pi+4\pi^2(\|z\|+1)^2)e^{-\pi(\|z\|-1)_+^2}\,dz .
\]
Indeed the integrand bounds the operator norm of the Hessian at any point within distance \(h\le1\) of the cell's integration point \(z\). When \(a=0\) the same estimate applies to all cells; when \(a\ge1\) equation (3) is exact with zero on both sides.

For boundary cells \(|\|x\|-R|\le h\) with center \(x\), integration points have norm in \([(R-2h)_+,R+2h]\). The absolute change of the clipped value from center to integration point is bounded by the absolute change of \(f\), hence by \(2\pi h(R+2h)e^{-\pi(R-2h)_+^2}\). The union of their cells has volume at most \(4r v_r h(R+2h)^{r-1}\) by the annulus volume formula. Thus one can take
\[
 K_r=\frac12\int_{\mathbb R^r}(2\pi+4\pi^2(\|z\|+1)^2)e^{-\pi(\|z\|-1)_+^2}\,dz
   +8\pi r v_r\sup_{R\ge0}(R+2)^r e^{-\pi(R-2)_+^2}.
\]
Both terms are finite. This proof uses only the covering radius of the whitened lattice, not a basis quality or any moment assumption on the hint.

Set \(N_v=\beta\sum_{z\in\Gamma+v} f(z)\); by (3) at \(a=0\), \(|N_v-1|\le K_rh^2\). The posterior weight at \(z\) is \(p_v(z)=\beta f(z)/N_v\). Replacing \(f\) by \(f/N_v\) inside the clipping sum changes it by at most \(\beta\sum |f/N_v-f|=|1-N_v|\). Therefore
\[
 \left|\sum_z(p_v(z)-\beta a)_+-\mathcal F_r(a)\right|\le\delta
 \quad\hbox{uniformly in }v,\ a\ge0.
 \tag{4}
\]
Zero-probability labels outside the posterior lattice make no contribution. The finite-width result uses (4), not just an approximation of the posterior's largest atom.

## 3. Optimality when the hint marginal is free

Let a competitor \(Q\) satisfy \(d_{\rm TV}(P,Q)\le\epsilon\), and let \(q_y(x)\) be the densities of the absolutely continuous parts of its label-specific hint measures with respect to \(P_Y\). Put \(t(y)=\sup_x q_y(x)\). Then \(G(Q)\ge \mathbb E_{P_Y}t(Y)\); singular parts only add nonnegative contributions to \(G(Q)\). The positive part of \(P-Q\), using \(q_y(x)\le t(y)\), implies
\[
 \epsilon\ \ge\ \mathbb E_{P_Y}\sum_x(p_y(x)-t(y))_+
 \ \ge\ \mathbb E_{P_Y} \mathcal F_r(t(y)/\beta)-\delta
 \ \ge\ \mathcal F_r\bigl(\mathbb E_{P_Y}t(Y)/\beta\bigr)-\delta .
 \tag{5}
\]
The last inequality is Jensen's inequality for the convex profile, valid also for cap ratios larger than one. This proves the lower bound in (1), including competitors that concentrate all their changes at certain hints or change the hint law.

For the upper bound choose the same conditional cap \(t_0=\beta a_{\epsilon-\delta}>0\) for every hint. Clip each posterior at this cap. Its removed mass is bounded by \(\mathcal F_r(a_{\epsilon-\delta})+\delta=\epsilon\). A normalized posterior with no atom above the cap can be obtained by restoring this mass under the cap on a fixed finite list of \(N\) labels with \(Nt_0\ge1\). The list has enough spare capacity because the clipped mass on it is at most the total mass left after clipping; greedily allocating the removed mass in list order is a measurable existence construction. The smoothing law may change support within the specified alphabet. Keeping \(P_Y\) and making these changes gives TV at most \(\epsilon\) and \(G(Q)\le t_0\). This is a proof of existence of a nearby law, not a reconstruction of an \(X\) value from a hint.

For fixed \(0<\epsilon<1\), the inverse cap has bounded derivative on a neighborhood of \(\epsilon\): \(\mathcal F'_r(a)=-v_rR^r<0\) at \(a=a_\epsilon\). This turns (1) into (2). For \(\epsilon=0\), each translate has a point of norm at most \(h\); Gaussian weights then put its maximal atom between \(\beta e^{-\pi h^2}/(1+K_rh^2)\) and \(\beta/(1-K_rh^2)\) for small \(h\). For \(r=0\), the true joint law is on the graph of its unique label. Any competitor within TV \(\epsilon\) must retain at least \(1-\epsilon\) mass on the graph, giving \(G(Q)\ge1-\epsilon\); keeping that much conditional graph mass and distributing the rest among enough other labels achieves equality.

The limiting smoothing gain is explicit. For example, \(\mathcal F_2(a)=1-a+a\log a\). More generally
\[
 \mathcal F_r(1-s)\sim \frac{2v_r}{(r+2)\pi^{r/2}}s^{\,1+r/2}\qquad(s\downarrow0).
\]
To see this, change variables \(z=\sqrt{s/\pi}\,w\) within the clipping ball; its radius in the \(w\) coordinates tends to one, and the clipped difference divided by \(s\) converges there to \(1-\|w\|^2\). This expansion concerns the profile, not an assertion of a uniform relative error at vanishing \(\epsilon\).

## 4. Finite alphabets and coarsened observations

For an injective finite labeling of a selected set \(F\subset c+L\), write \(\tau=P(X\notin F)<1\) and let \(P_F=P(\,\cdot\,\mid X\in F)\). If \(r\ge1\), \(\epsilon>\delta+\tau\) and \(|F|\beta a_{\epsilon-\delta-\tau}\ge1\), then
\[
 G^\epsilon(P_F)\le\beta a_{\epsilon-\delta-\tau}.
 \tag{6}
\]
Indeed, remove labels outside \(F\) and clip the rest at \(t_0=\beta a_{\epsilon-\delta-\tau}\), with all masses relative to \(P_Y\). The total removed mass is at most \(\tau+\mathcal F_r(t_0/\beta)+\delta=\epsilon\). Restore on \(F\) as above, keeping \(P_Y\). Both the restored law and \(P_F\) contain the clipped joint subprobability as a pointwise lower bound on their measures, since \(P_F\) dominates the restriction of \(P\) to \(F\). Thus their TV is at most the removed mass; the tail is charged once, not twice. The converse bound \(G^\epsilon(P_F)\ge\beta a_{\epsilon+\tau+\delta}\) follows from (5) and \(d_{\rm TV}(P_F,P)=\tau\) if \(\epsilon+\tau+\delta<1\). These equations use normalized smoothing on the finite label alphabet.

If \(F\) is a finite choice of distinct representatives for a quotient, the finite label \(X\bmod L'\) under \(P_F\) has precisely the same entropy given the unwrapped hint. Under any deterministic coarsening of the hint (including modular reduction), (6) still bounds its smooth guessing mass from above: push both laws through the coarsening, and use contraction of TV and the fact that merging hint outcomes cannot increase \(G\). This is not an equality claim for wrapped hints, or for an **untruncated** source reduced modulo an arbitrary lattice.

## 5. Connection to primary work and limitations

- Brakerski and Döttling, [Hardness of LWE on General Entropic Distributions](https://eprint.iacr.org/2020/119.pdf), §5, give general lossiness bounds based on source min-entropy and the noise channel. Their [Lossiness and Entropic Hardness for Ring-LWE](https://iacr.org/archive/tcc2020/12550224/12550224.pdf), §§2.1, 2.4, uses average conditional min-entropy and normalized TV smoothing. This note computes the sharp fixed-\(\epsilon\) value for a particular Gaussian source and posterior model, not a replacement for their reduction or a general estimate for all sources.
- Boudgoust and Lapiha, [Leftover Hash Lemma(s) Over Cyclotomic Rings](https://opencryptology.org/2025/1080/versions/20260428T172000Z.pdf), §4.4, Lemma 29, use the Gaussian posterior under compatible discrete Gaussian hints, citing Espitau, Niot and Prest, [Flood and Submerse](https://eprint.iacr.org/2024/959.pdf), Lemma 1 and Appendix D. The completed-square part here is the same principle. The clipping comparison, optimal normalized smoothing constant, and explicit support-lattice dependence are the focus here; the note does not bound entropy simultaneously in all ideals or prove a new leftover hash lemma.
- Dai et al., [Lattice-based, LWE-leakage model for Gaussian and uniform secret and its application in decentralization](https://doi.org/10.1186/s42400-025-00439-5), Theorem 1, give an unsmoothed lower bound for a particular finite modular lattice model via a Gaussian lattice mass. Jin, Liu, Wang and Gu, [Discrete Gaussians Modulo Sub-Lattices](https://eprint.iacr.org/2024/1695.pdf), §§3–4, distinguish exact and smooth min-entropy and address the unconditional modular Gaussian law. Neither comparison gives (2) for the normalized smooth conditional quantity of this unwrapped lattice model.

The results use fixed \(r\) for asymptotics, a small whitened covering radius, and either exactly continuous or exactly discrete Gaussian noise. The study does not imply computational hardness, validate finite-precision sampling, or assess any scheme. The accompanying verifier checks synthetic rational clipping identities and numerical Gaussian quadrature; it does not take external instances or perform any inference about them.
