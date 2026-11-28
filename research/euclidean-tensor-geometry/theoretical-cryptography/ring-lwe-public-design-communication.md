# Fully public coefficients: a sharp conditional spectral floor and fresh-batch communication

Earlier broad-noise communication notes treat the design coefficients as part of each private batch. Here **every coefficient is public for free**, before interaction begins. In the model below the centered conditional comparison has squared spectral norm asymptotic to \(b^2\), not exponentially small. A smooth positive truncation gives exactly that rate while retaining all but exponentially small mass; a stopped likelihood-ratio argument then gives a fresh-batch adaptive lower bound at the squared (rather than linear) accumulation scale. The result is an abstract resource bound, not a scheme analysis.

## 1. Model and statements

Fix an odd prime \(q\ge3\), \(0<t<\log q\), and \(\beta>0\). Let \(d\) be dyadic, \(R=\mathbb F_q[X]/(X^d+1)\), \(b=\beta/d\), \(k=\lfloor t/b^2\rfloor\), and \(M=kd\). A party's batch consists of \(k\) independent rows of the form \(Y_i=A_i s/q+E_i\), with \(A_i\) independent uniform in \(R\), a common \(s\in R\) uniform, and scalar errors of density \(f_b(x)=\sum_{j\in\mathbb Z}b^{j^2}e^{2\pi i jx}\). The reference \(\nu=G\,dy\) on the responses has scalar factor \(g(y)=q^{-1}\sum_{a\in\mathbb F_q}f_b(y-a/q)=f_{b^{q^2}}(qy)\). Write \(L(y)=\prod_j f_b(y_j)/g(y_j)\), and \(L_s(y)=L(y-As/q)\) for fixed public design \(A=(A_i)\).

Let \(U\le L\) be a nonnegative residual comparison, let \(m\) be the average of \(U\) over all independent response-grid shifts, and put \(\eta=\int(L-U)\,d\nu\). Here \(0\le m\le1\), since the grid average of \(L\) is exactly one. For a fixed \(A\) define
\[
 \mathcal C_{A,U}h(y)=\mathbb E_s h(s)\{U(y-As/q)-m(y)\},
 \qquad \lambda(A,U)=\|\mathcal C_{A,U}\|^2_{\mathrm{op}},
 \tag{1}
\]
from the uniform label \(L^2\) to \(L^2(\nu)\). All label modes, including the constant, are included.

**Conditional spectral result.** There is an explicit positive smooth truncation \(U\) with \(\eta\le e^{-c d}\) and
\[
 {\mathbb E}_A\big|\lambda(A,U)/b^2-1\big|\longrightarrow0.
 \tag{2}
\]
Moreover any comparison \(U\) with \(\int|L-U|\,d\nu=o(b)\) has \(\lambda(A,U)\ge(1-o(1))b^2\) for every \(A\) if the norm is defined. This lower bound concerns the spectral comparison, not an operational disclosure bound.

**Fresh-batch protocol bound.** Give \(P\) parties independent such batches conditional on the common hidden label. All their \(A\)'s are public, and coefficient disclosure is not counted as a message. The coordinator visits each party at most once; it may select the order and the queries from all public designs, shared randomness and previous messages. Party \(i\) can return an arbitrary stochastic function of its own private response batch, the public designs and that history, with alphabet size at most \(r_i\). There is no revisiting or shared private batch. Then the joint law of \(s\) and the final view is at TV distance at most
\[
 P e^{-c d}+\sqrt{D_d}+24D_d,\qquad
 D_d\le (1+o(1))b^2\sum_{i=1}^P(r_i-1),
 \tag{3}
\]
from the law in which all public designs and the protocol are the same, but every private response batch has independent reference law \(\nu\), independent of \(s\). Consequently if \(P(2^\ell-1)=o(d^2)\) for at most \(\ell\ge1\) bits per party, the joint law becomes asymptotically independent. This also bounds balanced-property advantage and excess exact-label or list success over the uniform guesses. No matching protocol, arbitrary revisit claim, or time bound for ordinary sample access is asserted.

## 2. Conditional Fourier decomposition

For each torus-grid residue vector \(w\in R^k\), let \(\Gamma_w\) be the squared norm of the \(w\)-sector of \(U\) under \(G\). These sectors are orthogonal because \(G\) is grid invariant. The bar \(\overline A_i=A_i(X^{-1})\) gives the adjoint for the coefficient dot product, as multiplication by \(X\) is a signed cyclic shift. For fixed \(A\) the \(w\)-sector of \(\mathcal C_{A,U}h\) is the \(U\)-sector multiplied by the label Fourier coefficient \(\widehat h(\sum_i\overline A_i w_i)\) if \(w\ne0\), and zero otherwise. Thus exactly
\[
 \lambda(A,U)=\max_{z\in R}\sum_{w\ne0:\,\sum_i\overline A_i w_i=z}\Gamma_w .
 \tag{4}
\]
For any positive or signed comparison within \(L^1\) error \(\eta_0\) of \(L\), a pure single-coordinate harmonic \(e^{2\pi i y_j}\) has scalar product with \(U\) of magnitude at least \(b-\eta_0\). It is a unit-norm vector in a nonzero residue sector, so that sector contributes at least \((b-\eta_0)^2\) to some group in (4), regardless of \(A\). This gives the spectral lower bound.

We will also use that every nonzero ideal has size at least \(\exp(\alpha_q d)\) for a fixed \(\alpha_q>0\). Each irreducible factor of \(X^d+1\bmod q\) has degree \(\operatorname{ord}_{2d}(q)\), a positive constant fraction of \(d\) for large dyadic \(d\), since \(v_2(q^{2^j}-1)=v_2(q^2-1)+j-1\) for \(j\ge1\). All factors are distinct. For \(w\ne0\), \(\sum_i\overline A_i w_i\) is uniform on the nonzero ideal \(\sum_i w_iR\). It follows that the probability a prescribed nonzero difference \(w-w'\) maps to zero is at most \(e^{-\alpha_qd}\).

## 3. Smooth positive truncation and its spectral tails

Set \(X(y)=\log L(y)\). Choose constants \(x>t\), \(\sigma>0\) with \(x+\sigma^2/2<\log q\). With \(\Phi\) the standard Gaussian CDF, take
\[
 U(y)=F(X(y)),\qquad F(u)=e^u\Phi((xd-u)/(\sigma\sqrt d)).
 \tag{5}
\]
Equivalently \(F(u)=e^u\Pr[u\le xd+\sigma\sqrt d\,Z]\) with \(Z\) standard normal. In particular \(0\le U\le L\), \(\sup U\le e^{(x+\sigma^2/2)d}\), and \(\|U\|_2^2\le e^{(x+\sigma^2/2)d}\) because \(\int U\le1\). Under the true residual measure \(L\,d\nu\), Chernoff gives \(\eta=\Pr[X+\sigma\sqrt d\,Z> xd]\le e^{-c d}\). Indeed for fixed \(a>0\) the scalar log moments yield
\[
 \log\mathbb E_{L\,d\nu}e^{aX}
 =t a(a+1)d+O(d^{-1}),
\]
by expanding \(\int f_b^{1+a}g^{-a}=1+a(a+1)b^2+O_q(b^4)\) as in the usual scalar cosine expansion. An independent Gaussian adds \(a^2\sigma^2d/2\); sufficiently small \(a>0\) works because \(x>t\).

**High degrees.** Let \(\Gamma_j^{\rm tot}=\sum_{\mathrm{wt}(w)=j}\Gamma_w\), where \(\mathrm{wt}\) is the number of nonzero scalar residues. For every fixed \(K>0\) there is a constant \(C_K\) such that
\[
 \sum_{j>C_Kd}\Gamma_j^{\rm tot}\le e^{-K d}.
 \tag{6}
\]
We justify this rather than assuming that clipping keeps the original product spectrum. The scalar Fourier transform of \(F\), with \(\widehat F(\xi)=\int F(u)e^{-i\xi u}\,du\), is
\[
 \widehat F(\xi)=\frac{\exp((1-i\xi)xd+(1-i\xi)^2\sigma^2d/2)}{1-i\xi}.
\]
Integrate \(e^{(1-i\xi)u}\) up to the independent Gaussian endpoint in (5), then take its moment. This is integrable in \(\xi\) and Fourier inversion applies. For \(V_\xi(y)=e^{i\xi X(y)}\), the sectors are tensor products of scalar functions \(e^{i\xi\log(f_b/g)}\). Each has \(L^2=1\); its total squared mass on nonzero residues is at most \(\|e^{i\xi\log(f_b/g)}-1\|_2^2=O_q(\xi^2b^2)\), because \(\log(f_b/g)=O_q(b)\) uniformly. Thus the high-residue-weight norm squared of \(V_\xi\) is a binomial tail with at most \(O_{\xi,t}(d)\) expected nonzero positions. For \(|\xi|\le H\), its tail after \(Cd\) is at most \(\exp[d(-C+O_{H,t}(1))]\) by direct exponential Markov. For \(|\xi|>H\) use norm at most one and the Gaussian decay of \(\widehat F\). First choose \(H\) large enough to absorb \(\exp[(x+\sigma^2/2)d]\) and any desired exponential error on that region; then choose \(C\) large enough on \([-H,H]\). Minkowski under Fourier inversion, with the projected \(L^2\) norm, proves (6).

**Bounds at low degrees.** For \(0<u\le1\), apply the positive product operator which, independently on each scalar coordinate, keeps its phase with probability \(u\), otherwise averages over all its phase translations. It multiplies a \(w\)-sector by \(u^{\mathrm{wt}(w)}\). Since \(0\le U\le L\), the pointwise order remains valid after applying it. By squaring norms and using the product sectors of \(L\), this gives
\[
 \sum_{j\ge0}u^{2j}\Gamma_j^{\rm tot}\le(1+u^2B)^M,\qquad
 B=\sum_{a\ne0}\|(f_b/g)_a\|_2^2=2b^2+O_q(b^8).
 \tag{7}
\]
Here the original coefficient sectors follow from scalar Parseval, and the zero sector equals one. Taking \(u^2=j/(MB)\) for \(1\le j\le MB\) bounds \(\Gamma_j^{\rm tot}\le(eMB/j)^j\). The comparison \(U\) is invariant under permutations of all \(M\) scalar positions, not only within a row. Thus each support of size \(j\) has the same total sector mass, and
\[
 \Gamma_w\le(eB)^j\quad(\mathrm{wt}(w)=j\le MB)
 \tag{8}
\]
by \(\binom Mj\ge (M/j)^j\).

For the exact leading one-coordinate sectors, average \(L-U\) over all phases **outside** one coordinate \(j\), with all within-cell positions and \(y_j\) fixed. This average is \(e^{X_j}\) times the expectation of the lost Gaussian cutoff probability under the product of true scalar **phase** weights on the other coordinates, where \(X_j=\log(f_b(y_j)/g(y_j))=O(b)\). The weights are normalized by the zero-sector identity. Uniformly over the within-cell choice, for fixed \(a>0\) their scalar conditional moment is
\[
 \mathbb E_{\mathrm{true\ phase}}\big[e^{a X_i}\mid q y_i\bmod1\big]
   =1+a(a+1)b^2+O_q(b^3).
\]
Indeed on a shifted \(q\)-point grid the mean cosine is zero and the mean cosine square is \(1/2\) for all odd \(q\), and \(g=1+O(b^9)\). The allowed \(O(b^3)\) error sums to only \(O(1)\) over \(M\) coordinates. The same strict Chernoff margin \(x>t\), now uniform in the within-cell choice, proves that this outside-phase average of \(L-U\) is \(O(e^{-c'd})\) in supremum norm. Project further onto any chosen nonzero residue at the single coordinate; its \(L^2\) norm is at most the norm just bounded. The corresponding original sector norm squared is \(\tau_{\pm1}=b^2+O_q(b^8)\), or \(O_q(b^8)\) for other residues. Thus uniformly over all weight-one sectors their squared norms differ from those original values by \(O(e^{-c'd})\).

## 4. Controlling the largest image group

Split (4) into degree one, low degrees \(2\le j<c_0d\), middle degrees \(c_0d\le j\le C d\), and the tail (6). The constants \(c_0\) small and \(C\) large will be fixed. For degree one, all the words have distinct image group targets with probability \(1-e^{-\Omega(d)}\). There are only \((q-1)M=O(d^3)\) words, and each equality for distinct words has probability at most \(e^{-\alpha_qd}\). In this event the maximum one-degree contribution is \(b^2(1+o(1))\). In its complement, the total one-degree mass is \(O(d)\) by (7), so the exceptional contribution is negligible in expectation.

For the low band let \(W=\sum_{2\le j<c_0d}\Gamma_j^{\rm tot}\). Choose an integer \(r\ge4\). By (7), choose \(c_0>0\) small so that \(c_0d<MB\) and \(W\le\exp(\alpha_q d/(2r))\), using the coefficient bound \((eMB/j)^j\). In the \(r\)-th moment sum over all target groups \(z\), any tuple of words not all identical requires the image of a nonzero difference to be zero. Its total contribution is at most \(e^{-\alpha_qd}W^r\). By (8) the diagonal contribution is at most
\[
 \sum_{j\ge2}\binom Mj (q-1)^j(eB)^{rj}
  =O_r\big((MB^r)^2\big)=O_r(d^{6-4r}).
\]
Here the sum is interpreted over \(j\le M\); omitting the constant and linear terms of a binomial gives the bound. Taking the \(r\)-th root shows the expected maximum group mass from low degrees at least two is \(O_r(d^{6/r-4})+e^{-\Omega(d)}=o(b^2)\).

For the middle band let \(W_j=\Gamma_j^{\rm tot}\) and sample a word of weight \(j\) with probability proportional to \(\Gamma_w\), ignoring \(j\)'s of zero mass. By permutation invariance its support is uniform, regardless of within-support residue dependence. With probability \(1-e^{-\Omega(d\log d)}\), at least \(j/2\) rows contain one occupied position: otherwise all positions fall within at most \(3j/4\) rows, and the union bound is \(\binom{k}{a}(a/k)^j\) with \(a=\lfloor3j/4\rfloor\). For two independently chosen weighted words of such degrees, with the same high probability each has at least one single-occupied row not touched by the other. For any specified \(h\) singleton rows, the probability the other word of weight \(l=O(d)\) hits all of them is at most \((l)_h d^h/(kd)_h\le(2l/k)^h\). Missing an exclusive row requires hitting at least a linear number of these singleton rows; even allowing a \(2^{O(d)}\) choice factor makes the failure \(e^{-\Omega(d\log d)}\). Since \(q\) is prime, every nonzero singleton residue supplies a unit monomial. One singleton row makes a single image uniform on \(R\); two exclusive such rows make the two images jointly uniform on \(R^2\), conditional on the other public coefficients.

It follows by the same first- and second-moment expansion that, for each \(z\), the expected absolute difference between its degree-\(j\) mass and \(q^{-d}W_j\) is at most \(W_j e^{-\Omega(d\log d)}\). Summing over \(q^d\) targets to bound the expected maximum error and over all middle degrees still gives \(e^{-\Omega(d\log d)}\), since \(\sum W_j\le e^{(x+\sigma^2/2)d}\). The deterministic comparison \(q^{-d}\sum W_j\) is exponentially small by the choice of \(x,\sigma\). Together with (6) and the low band this proves the upper side of (2); the uniform single-harmonic lower bound in Section 2 proves convergence in \(L^1\). This argument would need an additional nonunit-residue bound in the middle band for composite \(q\), which is not claimed.

## 5. Adaptive composition without first-order accumulation

Replace each party's true conditional law by the probability density \(U(y-As/q)+1-m(y)\) relative to \(\nu\). This is nonnegative of mass one, and differs from the true law in TV at most \(\eta\) for every \(s,A\), because the discarded and reinserted pieces each have mass \(\eta\). Coupling all parties adds at most \(P\eta\) to the total variation distance.

Let \(Q\) be the joint law of public information, uniform label, and view under the reference, and let \(P_*\) be the corresponding joint law for the replaced probabilities. Condition on all public designs and shared tapes. Given the public message prefix under the reference (not including the hidden label), \(s\) is uniform and independent, and the next party has not been seen; for each fixed \(s\), in either law its response block is independent of the past once its design is given. For an encoder with output probabilities \(F_j(y)\) and reference masses \(p_j=\int F_j\,d\nu\), write the replaced conditional output as \(p_j+\Delta_{s,j}\). For \(p_j>0\),
\[
 \mathbb E_s \Delta_{s,j}^2
 \le \lambda(A,U)\operatorname{Var}_{\nu}(F_j)
 \le \lambda(A,U)p_j(1-p_j)
\]
by (1) and its dual, since the comparison has mean zero. The variance bound uses \(0\le F_j\le1\). If \(p_j=0\), the replaced output mass is zero too, by absolute continuity. Thus the mean conditional \(\chi^2\) relative to the reference is at most \((r_i-1)\lambda(A_i,U)\) for the visited party. Even if the order depends on all public designs and transcripts, the sum along every reference path is bounded by the sum over all distinct available parties. The total expected conditional \(\chi^2\), denoted \(D_d\), is therefore bounded as in (3) by (2).

For clarity, the following elementary stopping argument converts this **reference-path** quantity to TV, without assuming adaptive queries are independent. Use the filtration that *includes* the label at time zero, with the one-step conditional discrepancies averaged over it in \(D_d\). Let \(M_j\) be the cumulative likelihood ratio of \(P_*\) relative to \(Q\), starting at one; the one-step ratio has conditional \(Q\)-mean one. Stop multiplying after the first time the ratio leaves \([1/2,2]\), and write \(M_j^\star\) for this stopped martingale (it retains the first crossing increment). Conditional variance of each kept increment is at most four times the corresponding conditional \(\chi^2\) because the preceding ratio is at most two. Orthogonality of martingale increments yields \(\mathbb E_Q|M_P^\star-1|^2\le4D_d\). The \(Q\)-probability of crossing is at most \(16D_d\), since on a crossing the stopped ratio differs from one by at least \(1/2\). Under the stopped law of density \(M_P^\star\) relative to \(Q\), the same event has mass at most \(16D_d+\sqrt{4D_d\cdot16D_d}=24D_d\). Its mass under \(P_*\) is identical: the stopped law runs the same transitions as \(P_*\) until the crossing, then follows \(Q\). Thus TV from the stopped law to \(P_*\) is at most \(24D_d\), while its TV to \(Q\) is at most \(\sqrt{D_d}\). An early terminating protocol may be padded with deterministic messages. Adding \(P\eta\) proves (3). The order may be arbitrary and adaptive, but reusing a party would break the fresh-response conditional law used above.

## 6. Prior and scope

* [Acharya, Canonne and Tyagi, Inference under Information Constraints I](https://proceedings.mlr.press/v99/acharya19a.html) and [Acharya, Canonne, Liu, Sun and Tyagi, Interactive Inference under Information Constraints](https://arxiv.org/abs/2007.10976) develop general contraction and composition techniques for decentralized statistics. We do not claim that output-alphabet contraction or adaptive lower bounds are new general ideas. Here the spectral comparison is for a continuous ring experiment with **data-bearing coefficients** publicly disclosed, not just a public random coin.
* [The preceding batch communication result](https://github.com/mxym/math/blob/9c7c903b1aa999d663b8bc4f5b48ad499beb738e/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-batch-communication-entropy-scale.md) averages over coefficients inside private observations, so its exponentially small spectrum does not apply here. [The public coordinate-degree spectrum](https://github.com/mxym/math/blob/1aaf3b754c946fbefcfadcdee20fd3ae10648a1b/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-coordinate-degree-and-tv.md) handles the original product density and the binomial degree profile. The new ingredients for fully public communication are the smooth cutoff on the actual Shannon side, its high-degree sector control and sharp conditioned spectral floor, and the reference-path squared composition.
* The model uses fixed odd prime modulus, broad independent noise, finite-alphabet one-visit protocols and exact continuous conditional responses. No deployment, adaptive revisiting, concrete parameters, algorithm for label recovery, or general Ring-LWE time implication is inferred.
