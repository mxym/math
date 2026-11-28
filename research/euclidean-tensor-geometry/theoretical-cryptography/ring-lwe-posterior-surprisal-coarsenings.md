# Posterior surprisal and soft covering for arbitrary priors in broad ring learning

For a fixed public-design experiment, we identify the posterior surprisal of the true label up to bounded exponential tails, *uniformly for every prior chosen before the public design*. The same coupling gives the posterior surprisal of any deterministic coarsening of that label. A bivariate tilted comparison also yields an exact TV formula for those same priors and coarsenings. These results separate an information-onset threshold for a coarse label from the threshold for identifying it, and give Gaussian list-size windows. No efficient posterior computation, decoder, or implementation is supplied.

## 1. Model and main result

Fix an odd integer \(q\ge3\), \(\beta>0\), dyadic \(d\to\infty\), and \(R=(\mathbb Z/q)[X]/(X^d+1)\). Let the rank \(r\ge1\) be arbitrary and take any prior \(\mu=\mu_d\) on \(R^r\), independent of the design. Conditional on \(S\sim\mu\), take \(k\) rows
\[
 A_i\sim U_{R^r},\qquad Y_i=\langle A_i,S\rangle_R/q+E_i,
 \qquad f_b(y)=\sum_{j\in\mathbb Z} b^{j^2}e^{2\pi i j y},
\]
with all coefficients independent uniform, independent scalar errors of density \(f_b\), and \(b=\beta/d\). Assume \(t_d=kb^2\) lies in a fixed compact subinterval of \((0,\infty)\). Given the design, let \(\nu\) be the reference for the responses alone, with independent scalar densities \(g_b(y)=f_{b^{q^2}}(qy)=q^{-1}\sum_u f_b(y-u/q)\). Write \(L_s\) for the conditional response likelihood \(dP_s(\cdot\mid A)/d\nu\), and
\[
 Z=\log L_S(Y),\qquad W=-\log\mu(S).
\]
Under the true joint law, the distribution of \(Z\) given \(S,A\) is always that of a sum of \(kd\) independent copies of \(\log(f_b(E)/g_b(E))\), \(E\sim f_b\). In particular \(Z\) is independent of \(S,A\) as a random variable in this experiment.

For any deterministic feature \(F=f(S)\), chosen before \(A\), set \(W_F=-\log\Pr(F)\). Define the actual true-value posterior surprisals
\[
 H_S^{\mathrm{pt}}=-\log\Pr[S\mid A,Y],\qquad
 H_F^{\mathrm{pt}}=-\log\Pr[F\mid A,Y],
\]
evaluated at the realized \(S,F\). All logarithms are natural. There is a constant \(C\), independent of the prior, rank, and feature, for which
\[
 \begin{split}
 \Pr\big[|H_S^{\mathrm{pt}}-(W-Z)_+|>u\big]&\le C e^{-u},\\
 \Pr\big[|H_F^{\mathrm{pt}}-\min\{W_F,(W-Z)_+\}|>2u\big]&\le 2C e^{-u}
 \qquad (u\ge0).
 \end{split}                                                    \tag{1}
\]
The statements concern the joint law including \(A\), not an error bound for every fixed \(A\). For any finite collection of \(B\) prescribed features, the same probability of the maximum error exceeding \(2u\) is at most \(2BCe^{-u}\). Features or priors selected from the realized design are excluded. Writing \(H(F\mid A=a,Y)\) for the conditional entropy in the experiment at design \(a\), we have the useful deterministic-reference version
\[
 \mathbb E_A\left|H(F\mid A,Y)\big|_{A}
       -\mathbb E\min\{W_F,(W-Z)_+\}\right|=O(1).                \tag{2}
\]
The expectation on the right is independent of the realized design.

## 2. A finite overlap-to-surprisal comparison

The probabilistic argument needs only a first moment bound on false-label overlap; it does not require independent codewords. Consider an arbitrary finite label model with a design \(A\) independent of the label, a common conditional reference \(\nu\), and densities \(L_s\). Assume
\[
 \sup_{s\ne s'}\mathbb E_{A,\nu} L_s L_{s'}\le C_0 .            \tag{3}
\]
The argument in this section applies as stated to discrete, continuous, or mixed observations, and \(Z\) need not be independent of the true label in the general case.

Let \(L_\mu=\sum_s\mu(s)L_s\). For the actual label, put \(T_S=\sum_{s'\ne S}\mu(s')L_{s'}\); then \(L_\mu=e^{Z-W}+T_S\). Under the true joint experiment
\[
 \mathbb E T_S=
 \sum_s\sum_{s'\ne s}\mu(s)\mu(s')\mathbb E_{A,\nu}L_s L_{s'}
 \le C_0.                                                       \tag{4}
\]
Bayes' identity gives
\[
 H_S^{\rm pt}-(W-Z)_+
        =\log L_\mu-(Z-W)_+=:D.
\]
Since \(\log(e^x+y)\le x_++\log(1+y)\) for \(y\ge0\), \(D\le\log(1+T_S)\). Also \(D\ge0\) whenever \(Z-W\ge0\); otherwise \(D=\log L_\mu\). The true marginal response law given \(A\) has density \(L_\mu\), so \(\Pr[\log L_\mu<-u\mid A]\le e^{-u}\). Markov applied to \(1+T_S\) proves
\[
 \Pr(|D|>u)\le(2+C_0)e^{-u}.
\]
This bound does not approximate exponentially small likelihoods by a uniform absolute error and does not need a concentration estimate for every false prototype.

For each possible \(F=f\), apply the same result with prior \(\mu(\cdot\mid F=f)\). The overlap bound (3) is uniform in the prior, and conditioning on \(F\) keeps \(A\) independent; the true residual \(Z\) has the same definition. The conditional prior surprisal is \(W-W_F\). At the actual label \(H_F^{\rm pt}=H_S^{\rm pt}-H_{S\mid F}^{\rm pt}\) exactly. Subtracting the two approximations and using
\[
 (W-Z)_+-(W-W_F-Z)_+=\min\{W_F,(W-Z)_+\}
\]
give the second inequality in (1). Conditional Jensen and integration of the exponential error give (2) once the surrogate law is seen not to depend on \(A\). In particular, the same computation gives
\[
 \big|\mathbb E_A D(P_{Y\mid A}\Vert\nu)-\mathbb E(Z-W)_+\big|=O(1);
\]
this is a byproduct, not an additional assumption of the posterior argument.

## 3. Checking the overlap uniformly in the ring model

Put \(g=g_b\) and let \(\tau_a\) be the squared norm under \(g\,dy\) of the residue-\(a\) phase sector of \(f_b/g_b\). Scalar Parseval and \(g=1+O_q(b^{q^2})\) give
\[
 \tau_0=1,\quad \tau_{\pm1}=b^2+O_q(b^8),\quad
 \tau_a=O_q(b^8)\quad(a\notin\{0,1,-1\}).
\]
For \(s\ne s'\), let \(I=\sum_{j=1}^r(s_j-s_j')R\ne0\). In one random public row, \(\langle A,s-s'\rangle_R\) is uniform in \(I\), as it is the image of a uniform additive input under a homomorphism. The joint reference inner product of the two likelihoods depends on their difference shift. Averaging over the public row, orthogonality of grid phases gives precisely
\[
 \mathbb E_{A_i,\nu_i}L_{i,s}L_{i,s'}
       =\sum_{w\in I^\perp}\prod_{j=1}^d\tau_{w_j}.              \tag{5}
\]
The dot-product annihilator \(I^\perp\) is a proper ideal, as multiplication by \(a\) is adjoint to multiplication by \(a(X^{-1})\). It contains no signed monomial or signed binomial with distinct exponents. To see this for composite odd \(q\) as well, reduce modulo any maximal ideal: in its odd characteristic the image of \(X\) has exact order \(2d\), so an exponent difference of magnitude between 1 and \(d-1\) cannot have power \(1\) or \(-1\). A signed binomial or signed monomial is therefore a unit in \(R\).

Consequently the nonconstant terms in (5) either contain a residue other than \(0,\pm1\), or have weight at least three. The total is
\[
 1+O_q(db^8+d^3b^6)=1+O_q(d^{-3}),
\]
by a product binomial bound, since \(db^2=O(d^{-1})\). Multiplying over \(k=O(d^2)\) independent rows gives (3) with \(C_0=1+O(d^{-1})\), uniformly in \(s,s',r\). The availability of arbitrary rank in (1) comes from this one ideal for the label difference. It does not require the competing label vectors to be independent under the prior.

For use below, under the true residual distribution,
\[
 \mathbb E Z=t_d d+O(d^{-1}),\qquad
 \operatorname{Var} Z=2t_d d+O(d^{-1}),                         \tag{6}
\]
and the centered normalized variable converges to \(N(0,1)\). This follows from the same scalar cosine expansion: the mean and variance of \(\log(f_b(E)/g_b(E))\) are \(b^2+O_q(b^4)\) and \(2b^2+O_q(b^4)\), and its third absolute centered moment is \(O_q(b^3)\). Summing gives the stated errors and Lyapunov criterion. Uniform exponential deviations for any fixed linear-in-\(d\) gap about the mean also follow by Chernoff, since for any fixed real \(a\),
\[
 \log\mathbb E e^{aZ}=t_d a(a+1)d+O_{q,a}(d^{-1}),
\]
by integrating \(f_b^{1+a}g_b^{-a}\) and expanding through third order; the odd cosine terms integrate to zero.

## 4. Uniform soft covering via a bivariate tilted limit

The same model has the following design-conditional TV statement, with an error uniform over all priors chosen before the design:
\[
 \mathbb E_A\left|
     \operatorname{TV}(P_{Y\mid A},\nu)-\Pr[Z>W]\right|=o(1).
 \tag{8}
\]
For a prescribed feature \(F\), this also gives
\[
 \mathbb E_A\left|
   \operatorname{TV}(P_{F,Y\mid A},P_F\otimes\nu)
            -\Pr[Z>W-W_F]\right|=o(1).
 \tag{9}
\]
In (9), \(\nu\) is the specified reference, not the actual output marginal. When the prior itself has the right side of (8) tending to zero, \(\nu\) can also be replaced by \(P_{Y\mid A}\) in (9).

We need more than the first-moment overlap bound for this. For each nonzero ideal \(I\subseteq R\), the coefficient set of \(I\) is a product of \(d/d_0\) copies of a fixed base ideal, for a sufficiently large fixed dyadic \(d_0\) depending only on \(q\). Here is the argument also for odd composite \(q\). In the prime-power component \(p^e\Vert q\), the factors of \(X^{d_0}+1\bmod p\) have degree \(\operatorname{ord}_{2d_0}(p)\), and their Hensel lifts factor \(X^{d_0}+1\) into coprime monic factors modulo \(p^e\). For \(\ell=d/d_0\), substituting \(X^\ell\) gives a factorization at \(d\); each reduced factor is irreducible since its degree equals \(\operatorname{ord}_{2d}(p)\) once the degree ratio stabilizes. Each factor quotient has field modulo \(p\), and all its ideals are powers of \(p\): an element of minimal \(p\)-valuation in a nonzero ideal is \(p^j\) times a unit, by reduction to the field. Its units are precisely the elements nonzero modulo \(p\), since the kernel is nilpotent. Thus by CRT any ideal is the extension of one at \(d_0\), using the lifted factor idempotents, which are preserved by substitution. In the coefficient decomposition \(\bigoplus_{a<\ell} X^a R_{d_0}\), multiplication by that base ideal acts separately on the \(\ell\) blocks. This gives the claimed product description and a finite list of possible base ideals. Stabilization follows from \(v_2(p^{2^j}-1)=v_2(p^2-1)+j-1\) and the fact that every root has order \(2d\).

Fix \(s\ne s'\) and write \(I\) for their nonzero image ideal in (5). Under the joint reference including \(A\), the residual at \(s\) has law \(\nu\) independently of the uniform \(I\)-shift to the residual at \(s'\), by grid invariance; their pair law divides into independent base blocks. Within a block, write \(y\) for the residual at \(s\), \(v\) for the shift uniform on \(I_0\), and \(L_b^{(0)}(y)=\prod_{j\le d_0}(f_b/g_b)(y_j)\). Consider the probability law tilted by \(L_b^{(0)}(y)L_b^{(0)}(y-v/q)\), normalized by its mean. The normalizing factor is \(1+O(b^6)\) by (5) on the fixed base ring. Across all \(k\ell=O(d^3)\) independent blocks the normalization is \(1+O(d^{-3})\).

Under this pair-tilted base law, the mean vector of the two log-likelihoods is \((d_0b^2,d_0b^2)+O(b^3)\); their covariance matrix is \(2d_0b^2 I_2+O(b^3)\), and the third absolute centered moments are \(O(b^3)\). To check, let \(C,C'\) be the two sums of cosines, and \(D,D'\) the sums of their squared cosines. The two log-likelihoods expand as \(2b C-2b^2 D+O(b^3)\) and its primed version. The tilted density is \(1+2b(C+C')+O(b^2)\). Under the un-tilted base law, the cosine sums have mean zero, variances \(d_0/2\), and zero cross expectation: cross-coordinate terms integrate to zero under the independent \(y_j\), and the same-coordinate term is half the mean cosine of the phase shift, zero because every coordinate projection of the nonzero ideal \(I_0\) is a nontrivial subgroup. The latter follows from the signed cyclic shifts, and the primitive first character sums to zero on any such subgroup. The expected \(D,D'\) are \(d_0/2\). These facts give the expansions just stated. All terms are bounded uniformly over the finite list of ideal types.

The bivariate Lyapunov limit for the two whole-block log-likelihoods under the pair tilt is therefore independent standard normals after centering at \(t_dd\) and scaling by \(\sqrt{2t_dd}\): the accumulated mean and covariance errors are \(O(1)\), and the sum of third moments after normalization tends to zero. The bivariate distribution functions converge uniformly over lower rectangles (use continuity of the limit on a finite grid and then control both tails). The single true \(Z\) has the same asymptotic marginal by (6). It follows that, uniformly in real \(u,v\) and in all distinct labels,
\[
 \mathbb E_{A,\nu}
    \big[L_sL_{s'} \mathbf1_{\{\log L_s\le u,\ \log L_{s'}\le v\}}\big]
       =\Pr(Z\le u)\Pr(Z\le v)+o(1).                          \tag{10}
\]
The independence in (10) is a *tilted asymptotic*. The two codewords are not independent merely because their label difference generates a nonzero ideal.

To prove (8), choose \(h_d\to\infty\), \(h_d=o(\sqrt d)\), and for each label of positive prior mass trim \(L_s\) above log-likelihood \(-\log\mu(s)-h_d\), writing the result \(U_s\). Its reference mass \(m_s=\Pr[Z\le-\log\mu(s)-h_d]\) is the same for every \(A\). Put \(U_\mu=\sum_s\mu(s)U_s\), \(m=\sum_s\mu(s)m_s\). In the second moment of \(U_\mu\), (10) handles all off-diagonal pairs, with its uniform error weighted by \(\mu(s)\mu(s')\). The diagonal is at most \(e^{-h_d}\sum_s\mu(s)m_s\) since \(U_s\le e^{-h_d}/\mu(s)\). Hence \(\mathbb E_{A,\nu}|U_\mu-m|^2=o(1)\). The mass removed from the mixture is \(1-m\), while the reference mass outside its constant \(m\) is also \(1-m\); the expected TV is thus at most \(1-m+o(1)=\Pr[Z>W-h_d]+o(1)\).

For every \(A\), the union of the sets \(\{\mu(s)L_s>e^{h_d}\}\) has reference mass at most \(e^{-h_d}\) and true mixture mass at least \(\Pr[Z>W+h_d]\), so gives the corresponding lower bound on TV. By the one-dimensional CLT, the supremum over intervals of length \(2h_d\) of the probability for \(Z\) is \(o(1)\); using independence of \(Z\) and \(W\) also controls the random interval endpoints. The conditional lower bound and average upper bound consequently prove the \(L^1\) convergence in (8). The argument is uniform in the prior, since the only pair bound used was (10) uniformly over thresholds and label differences. Average (8) over the conditional priors \(\mu(\cdot\mid F)\) to obtain (9); this averages TV over disjoint feature fibers and uses the conditional prior surprisal \(W-W_F\). When \(P_{Y\mid A}\) is close to \(\nu\), the replacement claim follows by the triangle inequality.

## 5. One-shot list criterion and specific consequences

Let \(p_L(A)\) be the unrestricted optimal conditional probability that the true feature \(F\) lies in a reported list of at most \(L\) values. For any finite posterior, the largest-\(L\) mass is bounded, for \(\gamma\ge0\), by
\[
 \Pr[H_F^{\rm pt}\le\log L-\gamma\mid A]
  \ \le\ p_L(A)\
  \le\ \Pr[H_F^{\rm pt}\le\log L+\gamma\mid A]+e^{-\gamma}.     \tag{7}
\]
Indeed all values of posterior mass at least \(e^\gamma/L\) fit into a list of size \(L\); the contribution from values of mass below \(e^{-\gamma}/L\) to any list is at most \(e^{-\gamma}\). This is an optimal statistical bound, not a recipe for efficient list computation.

In (7) one may replace \(H_F^{\rm pt}\) by the surrogate \(V=\min\{W_F,(W-Z)_+\}\), moving the thresholds by any extra \(\rho\ge0\) and paying conditional bad probability \(\Pr[|H_F^{\rm pt}-V|>\rho\mid A]\), whose mean is \(O(e^{-\rho/2})\). Conditional on \(A\), the distribution of \(V\) is independent of the design. Therefore if the probabilities at the two surrogate thresholds converge to the same limit for any \(\gamma,\rho\to\infty\), then \(p_L(A)\) converges to that limit in \(L^1\) over \(A\). This explains why an averaged tail estimate in (1) gives a typical-design operational limit.

For concrete examples, fix \(r\), take \(S\) uniform on \(R^r\), write \(B=r\log q\), and let \(F\) be **any** balanced partition with \(M_d\) values, all fibers of the same size. Suppose \(h_d=\log M_d/d\to h\in(0,B)\) and \(\chi_d=B-h_d\to\chi>0\). The partition need not be a module map or a CRT splitting. Here \(V=\min(dh_d,(dB-Z)_+)\).

* At a fixed limit \(t_d\to t>0\), \(d^{-1}H(F\mid A,Y)\big|_A\) converges in \(L^1_A\) to \(\min(h,(B-t)_+)\). Thus the mutual information about the feature becomes linearly positive at its *fiber entropy* threshold \(t=\chi\), whereas unrestricted identification of the whole feature has its transition at \(t=B\).
* At the onset window \(\sqrt d(t_d-\chi_d)\to\xi\), the mutual information divided by \(\sqrt d\) converges in \(L^1_A\) to \(\mathbb E(\xi+\sqrt{2\chi}\,G)_+\), \(G\sim N(0,1)\). Also at this onset window, the design-conditional TV between the true joint feature and responses and the product of their actual marginals converges in \(L^1_A\) to \(\Phi(\xi/\sqrt{2\chi})\), by (8)–(9). For the information statement use (2), (6) and \(dh_d-V=(Z-\chi_dd)_+-(Z-Bd)_+\). For lists satisfying \(\log L=dh_d-a\sqrt d+o(\sqrt d)\) with \(a>0\), their optimal success converges to \(\Phi((\xi-a)/\sqrt{2\chi})\). The case of an order-smaller removal from the whole list (\(a=0\)) is not implied, because the capped surrogate has an atom at \(dh_d\).
* At any fixed \(t\in(\chi,B)\), if \(\log L=(B-t_d)d+a\sqrt d+o(\sqrt d)\), optimal list success converges in \(L^1_A\) to \(\Phi(a/\sqrt{2t})\), by (6)–(7) away from both caps of \(V\). In particular the feature can carry \(\Theta(d)\) mutual information while still requiring an exponentially large list for constant statistical success.
* For exact identification (\(L=1\)), at \(\sqrt d(t_d-B)\to\xi\) the optimal success converges in \(L^1_A\) to \(\Phi(\xi/\sqrt{2B})\), and it tends to zero or one exponentially in average error for fixed constant margins below or above \(B\). For the upper bound use (7) with a positive \(\gamma\to\infty\), \(\gamma=o(\sqrt d)\) in the critical window. Since \(dh_d\gg\gamma\), \(V\le2\gamma\) is equivalent to \(Z\ge dB-2\gamma\) eventually, and (1) controls the difference. For the lower bound even optimal **full label** success is at least the expectation of the true-label posterior probability. On \(Z-W\ge\gamma\) and \(T_S\le e^{\gamma/2}\), that posterior probability is \(1/(1+T_S e^{W-Z})\ge1-e^{-\gamma/2}\). By (4), the exceptional conditional probability has mean at most \(C_0e^{-\gamma/2}\), and the first event has a design-independent probability. Squeezing with (6) gives the claimed limit. Taking small linear \(\gamma\) under constant margins and using the Chernoff bound gives the stated exponential forms.

Here \(\Phi\) is the standard normal CDF. The entropy window uses uniform integrability from (6) to pass to positive-part expectations. All the results also apply when the balanced feature is exactly the quotient label of any fixed additive subgroup or a CRT projection. No formula for the full posterior distribution is implied beyond the surprisal coupling for the true realized values.

## 6. Prior and scope

* [Verdú and Han, A General Formula for Channel Capacity](https://web.mit.edu/6.441/www/reading/IT-V40-N4.pdf) and [Tan and Moulin, Fixed Error Asymptotics for Erasure and List Decoding](https://arxiv.org/abs/1402.4881) give the relevant information-spectrum and second-order list-decoding antecedents. The posterior-list threshold comparison (7) is elementary and not a new general coding theorem. [Merhav, A Statistical-Physics Refinement of Soft Covering](https://arxiv.org/abs/2605.01839) studies random-code partition functions and Rényi phases; we use only the finite planted-label/false-label decomposition and a uniform overlap bound, not a free-energy ansatz.
* [The earlier fixed odd-modulus search note](https://github.com/mxym/math/blob/18d24b1b/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-fixed-odd-modulus-threshold.md) gives exact entire-label search thresholds for a broader range of coefficient widths with uniform labels. [The public degree and TV note](https://github.com/mxym/math/blob/1aaf3b754c946fbefcfadcdee20fd3ae10648a1b/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-coordinate-degree-and-tv.md) obtains the marginal output TV profile. We do not count those uniform full-label results again. The new statements are the bounded-tail true-value posterior coupling and exact soft-covering profile for arbitrary priors and partitions, including the onset and list windows for coarse labels. The new moment check in (10) tilts the reference law by the product of two likelihoods and analyzes relative-ideal phase blocks; it does not assert independence of codeword rows under all changes of measure.
* This is an abstract independent-coefficient, broad-noise experiment, not a computational complexity classification or a statement about actual parameter choices. The finite verifier checks algebraic identities and small synthetic probability laws only, not label recovery.
