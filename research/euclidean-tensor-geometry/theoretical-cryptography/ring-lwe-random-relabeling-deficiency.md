# Near-maximal deficiency for random relabelings of broad dyadic experiments

Equal-dimensional experiments can be far apart even though both use the same ring, label set, broad spherical noise scaling, and independent uniform public designs. Compare two batch experiments by a uniformly random permutation of their labels, known to the randomization kernel. The asymptotic deficiency is the probability of failure of exact label identification in the *source* experiment, regardless of the positive information level of the target. The proof that no kernel can bridge the gap uses small overlap between entire families of credible lists, not computation assumptions or pairwise distances.

## 1. Setup and statement

Fix odd \(q\ge3\), let \(d\to\infty\) dyadic, and write \(R=(\mathbb Z/q)[X]/(X^d+1)\). Use a deterministic set \(\mathcal S_d\subset R^{r_d}\) of distinct labels with \(N=|\mathcal S_d|\), \(B_d=d^{-1}\log N\to B>0\), and \(r_d\le d^C\) for a fixed \(C\). There are two experiments, independently parameterized:
\[
 b_j=\beta_j/d,\quad \beta_j>0,\qquad k_j b_j^2=t_{j,d}\to t_j\in(0,\infty),
 \quad j\in\{1,2\}.
\]
At label \(s\), experiment \(j\) has \(k_j\) independent rows \(A_i\sim U_{R^{r_d}}\) and \(Y_i=\langle A_i,s\rangle_R/q+E_i\) on the coefficient torus, with independently wrapped scalar errors of density \(f_{b_j}(x)=\sum_h b_j^{h^2} e^{2\pi i h x}\). Write \(P^{(j)}_s\) for the resulting joint law of design and responses. The choice of \(s\) does not change the prior law of the design.

Let \(\psi\) be a uniform permutation of \(\mathcal S_d\), drawn independently of the experiment. For a fixed \(\psi\) define the two directed deficiencies
\[
 \begin{split}
 \delta_{\rm av}(\psi)&=\inf_K \frac1N\sum_s
        \operatorname{TV}(P^{(1)}_sK,P^{(2)}_{\psi(s)}),\\
 \delta_{\rm max}(\psi)&=\inf_K\max_s
        \operatorname{TV}(P^{(1)}_sK,P^{(2)}_{\psi(s)}).
 \end{split}
\]
The infima are over arbitrary Borel Markov kernels, which may depend on \(\psi\); both the public design and responses in the output may be changed, with no efficiency or causality restriction. This is the directed comparison of experiments in the sense of [Blackwell](https://digicoll.lib.berkeley.edu/record/112749) and [Le Cam's approximate sufficiency](https://doi.org/10.1214/aoms/1177700372).

Define \(p\) from the source alone:
* If \(t_1<B\), put \(p=0\); if \(t_1>B\), put \(p=1\).
* If \(t_1=B\) and \(\sqrt d(t_{1,d}-B_d)\to\xi\in[-\infty,\infty]\), put \(p=\Phi(\xi/\sqrt{2B})\), with the endpoint conventions for the standard Gaussian distribution function.

**Theorem.** With convergence in probability over the public choice of the permutation,
\[
             \delta_{\rm av}(\psi)\ \longrightarrow\ 1-p,\qquad
             \delta_{\rm max}(\psi)\ \longrightarrow\ 1-p .
\]
If the source critical coordinate has no limit, the corresponding statement applies along each subsequence along which it converges in the extended real line. The target may be in any of its subcritical, critical, or supercritical ranges, provided \(t_2>0\). The hypothesis excludes target observations independent of the label, for which both deficiencies are zero. This is a probability comparison for abstract broad-noise experiments, not a statement about a particular sample transform, computational recovery, or cryptographic scheme.

## 2. A general credible-list obstruction to relabelings

Let \(\eta_x(s)\) be the probability of label \(s\) after observing a source record \(x\) from the uniform label prior. Suppose there are deterministic credible lists \(L_1(x)\), \(L_2(y)\) with at most \(K_1,K_2\) labels, from finite families \(\mathcal F_1,\mathcal F_2\) respectively. Define \(\varepsilon_j\) to be the probability that the true label at a uniformly random label in experiment \(j\) is absent from its own list. Suppose every pair \(U\in\mathcal F_1,V\in\mathcal F_2\) satisfies
\[
                     |\psi(U)\cap V|\le D.                      \tag{1}
\]
For every \(h\ge0\),
\[
 \delta_{\rm av}(\psi)\ \ge\
  1-\varepsilon_1-\varepsilon_2-\Pr[-\log\eta_X(S)<h]-De^{-h},      \tag{2}
\]
where the probability is the source law with uniform \(S\).

To see this, include the hidden label as part of both laws *for the TV analysis*. By disjointness of its atoms, the TV of the joint laws is exactly the average of the fixed-label TVs. Test the event \(\psi(S)\in L_2(Y')\). Its target probability is \(1-\varepsilon_2\) because \(\psi(S)\) is still uniform. Under a simulated output from \(K\), \(\Pr[S\notin L_1(X)]=\varepsilon_1\) and the source high-posterior event has its original probability. Conditional on both \(X=x\) and the simulated output \(Y'=y\), the label still has posterior \(\eta_x\) (the kernel law depends only on \(x\)). On the remaining part of the event, at most \(D\) eligible labels lie in \(L_1(x)\cap\psi^{-1}(L_2(y))\) by (1), each with posterior mass at most \(e^{-h}\). Taking its probability proves (2), uniformly over all output kernels. The event used in this proof is a comparison certificate, not an estimator given only observations.

For a uniform permutation of an \(N\)-point label set with fixed \(U,V\), \(D_0\ge1\),
\[
 \Pr(|\psi(U)\cap V|\ge D_0)\le
 \binom{|U|}{D_0} (|V|/N)^{D_0}\le
   \big(e K_1 K_2/(N D_0)\big)^{D_0}.                            \tag{3}
\]
The first inequality unions the choices of distinct source labels; the images are sampled without replacement, whose probability of lying in \(V\) is at most \((|V|/N)^{D_0}\). If the count is impossible the probability is zero. In particular simultaneously over the families (1) holds with probability at least \(1-|\mathcal F_1||\mathcal F_2|e^{-D}\) for any integer \(D\ge e^2 K_1K_2/N\). The lists need not be independent, randomly drawn, or exchangeable.

## 3. Both experiments admit small finite families of credible lists

For experiment \(j\) let \(W_j\) be the true log likelihood against the independent full-grid response reference, and \(\eta^{(j)}\) its posterior under the prior \(U_{\mathcal S_d}\). The [posterior surprisal theorem, equations (1)–(4)](https://github.com/mxym/math/blob/15a25c0d1d01551372cfb03794958adc753ca3b6/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-posterior-surprisal-coarsenings.md) gives
\[
 -\log \eta^{(j)}(S)=(\log N-W_j)_++O_{\mathbb P}(1) .             \tag{4}
\]
This uses a prior chosen before the construction of the design. Its exponential-tail error is uniform and needs only the bounded pair overlap, not independent likelihood scores. The true score \(W_j\) is a sum of independent scalar logs \(\log(f_{b_j}/g_{b_j})(E)\) with true residual density \(f_{b_j}\), \(g_b=q^{-1}\sum_{u=0}^{q-1}f_b(\cdot-u/q)\); its distribution is the same for every fixed true label and every design. In particular
\[
 \operatorname{\mathbb E}W_j=t_{j,d}d+O(d^{-1}),\quad
 \operatorname{Var}(W_j)=2t_{j,d}d+O(d^{-1}),\quad
 (W_j-t_{j,d}d)/\sqrt{2t_{j,d}d}\ \Rightarrow\ N(0,1).             \tag{5}
\]
The scalar transform calculation in [the extremal process note, equation (1)](https://github.com/mxym/math/blob/178a3c4e54436a2c586605cb04a16547df077aed/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-extremal-likelihood-process.md) gives the same Taylor coefficients. Alternatively \(\log(f_b/g_b)=2b\cos(2\pi x)+O(b^2)\), and integration under \(f_b\) gives mean \(b^2+O(b^4)\) and variance \(2b^2+O(b^4)\), with odd terms canceled by circle symmetry. The standardized sum has a triangular CLT since each scalar log is \(O(b_j)\).

Set \(H_{j,d}=d(B_d-t_{j,d})_+\) and \(K_j=\lceil e^{H_{j,d}+d^{2/3}}\rceil\), which is strictly below \(N\) eventually since \(t_j>0\) and \(B>0\). From (4)–(5), the true surprisal is at most \(H_{j,d}+\frac12d^{2/3}\) with probability \(1-o(1)\). We construct a list family finite enough to use (3). Keep the finite design coordinates exact, round every response coordinate to a predeclared mesh of spacing at most \(d^{-3}\), and take the \(K_j\) labels of largest posterior at the rounded record, with fixed tie order. The uniform scalar derivative bound \(\|\partial_x\log f_{b_j}\|_\infty=O(b_j)\) follows from the absolutely convergent differentiated Fourier series and positivity near 1. The log of each response likelihood changes by at most \(O(k_j d b_j d^{-3})=O(d^{-1})\) under rounding, uniformly in the record and label. The log posterior changes by at most twice this error since the sum of likelihoods changes by the same multiplicative factor. On the high-probability surprisal event, the rounded posterior therefore exceeds \(1/K_j\). Fewer than \(K_j\) labels can exceed \(1/K_j\), and the true label is in the list. This proves \(\varepsilon_j=o(1)\). The lists are abstract tests, with no enforcement of computational access to the posterior.

The number of mesh records gives
\[
       \log|\mathcal F_j|=O(k_j d(r_d+\log d)).
\]
Indeed there are \(q^{d r_d k_j}\) designs and at most \((d^3+1)^{d k_j}\) rounded response vectors. Thus the log list-family sizes grow polynomially, even though the observation law is continuous. No restriction on the support of the simulated output is needed: the rounding and list construction apply to every output.

## 4. Apply the obstruction

Take \(D=\lceil e^2 K_1K_2/N+d^{C'}\rceil\) with fixed \(C'\) large enough to dominate both log list-family sizes. Then the common pair bound (1) holds with probability \(1-o(1)\) over \(\psi\). Let \(h=\log D+(\log d)^2\). This makes \(De^{-h}=o(1)\).

If \(t_1<B\),
\[
 \frac{\log D}{d}\ \longrightarrow\
    \max\{0,\ B-t_1-\min(t_2,B)\}
      \ <\ B-t_1 .
\]
Equation (4) implies the source surprisal divided by \(d\) tends to \(B-t_1\). Hence the high-posterior probability in (2) is \(o(1)\), proving the lower limit 1.

If \(t_1=B\), then \(H_{1,d}=o(d)\) whereas \(H_{2,d}\le (B-\min(t_2,B)+o(1))d\). Consequently \(K_1 K_2/N\to0\) exponentially, \(\log D=O(\log d)\), and \(h=(1+o(1))(\log d)^2=o(\sqrt d)\) tends to infinity. By (4), the source event \(-\log \eta^{(1)}(S)<h\) then has limiting probability \(\Phi(\xi/\sqrt{2B})\). For finite \(\xi\), sandwich it between the events \(W_1-\log N> \pm o(\sqrt d)\) using the tight additive error in (4): more explicitly on error at most \(h/2\), the event holds if \((\log N-W_1)_+<h/2\) and can hold only if \((\log N-W_1)_+<3h/2\). Subtract the negligible probability that the error exceeds \(h/2\). Now (5) and the vanishing normalized widths give the limit. The same sandwich and (5) give the limits for infinite \(\xi\). Equation (2) proves the lower limit \(1-p\). In the supercritical case the lower bound \(\delta_{\rm av}\ge0=1-p\) is enough. All these conclusions also lower-bound the worst-label deficiency.

## 5. Matching information-theoretic upper limit

For any two finite-label experiments, the directed deficiency to the second under any relabeling is at most the largest label-identification error of an abstract decision rule in the first. This is just a coupling of probability laws: conditional on the decided finite label, take the target law with its relabeled parameter; for a fixed true label the correct-decision part has exactly the desired target law, while the error part has TV at most the error probability. This is only an unrestricted comparison bound and requires no claim about efficient decisions.

In the present source, take a posterior mode under the uniform prior with any measurable tie choice. The [fixed-design extremal theorem, part 1](https://github.com/mxym/math/blob/178a3c4e54436a2c586605cb04a16547df077aed/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-extremal-likelihood-process.md) shows that conditional on every fixed true label, uniformly in its choice, the wrong maximum is
\[
 -t_{1,d}d+2d\sqrt{t_{1,d} B_d}+O(\log d)+O_{\mathbb P}(1).
\]
That theorem centers using \(\log(N-1)\), whose replacement by \(\log N\) is negligible. The uniformity follows from the uniform finite-tuple relative probabilities (its equation (5)) and upper-tail bound; it is not a statement jointly over all latent labels in one experiment. The true score satisfies (5). For \(t_1<B\) the \(O(d)\) location gap is unfavorable, and for \(t_1>B\) it is favorable. At \(t_1=B\), the normalized location difference between the true center and wrong center is
\[
 \frac{2d(t_{1,d}-\sqrt{t_{1,d}B_d})+O(\log d)}{\sqrt{2t_{1,d}d}}
     =\sqrt d(t_{1,d}-B_d)\,\frac{\sqrt 2}{\sqrt{t_{1,d}}+\sqrt{B_d}}+o(1).
\]
Together with the continuous true Gaussian limit this gives uniform success tending to \(p\), including at finite critical values where ties lie in a vanishing standardized interval. The worst-label deficiency is thus at most \(1-p+o(1)\) for every permutation. This completes both limits.

The [earlier exact symmetry classification](https://github.com/mxym/math/blob/0493a4bb320cd5e2740381680810b5b326a672d6/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-joint-sample-symmetries.md) characterizes certain zero-error relabelings at fixed dimension; it does not give a growing-dimensional quantitative gap. The present result concerns a typical permutation and even different source/target batch sizes, not every forbidden deterministic relabeling. It explains why low error on fixed pairs or entropy alone cannot be treated as arbitrary statistical interchangeability. No runtime, practical transformation, or system-specific consequence follows.
