# Extremal likelihood process, frozen weights and microscopic ties in a broad dyadic model

The earlier large-deviation calculation gave the leading free energy of the competing-label likelihoods. We resolve the order-one extremal point process, including for a typical fixed realization of the shared public coefficients. For temperatures above freezing this gives the full limiting ranked weights, and a separate local comparison resolves the rare order-one tie between the specified true score and its competitors. These are probability statements about an explicitly given ensemble, not an algorithm to find high-scoring labels.

## 1. Setup and results

Let \(q\ge3\) be fixed and odd, \(d\to\infty\) dyadic, and \(R_d=(\mathbb Z/q)[X]/(X^d+1)\). Fix \(\beta>0\), \(b=\beta/d\), and \(k=k_d\) with \(t_d=kb^2\to t>0\). Let \(\mathcal S_d\subseteq R_d^r\) be a deterministic finite set of distinct labels (the rank \(r\) may vary), and choose \(s\in\mathcal S_d\) before seeing the design. Let \(n_d=|\mathcal S_d|-1\), \(B_d=(\log n_d)/d\to B>0\). Draw \(A_i\) independently uniformly in \(R_d^r\), and conditional on \(A\) and true label \(s\) observe \(Y_i=\langle A_i,s\rangle_R/q+E_i\) on the coefficient torus, with independent scalar errors of wrapped density \(f_b(y)=\sum_h b^{h^2}e^{2\pi i h y}\). Set \(g_b=q^{-1}\sum_{u=0}^{q-1}f_b(\cdot-u/q)\), and write \(X_v\) for the logarithm of the joint conditional response density at \(v\) divided by \(g_b^{\otimes kd}\).

Put \(V_d=2t_dd\), \(\alpha=\sqrt{B/t}\), and
\[
 z_d=\sqrt{2\log n_d}-
       \frac{\log\log n_d+\log(4\pi)}{2\sqrt{2\log n_d}},\qquad
 u_d=-t_dd+\sqrt{V_d}\,z_d .
\]
Define the point measure \(\Xi_d=\sum_{v\ne s}\delta_{X_v-u_d}\) and the true-score mark \(Z_d=(X_s-t_dd)/\sqrt{V_d}\).

1. Conditional on the public design \(A\), the joint law of \((\Xi_d,Z_d)\) converges to an exponential Poisson point process \(\Xi\) of intensity \(\alpha e^{-\alpha x}\,dx\) and an independent standard Gaussian \(Z\). Precisely, for each bounded continuous test (vague topology for the point measure) the conditional expected test converges in \(L^2\) over \(A\) to its limiting expectation. This also holds for the highest point jointly with the mark. Thus \(\Pr(\max_{v\ne s}X_v-u_d\le x\mid A)\to\exp[-e^{-\alpha x}]\) in probability over \(A\).
2. Fix a score multiplier \(\theta>\alpha\) (lower physical temperature). The sequence of decreasing normalized weights \(e^{\theta X_v}/\sum_{w\ne s}e^{\theta X_w}\), \(v\ne s\), converges in distribution in \(\ell^1\) to \(\mathrm{PD}(\alpha/\theta,0)\), jointly and independently with \(Z\). The conditional-law interpretation in part 1 holds for \(\ell^1\) tests as well. Here the Poisson–Dirichlet law is defined by ranking and normalizing the points of intensity \((\alpha/\theta)y^{-1-\alpha/\theta}\,dy\) on \((0,\infty)\).
3. Suppose \(a_d=(u_d-t_dd)/\sqrt{V_d}\to a\in\mathbb R\). For any fixed interval \(I\) of positive finite length, the event \(X_s-u_d\in I\) has probability asymptotic to \(|I|\phi(a)/\sqrt{V_d}\), where \(\phi\) is the standard Gaussian density. On this event \(\Xi_d\) still converges to \(\Xi\), independently of \(U=X_s-u_d\) which tends to uniform on \(I\). For \(\theta>\alpha\), the weight of the true label in the normalization over **all** labels then converges to
   \[
       \frac{e^{\theta U}}{e^{\theta U}+\sum_{x\in\Xi}e^{\theta x}}.
   \]
   The law given design and the tie event converges in the same \(L^2\)-test sense. The rare tie condition does not bias the law of the design.

4. Let a finite-message summary of the responses have at most \(M_d\) values; it and the final readout may use all public coefficients, with arbitrary private or shared randomization independent of the experiment. The readout returns at most \(\ell_d\) candidate labels. If \(M_d\ell_d=o(n_d)\), the probability that the list contains a wrong label within any fixed additive score margin of the best wrong score tends to zero. This also holds under the tie condition in part 3. It is a restricted summary/list result, not a claim about selecting the true label from unrestricted access.

If instead \(\sqrt d(t_d-B_d)\to\xi\in\mathbb R\), without conditioning on a tie, and \(\theta>\alpha=1\), the full decreasing weight sequence converges to a mixture: the single atom of weight 1 with probability \(\Phi(\xi/\sqrt{2B})\), otherwise \(\mathrm{PD}(1/\theta,0)\). Here \(\Phi\) is the standard normal distribution function. All claims are for the specified ensemble with fixed odd modulus and spherical product noise; they do not establish a general computational-time or sampling-complexity implication.

## 2. Uniform complex transforms with shared-design replicas

Use one or two independent response experiments conditional on the *same* \(A\) and fixed true label \(s\). Within each replica choose any fixed finite number of distinct wrong labels; labels may repeat across replicas without restriction. Define the listed scores to include the wrong ones and optionally the true score of each replica. For complex coefficients \(z\) in a fixed bounded set, the joint transform is
\[
 \mathbb E_s\exp\!\left\{\sum_j z_j X_j\right\}
   =\exp\!\left\{\sum_j(\mu_j z_j+V_d z_j^2/2)+O(d^{-1})\right\},
 \quad
 \mu_j=\begin{cases}-t_dd & \text{wrong},\\ t_dd & \text{true}.\end{cases} \tag{1}
\]
The error is uniform over the labels and bounded complex coefficients. This extends the transform in [the free-energy note, equation (4)](https://github.com/mxym/math/blob/9528947a2b9802d7d09f14686133f9c3e9ae0eb1/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-free-energy-and-mixing-obstruction.md), not a statement of independence for the full process.

Indeed, at one scalar coordinate within one replica, integrate under the \(g_b\) reference; include the true density as exponent 1, or \(1+z_j\) for a true score being tested. If \(a_j\) are the resulting exponents and \(y_j\) the scalar grid shifts, the integral equals
\[
 1+b^2\left[\sum_j a_j(a_j-1)+
       2\sum_{i<j}a_i a_j\cos(2\pi(y_i-y_j))\right]+O(b^4).
\]
This follows from \(\lambda_b=f_b/g_b=1+2b\cos+O(b^4)\) uniformly, with cubic terms vanishing by the half-period shift. This scalar expansion also applies to complex powers because \(\lambda_b\) is positive and close to 1. For each nonzero label difference, the row image is uniform on a nonzero ideal \(J\) of \(R_d\). The coefficient-dot annihilator is a proper ideal by the multiplication involution adjoint. It contains no signed monomial or signed two-term sum in distinct coordinates, since each is a unit (in every odd residue field the root has exact order \(2d\)). It also contains no \(2X^j\). Thus each cosine has mean zero, variance \(1/2\), and for any given label difference two distinct coordinates have covariance zero. The sum of its \(d\) coordinates has second moment \(d/2\).

Multiply the scalar factors for all coordinates and replicas *conditional on \(A_i\)*, using independent residual noises between replicas. The row log transform is
\[
 d b^2 C(z)+b^2 H(A_i,z)+O(db^4),
\]
with \(C(z)\) the deterministic sum from the individual quadratic terms, and \(H\) a fixed finite linear combination of the just-described cosine sums. Its mean is zero, its second absolute moment is \(O(d)\) by Cauchy–Schwarz, and \(|H|=O(d)\) deterministically. This estimate does not use independence between different differences or independence between the replicas' designs. The average of \(e^{b^2H}\) is \(1+O(db^4)\). Apply independence of the \(k\) public rows, and use \(kdb^4=O(d^{-1})\). The exponents \(z(z-1)\) and \((1+z)z\) respectively give (1). Repetitions across replicas do not create a single-coordinate cross term because the scalar integrals were separate.

## 3. A tilted local limit on the unscaled score axis

Write \(\lambda_d=z_d/\sqrt{V_d}\), so \(\lambda_d\to\alpha>0\) and \(u_d=\mu_{\rm wrong}+V_d\lambda_d\). For any finite selected tuple of \(m\) wrong scores in one or two replicas, tilt the joint law by \(e^{\lambda_d\sum_{j=1}^m X_j}\) and normalize; denote expectation under it by \(E_\lambda\). Write \(x_j=X_j-u_d\). There are two versions of the true marks in the local limit:
* Any number \(h\) of true marks on the *unscaled* axis, centered at constants \(c_{i,d}\) with \((c_{i,d}-t_dd)/\sqrt{V_d}\to a_i\). Write \(x_{m+i}=X_{s,i}-c_{i,d}\).
* Other selected true marks standardized as in \(Z_d\). No replica's true score is counted twice.

For fixed \(m,h\) with \(m+h\ge1\), finite compactly supported continuous \(F\) on the unscaled axes, and bounded continuous \(G\) of the standardized marks, the tilted joint local limit is
\[
 (2\pi V_d)^{(m+h)/2}
     E_\lambda[F(x)G(Z)]
    \longrightarrow
    e^{-\frac12\sum_{i=1}^h a_i^2}
       \left(\int_{\mathbb R^{m+h}}F(x)\,dx\right)\mathbb E G(N),          \tag{2}
\]
where \(N\) has independent standard Gaussian components. The statement is uniform in the listed labels. In addition, the absolute scaled mass of each translated unit cube on the \(x\) axes is bounded uniformly, without a restriction on its location. Formula (2) applies to box indicators, and to box indicators multiplied by continuous weights on that box.

For proof divide (1), at the complex tilt plus imaginary test frequencies, by the transform at the real tilt. For \(x\) frequencies \(w\) in a fixed bounded box and standardized mark frequencies \(\eta\) fixed, this gives the characteristic function
\[
 \exp\!\left\{-V_d\|w\|^2/2
          +i\sum_{i=1}^h w_{m+i}(t_dd-c_{i,d})
          -\|\eta\|^2/2+O(d^{-1})\right\}.                              \tag{3}
\]
The wrong linear terms cancel at the tilt and the standardized ones cancel by their own centering. The uniform bound on its absolute value is a constant times \(e^{-V_d\|w\|^2/2}\). For Schwartz \(F\) with compactly supported Fourier transform, integrate (3), set \(w=v/\sqrt{V_d}\), and apply dominated convergence. The inverse Fourier transform of the standard Gaussian at \((0,\ldots,0,a_1,\ldots,a_h)\) gives the constant in (2). This first proves (2) for characteristic functions on the standardized marks.

To justify extension without a high-frequency density bound, take in one dimension \(K(x)=(\sin x/x)^2\), positive and bounded below on \([-1,1]\), whose integrable Fourier transform has compact support. Use its product and arbitrary translations as upper tests for any unit cube. Formula (3) integrated against this product gives the uniform scaled cube bound. For a compactly supported continuous \(F\), convolve with Schwartz approximate identities with compactly supported Fourier transforms (e.g. the normalized squared modulus of a Schwartz function with smooth compact Fourier support, rescaled). In addition to uniform convergence on compact sets, the error summed as suprema over unit cubes tends to zero: compact support leaves finitely many nearby cubes, and outside a fixed larger compact set the Schwartz decay of the convolution tails gives a summable bound tending to zero. The cube bound therefore permits passage from the bandlimited tests to \(F\). For nonnegative \(F\) of positive integral and weighting the finite measures on the standardized marks by \(F\), characteristic-function convergence and their masses give weak convergence to the Gaussian law. General \(F\) follows by linearity; a nonnegative continuous majorant and minorant for a boundary-null box extend the result by squeezing. Uniformity follows either from the uniform errors above or by applying the argument to an arbitrary sequence of choices of labels.

Untilt on any fixed boxes \(J_j\) for the wrong \(x_j\), permitting finite boundaries. The prefactor combining the tilt and its normalization is
\[
 e^{-mV_d\lambda_d^2/2+O(d^{-1})},\qquad
 \frac{n_d\, e^{-V_d\lambda_d^2/2}}{\sqrt{2\pi V_d}}\ \longrightarrow\ \alpha,
                                                                         \tag{4}
\]
the latter by expansion of \(z_d^2\). The residual factor in the box integral is \(\prod_j e^{-\lambda_d x_j}\). Thus for \(h\) unscaled true intervals \(I_i\), in addition to any test \(G\) of standardized marks,
\[
 \begin{split}
 &n_d^m V_d^{h/2}\,
 \mathbb E_s\!\left[
     G(Z)\prod_j {\bf1}_{X_j-u_d\in J_j}
           \prod_{i=1}^h {\bf1}_{X_{s,i}-c_{i,d}\in I_i}\right]\\
 &\qquad\longrightarrow
 \mathbb E G(N)\,
 \prod_j\int_{J_j}\alpha e^{-\alpha x}\,dx\,
 \prod_{i=1}^h |I_i|\phi(a_i).
 \end{split}                                                            \tag{5}
\]
For \(m=0\) the same argument uses no tilt. When \(m=h=0\), (1) with standardized frequencies gives directly the Gaussian limit. This distinction prevents interpreting a global central limit theorem as a relative estimate for exponentially rare boxes; (2) is a local statement in every unscaled selected score coordinate.

## 4. From factorial moments to the fixed-design limit

For disjoint bounded intervals, mixed factorial moments of their counts expand into sums over exactly the distinct tuples within each replica. A repeated index among different bins of the same replica contributes zero. The number of tuples for \(m_i\) entries in a replica is \((n_d)_{m_i}\). Repetition *across* replicas is allowed and gives the product counts. Applying (5), the moments converge to those of independent Poisson bin counts, also independently between replicas. The standardized mark factor in (5) gives independence of the Gaussian marks. Conditional on prescribed true tie events in one or two replicas, divide (5) by the event probability; it cancels the \(V_d^{-h/2}\phi(a)^h\) factor and shows the same count limits and independent uniform local marks on the conditioning intervals (use subintervals there).

For clarity, finite families of these counts are tight by the first moment. Every fixed joint factorial moment is uniformly integrable because the moments one degree higher are bounded. Passing on a convergent subsequence thus retains the moments. The independent Poisson law is moment determinate (its moment generating function exists everywhere); weighted by any nonnegative bounded continuous test of the true marks, the remaining normalized count law has the same moments, hence is the same Poisson product. This proves the finite-interval convergence and joint independence. The first moment bound on every compact interval gives tightness for the vague point measures, and the finite-interval limits determine the Poisson processes. In the tie setting, compactness of the conditioned true intervals and convergence on their subintervals gives the same reasoning for the local marks. All such interval boundaries have zero limiting mass.

The maximum also converges, including in the tie setting: for any fixed \(K>0\), an upper point outside \([-K,K]\) has probability \(O(e^{-cK})\), uniformly for large \(d\) (proof below), and the probability of no point above \(-K\) converges to \(\exp(-e^{\alpha K})\) after taking the upper truncation to infinity. The same consequences hold jointly for both replicas. For any bounded continuous test \(F\) of one process and its marks, the unconditional one-replica limit gives the limit of \(E_A E[F\mid A]\); the independent two-replica limit gives the limit of \(E_A |E[F\mid A]|^2\) by conditional independence. This proves \(L^2\) convergence of the conditional expected test. Conditioning on the rare true tie does not reweight \(A\): conditional on \(A\), the true score is a function only of the independent true residuals and its law is constant in \(A\). Two replicas conditioned on their own tie events remain independent conditional on \(A\). The same second-moment argument therefore establishes the conditional conclusion in part 3.

## 5. Gibbs tail control and the true score

For a single wrong score, the uniform cube bound of §3 and untilting give a constant \(C\) with
\[
 n_d\,\Pr_s(X_v-u_d\in[x,x+1])\le C e^{-\lambda_d x}
 \quad(x\in\mathbb R),                                                  \tag{6}
\]
using (4). The same bound holds given \(X_s-u_d\in I\) under the hypothesis of part 3: use the two-coordinate cube bound and cover the true interval by finitely many unit intervals, then divide by a probability comparable to \(1/\sqrt{V_d}\). Constants may depend on \(I,a\) but not \(x\). Summing (6) on integer bins above \(K\) bounds the chance of any high point by \(O(e^{-cK})\). For fixed \(\theta>\alpha\) and bins below \(-K\) it gives
\[
 \mathbb E_s \sum_{v\ne s}e^{\theta(X_v-u_d)}
             {\bf1}_{X_v-u_d<-K}=O(e^{-c'K})                         \tag{7}
\]
with \(c'>0\), both with and without the tie condition. This step is needed for the normalized Gibbs weights; convergence of the point process alone would not control the many low points. Corresponding bounds hold for the limiting Poisson process by its intensity. Its total weight is almost surely positive and finite: points above zero have finite count, and the expected weight sum below zero is finite since \(\theta>\alpha\).

On a finite window the ranking and weighting converge, because the limiting point process is simple and has no points on the boundaries. Markov's inequality in (7), then increasing the window, gives convergence in distribution in \(\ell^1\) of the decreasing unnormalized weights centered at \(u_d\), jointly with the true marks; normalization is continuous at positive total mass. Changing variable \(y=e^{\theta x}\) in the Poisson intensity gives the Poisson–Dirichlet definition in part 2. The same truncation argument for two replicas and the \(L^2\) argument of §4 apply to the weight tests. On the tie event add the true unnormalized point \(e^{\theta(X_s-u_d)}\), which converges to \(e^{\theta U}\), giving the claimed labeled fraction.

Finally, if \(\sqrt d(t_d-B_d)\to\xi\), expand \(t_dd-u_d=2d(t_d-\sqrt{t_d B_d})+O(\log d)\). Dividing by \(\sqrt{V_d}\) gives \(\xi/\sqrt{2B}+o(1)\), and \(\alpha=1\). Away from an arbitrarily small band about the zero of this standardized true score, the true unnormalized weight either tends to infinity or to zero. The limiting false total weight is positive and finite; the sign is independent of its limit by part 1. Let the band shrink to obtain the asserted full-weight mixture. This does not claim convergence of fine weight statistics at \(\theta=\alpha\).

## 6. A finite-message list obstruction

There is a high-probability set of public designs on which each wrong score has a uniformly small conditional chance to reach the extreme range. This fact does not follow merely from the one-replica annealed process. To prove it, for \(\Delta=v-s\ne0\) set
\[
 H_v(A)=\sum_{i=1}^k\sum_{j=1}^d
               \cos(2\pi(\langle A_i,\Delta\rangle_R)_j/q).
\]
For fixed odd \(q\), the image ideal \(\sum_u\Delta_u R_d\) is a direct product by coefficient interleaving of blocks from a fixed base \(d_0\). For the algebra, see [the common-law note, §3](https://github.com/mxym/math/blob/ce786bb5e0060a7574add4ea103adb7c200c0a4f/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-common-law-ambiguity.md): degrees of all odd residue factors double past a fixed base, and their unique prime-power lifts also substitute \(X^{d/d_0}\). Every image is therefore a product of \(d/d_0\) copies of a fixed base ideal. With independent rows, \(H_v\) is a sum of \(kd/d_0\) independent centered terms in \([-d_0,d_0]\). Hoeffding gives
\[
  \Pr_A(|b^2H_v|>K)\le
        2\exp[-K^2/(2d_0 k d b^4)].
\]
Here \(k d b^4=\Theta(1/d)\). Choose \(K\) a large fixed constant depending on \(B,t,q,\beta\), then union bound over the \(n_d\) wrong labels. With probability \(1-o(1)\), \(\sup_v |b^2H_v|\le K\).

Conditional on any such \(A\), the same scalar Taylor calculation within one replica, now without averaging \(A\), gives for the pair consisting of one wrong and the true score
\[
 \log E_s[e^{aX_v+cX_s}\mid A]
   =t_dd[a(a-1)+c(c+1)]+2a(1+c)b^2H_v(A)+O(d^{-1}).
\]
The expression denotes the small-factor branch of the logarithm, or equivalently the transform is the exponential of the displayed right-hand side. In particular, for bounded complex \(a,c\), the correction to the diagonal Gaussian transform is bounded in absolute value in the exponent by a fixed constant, uniformly over all \(v\) and good \(A\). After tilt at \(a=\lambda_d,c=0\), the conditional analogue of (3) has a constant bound times \(e^{-V_d\|w\|^2/2}\) in both one and two unscaled axes. The proof of the upper cube bound in §3 only needs this absolute estimate, not the \(o(1)\) error. Thus (6) holds with an enlarged constant for each \(v\) given any good \(A\), and also given \(A\) and the true tie event after division by its \(A\)-independent probability. In particular, for each fixed \(K'\),
\[
 \sup_{v\ne s}\Pr_s(X_v-u_d\ge-K'\mid A)\le C_{K'}/n_d              \tag{8}
\]
on that same design event, with or without the designated tie condition.

Now freeze the independent random tapes of the summary and readout, and the public design. The union of all candidate lists over the possible summary messages has at most \(M_d\ell_d\) labels and is fixed before the response. Equation (8) and the union bound then show that any wrong label in this union attains level \(-K'\) with probability \(o(1)\), uniformly over allowed readouts. On the other hand, the full wrong maximum is at least \(-K'\) plus any fixed margin with probability tending to one as \(K'\to\infty\) after \(d\to\infty\), by §§4–5. This proves part 4. The summary itself can be arbitrarily complicated; the bound is on the information exported to generate a short list, not the running time or the storage of a method with later access to the responses.

As a further extremal statistic, the gap between the largest and second-largest wrong scores converges to an exponential variable of rate \(\alpha\), including given the tie in part 3. Indeed mapping \(x\mapsto e^{-\alpha x}\) gives a rate-one Poisson process on \((0,\infty)\); the two smallest points are \(T_1\), \(T_1+T_2\) with independent rate-one exponentials. The limiting gap tail at \(w\ge0\) is \(E\exp[-(e^{\alpha w}-1)T_1]=e^{-\alpha w}\). Tightness of the first two ranks follows as for the maximum (on taking the lower window to \(-\infty\), the limiting count of points above it tends to infinity in probability).

## 7. Prior and scope

Exponential Poisson extrema and Poisson–Dirichlet weights are prior phenomena in the Gaussian random energy model and its hierarchies; see [Bovier–Kurkova](https://www.numdam.org/item/AIHPB_2004__40_4_439_0/). [Hao–Huang–Livshyts–Tikhomirov](https://arxiv.org/abs/1912.12833) study minimum Hamming weight of random linear codes, including the proportional-codeword multiplicity and lattice-valued extreme correction. [Concetti–Franchini](https://arxiv.org/abs/2606.07757) obtain Poisson and Poisson–Dirichlet limits for an independently thinned random linear Hamiltonian. Here the label set need not be thinned or randomly selected, there is shared public ring design rather than independent score disorder, and the proof directly gives a typical-fixed-design result and an order-one local comparison with the true score. The earlier free-energy calculation supplies a bounded-complex-parameter transform for one replica; the relative local limit, shared-design two-replica step, and weighted tail comparison are needed for the refinements here. No result on the computational accessibility of extremal labels or on a real cryptographic system is inferred.
