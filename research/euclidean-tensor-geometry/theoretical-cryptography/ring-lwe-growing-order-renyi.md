# Growing-order Rényi profiles for wrapped random ring designs

The Rényi order itself can grow on the scale of the ring dimension. In that regime, the leading log moment is controlled by the heaviest label atom rather than by Shannon entropy. We compute the limit for typical public designs and, for one fixed nonproduct covariance family, locate its finer correlation-induced displacement. The theorem concerns density moments, not statistical identification or computational time.

## 1. Model and statements

Fix an odd integer \(q\ge3\), possibly composite, dyadic \(d\to\infty\), \(\beta>0\), and \(R=(\mathbb Z/q)[X]/(X^d+1)\). Let \(b=\beta/d\) and let \(A_1,\dots,A_k\) be independent uniform public rows of \(R\), where \(k/d\to\kappa\in(0,\infty)\). Given a label \(s\in R\), observations are \(Y_i=A_is/q+E_i\) in the coefficient torus, with independent rows of wrapped Gaussian error. We study either independent scalar coordinates with periodic density \(f_b^{(1)}(y)=\sum_{h\in\mathbb Z}b^{h^2}e^{2\pi i h y}\), or the fixed nearby-coordinate covariance
\[
 C_\rho=I+\rho(U+U^\top),\qquad 0<\rho<1/2,
 \qquad f_\rho(y)=\sum_{v\in\mathbb Z^d} b^{v^\top C_\rho v}e^{2\pi i v\cdot y},
\]
where \(U\) is signed cyclic shift, \(U^d=-I\), and \(\delta=1-2\rho\). Write \(f_0=\prod_j f_b^{(1)}\) for the independent product. Let the label have an arbitrary prior \(\mu=\mu_d\), and put \(H_{\infty,d}=-\log\max_s\mu(s)\), with \(H_{\infty,d}/d\to B_\infty\). All logarithms are natural. Let \(F_{\rho,A,\mu}\) be the density of the response mixture with respect to product Haar \(\lambda\).

Let \(p=p_d>1\) be the Rényi order, with \(p/d\to z\in(0,\infty)\). Put \(\ell(x)=\log I_0(x)\), where \(I_0(x)=\int_{\mathbb T}\exp(x\cos(2\pi y))\,dy\), and \(m(x)=\ell'(x)=I_1(x)/I_0(x)\). For both noise models,
\[
 \frac1{d^2}\log\int F_{\rho,A,\mu}^{\,p}\,d\lambda
   \xrightarrow{\mathbb P_A}
       [\,\kappa\ell(2\beta z)-z B_\infty\,]_+.                  \tag{1}
\]
Thus \(D_p(P_{Y\mid A,\mu}\|\lambda)/d\) tends to \([\kappa\ell(2\beta z)/z-B_\infty]_+\). The normalized divergence can tend to zero without the divergence itself tending to zero. The same conclusions hold for the grid-average response reference instead of Haar.

There is a finer result for \(0<\delta<1/2\), that is, \(1/4<\rho<1/2\). Define the deterministic offset
\[
 a_d=k d\,\ell(2pb)-p H_{\infty,d}.
\]
If \(a_d/d^{2-\delta}\to a\in\mathbb R\), then
\[
 \frac1{d^{2-\delta}}\log\int F_{\rho,A,\mu}^{\,p}\,d\lambda
   \xrightarrow{\mathbb P_A}
 [\,a+2\kappa z\beta^{1+\delta}m(2\beta z)^2\,]_+.              \tag{2}
\]
Again the grid-average reference gives the same result. This scale is not the Shannon or total-variation transition; in particular it is not a claim about ordinary noisy inference. The proof is uniform over priors with the stated maximum-atom weight in the conditional experiment.

## 2. Four elementary preparations

**Uniform character averages.** With probability \(1-e^{-\Omega(d)}\) over \(A\), for every \(\Delta\in R\setminus\{0\}\),
\[
 \left|\frac1{kd}\sum_{i,j} e^{2\pi i(A_i\Delta)_j/q}\right|
       \le C d^{-1/2}.                                       \tag{3}
\]
Here is the needed coefficient-block argument. For fixed \(\Delta\), each \(A_i\Delta\) is uniform in the nonzero ideal \(J=\Delta R\). For sufficiently large fixed dyadic \(d_0\) depending only on \(q\), every ideal in dimension \(d=\ell_0 d_0\) is the extension of an ideal at \(d_0\) under substitution \(X\mapsto X^{\ell_0}\), and has interleaved coefficient law equal to \(\ell_0\) independent copies under its uniform distribution. Indeed the mod-\(p_0\) irreducible factor degrees for any fixed odd prime \(p_0\mid q\) are \(\operatorname{ord}_{2d}(p_0)\), linear in \(d\) with stabilized ratio along the dyadic tower. This follows from the exact order \(2d\) of every root and the 2-adic formula \(v_2(p_0^{2^j}-1)=v_2(p_0^2-1)+j-1\). The monic Hensel factors modulo each \(p_0^{e}\Vert q\) at \(d_0\) remain irreducible modulo \(p_0\) after substitution by the degree formula. In each local factor all ideals are powers of \(p_0\), since every element nonzero in the residue field is a unit and an element of least \(p_0\)-valuation generates its respective power. CRT and the direct sum \(R=\bigoplus_{a<\ell_0}X^aR_{d_0}\) give the asserted form. On each coordinate of a nonzero base ideal, values range uniformly over a nontrivial subgroup of \(\mathbb Z/q\), because signed shifts transport a nonzero projection to every coordinate. Hence every primitive coordinate phase mean is zero. The sum of the phases now has \(k\ell_0\) independent centered bounded block contributions, each of size at most \(d_0\). Apply Hoeffding to its real and imaginary parts and union over \(q^d\) choices of \(\Delta\), taking \(C\) sufficiently large for \(k/d\to\kappa>0\). This proves (3).

**Consequent event for every weighting.** Fix a good \(A\). For any probability weights \(\nu(s)\), set
\[
 M_{ij}=\sum_s\nu(s)e^{2\pi i(A_is)_j/q}.
\]
Expanding the squared modulus and using (3) gives
\[
 \left|\frac1{kd}\sum_{i,j}|M_{ij}|^2-\|\nu\|_2^2\right|
        \le C d^{-1/2}.                                      \tag{4}
\]
No union bound over weightings is needed; their coefficients \(\nu(s)\nu(t)\) sum to one.

**Two Bessel facts.** The function \(x\mapsto \ell(x)\) is strictly convex on \(x\ge0\), since its second derivative is the positive tilted variance of a cosine. For fixed \(K>0\), \(v\mapsto\ell(K\sqrt v)\) is concave and Lipschitz on \(0\le v\le2\). Indeed its derivative is \(K^2m(K\sqrt v)/(2K\sqrt v)\). The quotient \(m(x)/x\) strictly decreases: the Bessel equation gives \(m'=1-m/x-m^2\), and the sign of the quotient derivative is that of \(D(x)=x(1-m^2)-2m\). The expansion at zero is \(D=-x^3/8+O(x^5)\); at any positive zero, \(m'=m/x\) and \(D'=-2m^2<0\). Thus there is no first crossing from its negative sign near zero. The derivative has a finite limit at zero by \(m(x)=x/2+O(x^3)\). These facts are uniform for \(K\) in a compact positive interval.

**Uniform correlation expansion.** For the correlated law with fixed \(0<\rho<1/2\),
\[
 \log f_\rho(y)-\log f_0(y)
   =2b^{1+\delta}\sum_{e=(j,j+1)}
       \cos(2\pi(y_j-\sigma_e y_{j+1}))
        +o(d b^{1+\delta})                                   \tag{5}
\]
uniformly in \(y\), with \(\sigma_e=1\) except for the signed wrap edge. To prove it, use \(v^\top C_\rho v=\delta\|v\|^2+\rho\|(I+U)v\|^2\) and split a proper support into separated connected intervals. Singletons have integer-square energy. A longer connected component has energy at least \(\delta\sum v_j^2+2\rho\) by its two boundary terms. The least energy \(1+\delta\) among them is attained just by the \(2d\) signed unit edge dipoles; longer components and the other magnitudes or signs have a fixed positive gap. Their total absolute Fourier weight is \(o(d b^{1+\delta})\) by a geometric length bound; full-cycle support is negligible, and two nonsingletons cost \(O((d b^{1+\delta})^2)e^{O(db)}\). For exactly one minimal edge dipole, sum the remaining singleton components. This monomer partition differs uniformly from \(f_0(y)\) by \(O(b+db^2)=o(1)\): omit the \(O(1)\) adjacent-to-dipole sites and any other occupied neighbor pair, bounding by the total **absolute** weights of those exclusions. The independent density itself has only \(O(db^2)\) absolute Fourier weight on supports with any adjacent pair, also negligible. Thus \(f_\rho-f_0\) is \(f_0\) times the displayed dipole term plus uniform \(o(d b^{1+\delta})\). Since \(f_0\) is bounded above and below (\(\log f_b^{(1)}=O(b)\), \(db=O(1)\)), take logs to obtain (5).

## 3. Integer-order likelihood moments

First take \(p\) integer and use \(N=kd\). Expand the mixture to power \(p\) by sampling \(p\) labels independently from \(\mu\). For one tuple \((s_1,\ldots,s_p)\), write \(\nu\) for its empirical label weights and \(M_{ij}\) as in §2. The all-coordinate likelihood product in the independent model factors under the Haar integral. At coordinate \((i,j)\),
\[
 \prod_{a=1}^p f_b^{(1)}(y-(A_i s_a)_j/q)
  =\exp\!\left(2pb\operatorname{Re}
         [e^{2\pi i y}\overline M_{ij}]+O(p b^2)\right).
\]
The error is uniform in the tuple and \(y\). Thus the logarithm of its Haar integral over all coordinates is
\[
 V_0(\nu)=\sum_{i,j}\ell(2pb|M_{ij}|)+O(N p b^2).
\]
Here and below \(V_0\) denotes the log of the integral. Concavity, (4), and \(N p b^2=O(d)\) give the uniform upper bound
\[
 V_0(\nu)\le N\ell\!\left(2pb\sqrt{\|\nu\|_2^2}\right)
                +O(d^{3/2}).                                \tag{6}
\]
For one repeated label (all \(p\) equal), the log value is exactly \(N\ell(2pb)+O(d)\) uniformly, because its coordinate marginal product is translated Haar.

For the correlated model the uniform bound in (5) alone gives a change \(O(p N b^{1+\delta})=o(d^2)\). For (2) we need its leading value as a function of the tuple. Normalize the product of all shifted independent scalar densities in the tuple to a product probability law on \(y\), and let \(u_{ij}\) be its coordinate mean of \(e^{2\pi i y_{ij}}\). The scalar tilt estimate above gives
\[
 |u_{ij}|\le C|M_{ij}|+O(p b^2),
 \qquad
 u_{ij}=m(2pb)e^{2\pi i(A_i s_*)_j/q}
                    +O(\epsilon+p b^2)
 \quad\text{if }\nu(s_*)\ge1-\epsilon .                      \tag{7}
\]
For the first, the exact von Mises mean is \(m(2pb|M_{ij}|)M_{ij}/|M_{ij}|\), interpreted as zero at zero, and the bounded log-density perturbation changes any bounded expectation by \(O(p b^2)\). The normalized von Mises mean is a Lipschitz function of \(M_{ij}\) on the unit disk, by differentiating the bounded statistic in the finite-dimensional tilt family. The second then follows from \(|M_{ij}-e^{2\pi i(A_i s_*)_j/q}|\le2\epsilon\).

In the correlated integral the change after inserting (5) is a log mgf under this product probability law. Summing the displayed edge terms across the tuple, an edge contribution is bounded by \(2p b^{1+\delta}\), and depends only on its two endpoint variables. Center these terms. The cycles have even length; partition their edges into two matchings and apply Cauchy–Schwarz to their exponentiated sums. Within each matching independence and the bounded-variable exponential moment bound show that the centered log mgf is between 0 (Jensen) and \(O(N (p b^{1+\delta})^2)\). This is \(o(d^{2-\delta})\), as is the uniform error from (5). Consequently the difference \(V_\rho(\nu)-V_0(\nu)\) is the mean of the edge correction, with uniform additive \(o(d^{2-\delta})\).

For later use, this mean is bounded in absolute value by \(C p b^{1+\delta}\sum_{i,j}|u_{ij}|^2\), by the product of endpoint means and \(2|u_j u_{j+1}|\le |u_j|^2+|u_{j+1}|^2\). In particular it is \(O(p N b^{1+\delta})(\|\nu\|_2^2+O(d^{-1/2}))\) by (4) and (7). If \(\nu(s_*)\ge1-\epsilon\), (7) shows instead that the mean equals
\[
 2p N b^{1+\delta}\big(m(2pb)^2+O(\epsilon+p b^2)\big).         \tag{8}
\]
In the majority part, the mean phases cancel the shifts (on either signed edge), and the minority total weight is at most \(\epsilon\). These estimates involve the independent ***coordinate law after fixing the tuple***. They do not assume that labels or responses of the original mixture factor conditional on the design.

## 4. Occupancy comparison and the macroscopic formula

For \(0<\tau<1\) call atoms of the empirical tuple heavy if \(\nu(s)\ge\tau\). Let \(h\) be their total mass, so \(\|\nu\|_2^2\le h^2+\tau\); there are at most \(J=\lfloor1/\tau\rfloor\) heavy labels. For any given possible \(h=r/p\), the prior probability of that heavy mass is at most
\[
 \exp\{-p h H_{\infty,d}+O(J d+p\log(J+1)+p)\}.                \tag{9}
\]
For a proof, overcount choices of at most \(J\) labels by \((J+1)|R|^J\). Choose the \(r\) positions belonging to them in at most \(2^p\) ways. For every such specified set of positions their probability of drawing from the chosen labels is no more than \((J\max_s\mu(s))^r\), with no restriction on the remaining positions. This proves (9) uniformly in \(\mu\), including \(r=0\).

For fixed small \(\tau>0\), (6) and the Lipschitz Bessel bound give an upper log moment, divided by \(d^2\), at most
\[
 \sup_{0\le h\le1}\{\kappa\ell(2\beta z h)-zB_\infty h\}
                   +O(\tau)+o(1).
\]
Indeed the errors in (9) are \(O_\tau(d)\), there are only \(p+1\) possible values of \(h\), and the uniform correlation change is \(o(d^2)\). The function being optimized is convex in \(h\), with value \(0\) at zero; its maximum is the positive part of its value at one. Let \(\tau\downarrow0\). Jensen gives the lower endpoint 0. The all-equal tuple at a largest atom has probability \(\exp(-pH_{\infty,d})\) and its integral has log \(N\ell(2pb)+o(d^2)\) for either noise law, giving the other endpoint. This proves (1). It also explains why different priors with the same minimum surprisal have the same leading growing-order profile.

## 5. The first correlation correction at the crossing

Suppose \(0<\delta<1/2\) and \(a_d/d^{2-\delta}\to a\), so \(N\ell(2pb)-pH_{\infty,d}=O(d^{2-\delta})\). Choose \(\tau=d^{-v}\) with \(\delta<v<1-\delta\). Then (6), the \(\tau\) Lipschitz cost, and the counting error in (9) are all \(o(d^{2-\delta})\). In particular \(d^{3/2}=o(d^{2-\delta})\). Write
\[
 \mathcal V_d(h)=N\ell(2pb h)-p h H_{\infty,d},
\]
a convex function, so \(\mathcal V_d(h)\le h a_d\).

Fix \(0<\epsilon<1/4\). Only tuples in either the diffuse region \(h\le\epsilon\) or the concentrated region \(\max_s\nu(s)\ge1-\epsilon\) can contribute at scale \(d^{2-\delta}\). For detail, on \(\epsilon\le h\le 1-\epsilon/2\), the limiting normalized convex function has equal endpoint values zero and is strictly convex, hence is uniformly negative away from the endpoints. If \(h>1-\epsilon/2\) but the largest atom is \(<1-\epsilon\), then \(\|\nu\|_2^2\le1-\epsilon\) and \(h^2-\|\nu\|_2^2\ge\epsilon^2/4\). Thus (6) incurs a fixed negative cost of order \(d^2\) relative to \(\mathcal V_d(h)\) (the Bessel function is strictly increasing at all positive arguments); the correlation term is only \(O(d^{2-\delta})\). These excluded contributions, after (9) and summing types, are exponentially negligible at the scale in question.

For diffuse tuples, \(\|\nu\|_2^2\le\epsilon^2+\tau\), so the edge correction is \(O(\epsilon^2 d^{2-\delta})+o(d^{2-\delta})\). Also \(\mathcal V_d(h)\le h a_d\le\epsilon |a_d|\). The diffuse log upper rate at scale \(d^{2-\delta}\) is therefore \(O(\epsilon+\epsilon^2)\). In the concentrated region, \(h\ge1-\epsilon\); convexity gives \(\mathcal V_d(h)\le a_d+\epsilon |a_d|\), including when \(a_d<0\). Equation (8) supplies the correlation contribution at most \(2p N b^{1+\delta}m(2pb)^2+O(\epsilon d^{2-\delta})+o(d^{2-\delta})\). The largest of these two upper bounds, followed by \(\epsilon\downarrow0\), matches the lower bound from Jensen and the largest-atom tuple with (8) at \(\epsilon=0\). Since \(p N b^{1+\delta}/d^{2-\delta}\to \kappa z\beta^{1+\delta}\), this proves (2).

These calculations used integer order. For real \(p\), use monotonicity of the \(L^p\) norm of a nonnegative density on a probability space, between the two adjacent integer orders. The normalized first-order limit is unchanged. For the seam offset, changing \(p\) by at most one changes \(a_d\) by \(O(d)\), since \(kd\,b=O(d)\) and \(H_{\infty,d}\le d\log q\); this is negligible. Thus the second formula also extends. For the reference replacement, the grid density \(G\) has \(\|\log G\|_\infty=O(k d b^{q^2})\): keep only frequencies divisible by \(q\) in each noise row and use the same component estimate with \(b^{q^2}\). Multiplying the density moments by \(G^{1-p}\) changes their logs by \(o(1)\), since \(k,p=O(d)\) and \(q^2\ge9\).

## 6. Earlier work and boundary

[Pathegama–Barg on Rényi smoothing](https://arxiv.org/abs/2405.04406) and [Yu–Tan on Rényi resolvability](https://arxiv.org/abs/1707.00810) give the finite-order coding and resolvability framework. [Merhav, A Statistical-Physics Refinement of Soft Covering](https://arxiv.org/abs/2605.01839) analyzes phase competitions in random code partitions. Here the order grows linearly with dimension, the rare tuples are controlled conditional on a typical public ring design, and (2) gives a subleading covariance correction rather than an annealed free energy. For uniform labels, taking \(z\to\infty\) **after** the limit in (1) recovers the normalized pointwise threshold from [the order-infinity study](https://github.com/mxym/math/blob/03723207e035a4cb915d41ce2ec629859d9958d2/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-pointwise-density-transition.md), because \(\ell(2\beta z)/z\to2\beta\). The proof does not exchange these limits. The correlation effect in (2) uses an unsquared edge term under a finite von Mises tilt and is distinct from the squared contribution to the TV critical window.

The theorem is for fixed odd \(q\) and fixed \(\rho\); (2) does not cover \(\delta\ge1/2\), fluctuating covariances, or noise families from particular schemes. It concerns normalized quenched divergence only, and does not establish convergence of the ensemble mean of the unnormalized moment, a statistical decoder, or any general runtime bound.
