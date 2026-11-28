# Free energy and fixed-graph mixing obstructions in broad ring learning

Wrong-label likelihoods in a random ring design are correlated. Nevertheless their log partition sum has the leading two-branch free energy of an independent Gaussian energy model. The Gaussian freezing window also holds for the partition sum normalized by its annealed mean. These facts imply exponential worst-start mixing lower bounds for any stationary dynamics whose visible moves obey a prescribed sparse graph, even if transition probabilities can depend on the full dataset.

## 1. Model and statements

Fix an odd integer \(q\ge3\), including composite \(q\), and \(\beta>0\). Let dyadic \(d\to\infty\), \(R=(\mathbb Z/q)[X]/(X^d+1)\), and \(b=\beta/d\). Fix a deterministic set \(\mathcal S_d\subseteq R^r\) of distinct labels of size \(M_d\), with \(B_d=d^{-1}\log M_d\to B\in(0,\infty)\); the rank \(r\) need not be fixed. The set and a true label \(s=s_d\in\mathcal S_d\) are chosen before the design. With \(t_d=kb^2\to t\in(0,\infty)\), draw \(k\) independent rows \(A_i\) uniformly in \(R^r\) and observations
\[
 Y_i=\langle A_i,s\rangle_R/q+E_i\pmod{\mathbb Z^d}.
\]
The scalar coordinates of the \(E_i\) are independent with density \(f_b(y)=\sum_{h\in\mathbb Z}b^{h^2}e^{2\pi i h y}\) on the circle, a wrapped Gaussian. Set \(g_b(y)=q^{-1}\sum_{u=0}^{q-1}f_b(y-u/q)\), and let \(\nu\) be the independent-coordinate response reference with density \(g_b\) in every scalar position, independently of \(A\). Put
\[
 L_v=\frac{dP_v(Y\mid A)}{d\nu(Y)},\qquad X_v=\log L_v.
\]
Write \(\mathbb P_s,\mathbb E_s\) for the joint law of the design and responses given the true label. For fixed \(B_d,t_d\) as above, the estimates are uniform over deterministic sets of those cardinalities and all choices of true labels. This is not uniform over label sets chosen from the data.

For \(\theta\ge0\) define the sum of the wrong-label Gibbs weights \(Z_-(\theta)=\sum_{v\ne s}e^{\theta X_v}\), where sums are over \(\mathcal S_d\). Then
\[
 \frac1d\log Z_-(\theta)\xrightarrow{\mathbb P_s}
 F(B,t;\theta):=
 \begin{cases}
 B-\theta t+\theta^2t,&\theta\le\sqrt{B/t},\\
 \theta(2\sqrt{Bt}-t),&\theta\ge\sqrt{B/t}.
 \end{cases}                                                       \tag{1}
\]
Also \(X_s/d\to t\). The per-dimension Shannon entropy of the normalized wrong-label weights tends to \((B-\theta^2t)_+\) at each fixed \(\theta>0\), including at \(\sqrt{B/t}\).

The normalization can be made much finer at the freezing boundary. If \(\theta_d>0\), \(\sqrt d(\theta_d^2t_d-B_d)\to\xi\in\mathbb R\), then
\[
 \frac{Z_-(\theta_d)}
 {\exp\{d[B_d+t_d(\theta_d^2-\theta_d)]\}}
       \xrightarrow{\mathbb P_s}\Phi\!\left(-\frac{\xi}{\sqrt{2B}}\right),
 \qquad
 \mathbb E_s\frac{Z_-(\theta_d)}
 {\exp\{d[B_d+t_d(\theta_d^2-\theta_d)]\}}\to1.                       \tag{2}
\]
Here \(\Phi\) is the standard normal CDF; the two limits in (2) deliberately differ. At a fixed subcritical temperature \(\theta^2t<B\) the same normalized sum tends to 1 in \(L^1\). At a fixed supercritical temperature it tends to 0 in probability, with log exponent \(-(\theta\sqrt t-\sqrt B)^2\), but its mean still tends to 1.

**Mixing consequence.** Fix \(\theta>0\) and the target law \(\pi_\theta(v)\propto e^{\theta X_v}\). A graph sequence on the label sets is prescribed independently of the data, with maximum incoming degree excluding self-loops at most \(\exp\{(\kappa+o(1))d\}\), \(0\le\kappa\le B\). On an event of probability \(1-o(1)\), the ordinary worst-start \(1/4\) TV mixing time of **every** chain stationary for \(\pi_\theta\) with transitions supported on that graph is at least \(\exp((\gamma-o(1))d)\) if
\[
 \gamma=\min\{\theta t,F(B,t;\theta)\}-F(\kappa,t;\theta)>0.           \tag{3}
\]
Use \(F(0,t;\theta)=-\theta t\). The notation for this high-probability assertion means that one may subtract any fixed positive number from \(\gamma\), or some deterministic \(o(1)\) along a fixed sequence. The transition probabilities themselves need not be prescribed and may depend on the data; detailed balance is not required. The same stationary-flux argument holds for a finite auxiliary state when its equilibrium visible marginal is \(\pi_\theta\) and the visible transitions obey the graph, with TV measured on the visible marginal from a worst auxiliary state. At the posterior temperature \(\theta=1\), and a subexponential graph, the explicit lower exponents are \(2t\) for \(t\le B\) and \(2\sqrt{Bt}\) for \(t\ge B\). For \(0<\kappa<\min(t,B)\) the corresponding exponents are reduced by \(2\sqrt{\kappa t}\).

These are statements about stationary sampling restrictions, not the existence or running time of general classical search algorithms.

## 2. Uniform multivariate moments

The key estimate is the following for any fixed \(m\), distinct labels \(v_1,\dots,v_m\ne s\), and real or complex \(a_j\) in a fixed bounded set:
\[
 \mathbb E_s \exp\!\left(\sum_{j=1}^m a_j X_{v_j}\right)=
 \exp\!\left\{t_d d\sum_{j=1}^m a_j(a_j-1)+O(d^{-1})\right\}.        \tag{4}
\]
The error is uniform over those labels, over \(s\), rank, and bounded \(a_j\). The exponential error notation is also valid for complex arguments. It is a finite-tuple transform estimate, not a joint independence assertion for exponentially many labels.

For a nonzero \(\Delta\in R^r\), the random \(\langle A_i,\Delta\rangle_R\) is uniform on the nonzero ideal \(I=\sum_j\Delta_jR\). Its coefficient-dot annihilator \(I^\perp\) is a proper ideal: multiplication by \(c(X)\) is adjoint for the coefficient dot product to multiplication by \(c(X^{-1})\), and the pairing is nondegenerate. It contains no signed monomial or signed binomial at distinct positions. In each residue field of \(R\), the image of \(X\) has exact order \(2d\), since \(X^d=-1\) and the characteristic is odd. Thus every such monomial or binomial is a unit even for composite \(q\). It follows that, for \(V\sim U_I\), every \(\cos(2\pi V_j/q)\) has mean zero, variance \(1/2\), and distinct positions are orthogonal. The variance statement also uses that \(2X^j\) is a unit; the cross statement uses the cosine product identity. In particular the coefficient sum of cosines for each individual nonzero difference has variance \(d/2\). No independence between different differences is needed.

Use the joint reference \(A,\nu\), multiplying its density by \(L_s\) for the planted law in (4). At one coordinate of one row, hold the grid displacements \(z_j\) of each relevant label fixed, and include index \(0\) for \(s\) with \(a_0=1\). Let \(\lambda_b=f_b/g_b\). Uniformly in these shifts, by Taylor expansion and circle integration,
\[
 \int g_b(y)\prod_{j=0}^{m}\lambda_b(y-z_j)^{a_j}\,dy
 =1+b^2\left[C_a+2\sum_{p<j}a_p a_j\cos(2\pi(z_p-z_j))\right]
      +O(b^4),
 \qquad C_a=\sum_{j=0}^m a_j(a_j-1).                               \tag{5}
\]
Indeed \(\lambda_b(y)=1+2b\cos(2\pi y)+O(b^4)\), \(g_b=1+O(b^{q^2})\), and odd-order terms in the cosine expansion integrate to zero by a half-period shift of \(y\). The scalar likelihood is positive and uniformly close to 1, so complex powers are defined by its real logarithm. The coefficients in (5) are from the individual quadratic terms and the cross cosine terms.

For the product in a row, take logarithms close to 1 and sum (5) over the coordinates. The resulting expression is \(\exp\{b^2(d C_a+H)+O(db^4)\}\), where \(H\) is the sum of the weighted cosine differences across coordinates. Each difference is nonzero. The ideal calculation gives \(\mathbb E_A H=0\) and \(\mathbb E_A|H|^2=O(d)\) by Cauchy–Schwarz over the finitely many pairs. Also \(|H|=O(d)\). Hence \(\mathbb E_A e^{b^2H}=1+O(db^4)\), by the second-order remainder bound with \(b^2|H|=O(d^{-1})\). Thus the row average is \(\exp\{db^2 C_a+O(db^4)\}\). Rows are independent and \(kdb^4=O(d^{-1})\). Since \(a_0(a_0-1)=0\), this proves (4). The same proof can omit index 0 for the unplanted reference, although only the planted law is needed below. For the true score, the scalar expansion or the transform with the sole exponent \(1+a\) gives mean \(t_dd+O(d^{-1})\) and variance \(2t_dd+O(d^{-1})\); equivalently these follow from independent true residuals.

## 3. From shell counts to the quenched free energy

For fixed \(x\ge-t\) put \(I_t(x)=(x+t)^2/(4t)\). By (4), Chernoff uniformly bounds the one-label upper tail at level \(dx\) by \(\exp\{-d I_t(x)+o(d)\}\) and a two-distinct-label upper tail at that level by \(\exp\{-2d I_t(x)+o(d)\}\). The one-label probability for a band \([dx,d(x+\delta)]\), with fixed \(\delta>0\), has the matching log lower rate \(-I_t(x)\). For detail, choose \(x'\) strictly inside the band and tilt by \(a=(x'+t)/(2t)\). Equation (4) at \(a\pm h\) shows exponentially strong concentration of \(X_v/d\) at \(x'\) under that tilt, by sufficiently small fixed \(h\). Untilt on an arbitrarily small interval about \(x'\) and let \(x'\downarrow x\). This also proves the endpoint claim \(x=-t\) with rate zero.

There are \(e^{(B+o(1))d}\) false labels. An upper first-moment bound on counts at finitely many levels gives the upper half of
\[
 \frac1d\log Z_-(\theta)\ \longrightarrow\
 \max_{-t\le x\le 2\sqrt{Bt}-t}
      \{B-I_t(x)+\theta x\}.                                    \tag{6}
\]
Here are the details of the upper discretization. With high probability there is no score above \(d(2\sqrt{Bt}-t+\delta)\) by the union bound. Scores below \(-td\) contribute at most \(M_de^{-\theta td}\), the contribution of the left endpoint. On a fixed mesh of width at most \(\delta\) between \(-t\) and the right endpoint, the number above a left endpoint \(x\) is at most \(e^{d(B-I_t(x)+\epsilon)}\) with probability \(1-o(1)\), using a fixed \(\epsilon>0\). The last bin can extend to the no-score level. Charge each bin its maximum weight. This gives the upper formula on letting \(\epsilon,\delta\) decrease. The same upper proof applied to any prescribed subset of wrong labels of cardinality at most \(e^{(\kappa+o(1))d}\) gives the upper bound with \(B\) replaced by \(\kappa\), including \(\kappa=0\) for which just the union bound at \(x=-t+\delta\) suffices.

For the lower bound inside the interval, with \(I_t(x)<B\), let \(N\) count scores in \([dx,d(x+\delta)]\). Then \(\mathbb E_s N=\exp\{d(B-I_t(x)+o(1))\}\); the pair bound and diagonal yield \(\mathbb E_sN^2/(\mathbb E_s N)^2\le\exp(o(d))\). Paley–Zygmund proves that \(N\ge\mathbb E_s N/2\) on an event of probability at least \(\exp(-o(d))\). Thus on an event of this probability the lower exponent in (6) is at least \(B-I_t(x)+\theta x-o(1)\). It remains to upgrade this event to high probability. The two-moment count estimate alone is not enough.

Let \(G=\log Z_-(\theta)\), a function of the independent rows \((A_i,E_i)\) conditional on \(s\). Denote the score in row \(i\) for label \(v\) by \(\ell_{i,v}\). Uniformly and deterministically \(|\ell_{i,v}|\le Cdb=O(1)\). Also
\[
 \sup_{i,v,A_i}\mathbb E_s[\ell_{i,v}^2\mid A_i]=O(d^{-1}).        \tag{7}
\]
In fact conditional on \(A_i\) its scalar terms are independent, each with variance \(O(b^2)\) and mean \(O(b^2)\): \(E_{i,j}\sim f_b\) gives any shifted first cosine mean at most \(b\) in magnitude, and the remaining log Taylor terms are \(O(b^2)\). This gives \(O(db^2+d^2b^4)\) as claimed.

Delete row \(i\) in the sum defining \(G\), giving \(G_{-i}\). Conditional on all other rows, the normalized wrong-label weights \(\mu_{-i}\) are fixed and
\[
 G-G_{-i}=\log \sum_v\mu_{-i}(v)e^{\theta\ell_{i,v}}.
\]
This is uniformly bounded in absolute value. Its conditional second moment is \(O(d^{-1})\): on the bounded range of the exponentials, the log is Lipschitz, and Cauchy–Schwarz gives the square bound \(C_\theta\sum_v\mu_{-i}(v)\ell_{i,v}^2\). For the Doob martingale revealing successive rows, the increment at row \(i\) is the difference between the conditional means of \(G-G_{-i}\) before and after seeing that row, because \(G_{-i}\) is independent of row \(i\). Thus increments are bounded, and conditional variance at each step is \(O(d^{-1})\) by Jensen and (7). The conditional mgf for a centered increment at real \(h\) with \(|h|\le1\) is at most \(\exp(C h^2/d)\) by Taylor remainder on its bounded support. Multiplication over \(k=O(d^2)\) increments and Chernoff imply, for every fixed \(\epsilon>0\),
\[
 \mathbb P_s(|G-\mathbb E_sG|>\epsilon d)\le 2e^{-c_\epsilon d}.   \tag{8}
\]
A lower event of probability \(\exp(-o(d))\) at an exponent \(g_0-o(1)\) forces \(\liminf_d\mathbb E_sG/d\ge g_0\); otherwise (8) contradicts it. Equation (8) then also forces the same lower exponent in probability. Approximate the right endpoint from inside \(I_t(x)<B\), optimizing over \(x\). This proves (6). Its optimizer is \(\min(2\theta t-t,\,2\sqrt{Bt}-t)\), yielding (1). Convexity of \(G/d\) as a function of \(\theta\) sandwiches its derivative between difference quotients at two fixed offsets. The limit in (1) is differentiable even at the boundary, so \(G'(\theta)/d\to\partial_\theta F\) in probability. Using entropy \(G-\theta G'\) gives the stated entropy limit. These arguments do not require independence of the indicators making up the shell count.

## 4. Critical normalization of the false partition sum

Define \(D_v=\theta_dX_v-d t_d(\theta_d^2-\theta_d)\) and \(V_v=e^{D_v}\), so that the normalized sum in (2) is \(M_d^{-1}\sum_{v\ne s}V_v\). In the window of (2), \(\theta_d\to \sqrt{B/t}>0\). Equation (4) shows uniformly \(\mathbb E_s V_v=1+O(d^{-1})\) and \(\mathbb E_s V_v V_w=1+O(d^{-1})\) for \(v\ne w\). Under the probability tilt of the planted law proportional to \(V_v\), the standardized \(D_v\), centered at \(\theta_d^2 t_d d\) and scaled by \(\theta_d\sqrt{2t_dd}\), tends to standard normal. Under the tilt by \(V_vV_w\) the two standardized variables tend to independent standard normals. To see this, apply (4) at \(\theta_d+iu/\sqrt{2t_dd}\), or at two such arguments. The centering cancels its linear imaginary term and the quadratic term gives \(e^{-u^2/2}\) for each coordinate. The uniform transform error tends to zero. Uniform convergence of the relevant CDFs follows by applying the characteristic-function argument to arbitrary sequences of distinct labels and using continuity of the limit.

Choose \(h_d\to\infty\), \(h_d=o(\sqrt d)\), and retain \(U_v=V_v\mathbf1_{\{D_v\le\log M_d-h_d\}}\). The one-label tilted limit gives \(\mathbb E_s U_v\to m=\Phi(-\xi/\sqrt{2B})\) uniformly, because the standardized cutoff tends to \(-\xi/\sqrt{2B}\). The pair tilt similarly gives \(\mathbb E_s U_vU_w\to m^2\) uniformly for \(v\ne w\). The diagonal cost in the second moment of the average is at most \(e^{-h_d}M_d^{-1}\sum_v\mathbb E_s U_v\), so \(M_d^{-1}\sum U_v\to m\) in \(L^2\). The middle range \(\log M_d-h_d<D_v\le\log M_d+h_d\) has vanishing expected contribution to the average by the one-label tilted limit and continuity. With probability \(1-o(1)\) no \(D_v\) is above \(\log M_d+h_d\), by Markov on \(V_v\) and a union bound with total \(O(e^{-h_d})\). This proves convergence in probability. The expectation of the untrimmed average tends to 1 by (4), so the critical convergence is not in \(L^1\).

For a fixed subcritical \(\theta\), the same argument for the retained part has \(m=1\) because the standardized threshold tends to \(+\infty\); the expected omitted mass tends to zero. Fixed supercritical \(\theta\) is covered by (1) and its normalizing exponent. In particular at \(\theta=1\), if \(\sqrt d(t_d-B_d)\to\xi\), the ratio \(Z_-(1)/M_d\) tends in probability to the constant in (2). Combining this with the true-score CLT gives the random posterior mass of \(s\) converging **in distribution** to a Bernoulli variable of success probability \(\Phi(\xi/\sqrt{2B})\): \((X_s-\log Z_-(1))/\sqrt d\) converges to \(N(\xi,2B)\), and the posterior mass is the logistic of the unscaled log-odds. This does not claim that the incorrectly labeled weight sum is close to its mean in this window.

## 5. Stationary bottleneck for an arbitrary fixed move graph

Given the data, write \(Z=e^{\theta X_s}+Z_-(\theta)\) and \(C\) for the set of incoming neighbors of \(s\) excluding \(s\). In stationarity, the one-step probability of entering \(\{s\}\) from outside is at most \(\pi_\theta(C)\). The probability of the reverse crossing is equal by stationarity of the mass of \(\{s\}\). This is valid on an extended state space by using the event that the visible label is \(s\); the incoming probability is still bounded by its stationary marginal on \(C\). By the subset upper bound in §3,
\[
 \pi_\theta(C)\le Z^{-1}\exp\{d[F(\kappa,t;\theta)+o_{\mathbb P_s}(1)]\}.
\]
Meanwhile the smaller stationary mass of \(\{s\}\) and its complement is \(Z^{-1}\exp\{d[\min(\theta t,F(B,t;\theta))+o_{\mathbb P_s}(1)]\}\) by (1). Let \(D\) denote that smaller side. If the chain starts in its stationary law conditioned on \(D\), its probability of having left \(D\) by step \(n\) is at most \(n\) times the stationary crossing probability divided by \(\pi_\theta(D)\). This follows by a union bound on crossing times in a run started at stationarity, followed by conditioning on its initial state lying in \(D\). Hence distance to stationarity at step \(n\) is at least \(1/2-n \exp\{d[-\gamma+o_{\mathbb P_s}(1)]\}\), using just the visible event \(D\). A mixture of starts cannot have larger TV than the worst single start. This proves (3), on a data event which depends on the graph but not any transition probabilities. It also permits a time-dependent sequence of kernels if the same joint law is stationary for each kernel and each step obeys the same graph, with the sequence fixed once the data are fixed.

For a fixed symmetric proposal graph of subexponential degree with total proposed mass away from \(s\) at least \(e^{-o(d)}\), the stationary flow of the standard Metropolis dynamics has this exact smaller-side cut exponent. Indeed all proposed neighbors have \(X_v/d=-t+o_{\mathbb P_s}(1)\) uniformly by the two one-sided Chernoff bounds from (4) and the subexponential union, whereas \(X_s/d=t+o_{\mathbb P_s}(1)\). Each distinct crossing contributes its proposed probability times \(e^{\theta X_v}/Z\). This verifies sharpness for this cut, not a matching mixing-time upper bound. Nor is this a warm-start guarantee: the smaller side can have exponentially small stationary mass.

## 6. Prior work and scope

[Merhav, Relations Between Random Coding Exponents and the Statistical Physics of Random Codes](https://arxiv.org/pdf/0708.0850), esp. §2.2 and footnote 3, gives the wrong-codeword partition sum and the high-temperature and frozen phase picture in independent random codes; that picture and the variational maximization are not new. Here the label codewords use the *same* random ring rows. No independent codeword count is invoked. The different mathematical input is the short-unit Fourier cancellation in (4), bounded-variance row martingale, and the uniform pair tilt under the actual planted law. [Levin–Peres–Wilmer, Markov Chains and Mixing Times](https://pages.uoregon.edu/dlevin/MARKOV/) gives the classical stationary bottleneck lower bound; the work here is the random-data bound on stationary flow that applies simultaneously to all kernels supported on a prescribed graph.

[Prior posterior-surprisal and coarsening note](https://github.com/mxym/math/blob/15a25c0d1d01551372cfb03794958adc753ca3b6/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-posterior-surprisal-coarsenings.md) described true-value posterior surprisal and marginal TV at unit temperature. It did not give the wrong-label log partition curve, normalization at the freezing line, or any stationary graph mixing consequence. In particular a typical finite-tuple limit does not imply the free energy: the row concentration in (8) is used after the shell second moment. This is an abstract continuous broad-noise model. No data-selected move graph, unrestricted search or time lower bound, efficient estimator, or deployed parameter statement is implied.
