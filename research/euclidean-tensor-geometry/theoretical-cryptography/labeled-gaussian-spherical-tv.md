# The cost of replacing labeled Gaussian covariance by a fixed law

Albrecht, Felderhoff, Lai, Lapiha and Woo's Gaussian leftover hash analysis over number fields produces an output Gaussian whose covariance depends on the realized matrix. Their §6 asks about replacing it by a single spherical distribution in negligible statistical distance. In a Gaussian matrix model the replacement has a precise total-variation cost, even if the candidate fixed output need not be Gaussian. We also pass this result to sufficiently broad discrete Gaussians in the dyadic cyclotomic ring.

## 1. Gaussian matrix model and statement

Let \(p,r,m\) be positive integers. Independently in \(p\) blocks draw \(G_j\in\mathbb C^{r\times m}\) with independent standard complex normal entries, meaning densities \(\pi^{-1}e^{-|z|^2}\). Set \(W_j=G_jG_j^*/m\). Given the label \(G=(G_j)_j\), let \(P_G\) be the product of the centered complex normal laws with covariance matrices \(W_j\); a singular matrix gives a possibly singular Gaussian. The covariance convention is \(\mathbb E YY^*=W_j\). Write \(Q_0\) for the standard complex Gaussian on \(\mathbb C^{pr}\) and put
\[
  v=\frac{p r^2}{m},\qquad
  \Delta=\inf_Q \mathbb E_G\,d_{\rm TV}(P_G,Q).
\]
Here \(Q\) is any fixed probability on this space, independent of \(G\), and may change with \(p,r,m\). The distance inside the infimum is also the joint TV with the label retained on both sides.

Assume \(pr\to\infty\), \(m\to\infty\). Define \(g(v)=2\Phi(\sqrt v/2)-1\) for standard real Gaussian CDF \(\Phi\). Then
\[
\begin{array}{ll}
 v\to v_0\in(0,\infty):&
 \Delta\longrightarrow g(v_0),\quad
 \mathbb E_G\,d_{\rm TV}(P_G,Q_0)\longrightarrow g(v_0);\\[2mm]
 v\to0:&
 \Delta\sim\mathbb E_G\,d_{\rm TV}(P_G,Q_0)
      \sim\sqrt{v/(2\pi)};\\[2mm]
 v\to\infty:& \Delta\longrightarrow1.
\end{array}                                                     \tag{1}
\]
Thus an optimized, possibly non-Gaussian fixed law cannot remove even the first-order error. In the first two lines the distance to \(Q_0\) also converges in probability to its stated limit, or relative to its stated first-order equivalent when \(v\to0\). The model retains the matrix label: the marginal with the label forgotten is a different problem.

## 2. Matrix estimates

Write \(E_j=W_j-I\), \(F=\sum_j\operatorname{tr}E_j^2\), and \(\eta=\max_j\|E_j\|_{\rm op}\). For a standard complex column \(g\), set \(Z=gg^*-I\). On the real vector space of Hermitian matrices, \(\mathbb E\operatorname{tr}(ZA)\operatorname{tr}(ZB)=\operatorname{tr}(AB)\); diagonalize \(A=B\) for its variance identity and polarize. Also, with \(S=\|g\|^2\sim\operatorname{Gamma}(r,1)\), \(\|Z\|_F^2=S^2-2S+r\), with mean \(r^2\) and variance \(4r^3+2r^2+2r\). Expanding \(E_j=m^{-1}\sum_a Z_{j,a}\), the diagonal terms and all distinct unordered cross terms in its squared Frobenius norm have zero pairwise covariance, by centering conditional on a shared column. The cross term \(\operatorname{tr}(Z_{j,a}Z_{j,b})\) has variance \(r^2\) by isotropy on the \(r^2\)-dimensional Hermitian space. Consequently
\[
 \mathbb E F=v,\qquad
 \operatorname{Var} F=
 \frac{p(4r^3+2r^2+2r+2(m-1)r^2)}{m^3},\qquad
 F/v\longrightarrow1\text{ in probability}.                   \tag{2}
\]
For \(v=O(1)\), \(r+\log(p+1)=o(m)\). A fixed unit vector sees \(m\) independent exponential energies with mean 1, whose average has tails at most \(2e^{-c m u^2}\) for \(0<u<1\) by its moment generating function. Use a \(1/4\)-net of the real sphere of dimension \(2r\), of size at most \(9^{2r}\), and \(\|E\|_{\rm op}\le2\max_{u\ {\rm in\ net}}|u^*Eu|\). A union bound gives
\[
 \eta=O_{\mathbb P}\left(\sqrt{\frac{r+\log(p+1)}m}\right)
       =o_{\mathbb P}(\sqrt v),\qquad \eta=o_{\mathbb P}(1).       \tag{3}
\]

## 3. The likelihood with the output held fixed

When \(v=O(1)\), eventually \(m\ge r\), and all \(W_j\) are positive definite almost surely. Use the reference experiment in which \(G\) has its usual law and \(Y\sim Q_0\) is independent. Let \(R=dP_G/dQ_0(Y)\), \(L=\log R\), \(B_j=Y_jY_j^*-I\). On \(\eta\le1/2\), the log-determinant and inverse power series give
\[
 L=A-\tfrac12 F-(T-F)+\mathcal E,\qquad
 A=\sum_j\operatorname{tr}(E_j B_j),\quad T=\sum_jY_j^*E_j^2 Y_j,\quad
 |\mathcal E|\le C\eta(F+T).                                    \tag{4}
\]
Conditional on \(G\), \(T\) has mean \(F\) and variance \(\sum_j\operatorname{tr}E_j^4\le\eta^2F\). For \(v\to v_0>0\), this shows \(T-F=o_{\mathbb P}(1)\) and \(\mathcal E=o_{\mathbb P}(1)\); for \(v\to0\), \(F,T=O_{\mathbb P}(v)\), so all terms after \(A\) are \(o_{\mathbb P}(\sqrt v)\).

Now condition on \(Y\), not on \(G\). The variable \(A\) is a sum of independent centered terms \(\operatorname{tr}(Z_{j,a}B_j)/m\) with total variance
\[
 V_Y=\frac1m\sum_j\operatorname{tr}B_j^2,\qquad V_Y/v\longrightarrow1
 \quad\text{in probability};
\]
this follows from the same gamma mean and variance as above. The third absolute moment of \(\operatorname{tr}(Z B)\) is at most \(C(\operatorname{tr}B^2)^{3/2}\): diagonalize \(B\), use the fourth moment of a linear combination of independent centered unit exponentials, then Hölder. Since \(\mathbb E(\operatorname{tr}B_j^2)^{3/2}=O(r^3)\), the expected sum of these third moments after normalization by \(\sqrt v\) is at most
\[
 C\,\frac{p r^3}{m^2 v^{3/2}}=\frac{C}{\sqrt{pm}}\longrightarrow0.
\]
The conditional Lyapunov or Berry–Esseen bound, with \(V_Y/v\to1\), therefore gives convergence of the conditional law of \(A/\sqrt v\) to the standard normal in probability over \(Y\). Equivalently, this holds for conditional integrals of bounded Lipschitz functions. The errors in (4) also tend to zero at their stated scales conditionally in probability over \(Y\): for each positive cutoff, the mean over \(Y\) of the conditional probability of exceeding it tends to zero by the joint estimate. Thus conditionally on \(Y\), in probability,
\[
 \begin{cases}
 R\ \Rightarrow\ S_{v_0}:=\exp(\sqrt{v_0}Z-v_0/2), & v\to v_0>0,\\
 (R-1)/\sqrt v\ \Rightarrow\ Z, & v\to0,
 \end{cases}                                                   \tag{5}
\]
where \(Z\) is a standard real normal. The exponential transformation uses tightness of the appropriate conditional log-likelihood and, in the second case, the derivative of the exponential at zero.

## 4. Optimizing over all independent targets

In the bounded positive window, the nonnegative variable \(R\) has mean 1 for each \(p,r,m\) and converges in distribution under the reference experiment to \(S_{v_0}\) of mean 1. Hence \(R\) is uniformly integrable. Let \(q=dQ_{\rm ac}/dQ_0\), allowing singular mass so \(\mathbb E_{Q_0}q\le1\). The overlap with \(Q\) in the joint experiment is
\[
        \mathbb E_Y\,\mathbb E_G\min(R,q(Y)).
\]
Equation (5) implies that, in mean over \(Y\), \(\mathbb E_G\min(R,z)\) is uniformly approximated for all \(z\ge0\) by \(b(z)=\mathbb E\min(S_{v_0},z)\). Indeed first clip both random variables at a large \(K\), costing at most their integrable tails; then the functions of \(z\) are 1-Lipschitz and constant for \(z\ge K\), so a finite mesh and conditional convergence for each bounded continuous integrand suffice. Thus the overlap is at most \(o(1)+\mathbb E_Y b(q(Y))\le o(1)+b(1)\), uniformly in \(Q\), since \(b\) is concave and increasing. Equality to first order is obtained by \(Q_0\). Finally \(1-b(1)=2\Phi(\sqrt{v_0}/2)-1\) by integrating the two halves of the log-normal overlap, splitting at \(Z=\sqrt{v_0}/2\).

For \(v\to0\), write \(U=(R-1)/\sqrt v\). To prove its uniform integrability, restrict first to \(F\le1/4\), where all eigenvalues \(a\) of all \(E_j\) satisfy \(|a|\le1/2\). Complex scalar integration yields
\[
 \mathbb E_{Q_0}(R^2\mid G)=\prod_a (1-a^2)^{-1},
 \qquad \mathbb E_{Q_0}[(R-1)^2\mid G]\le C F\quad(F\le1/4).
\]
Integrating and using (2) bounds the second moment of \(U\) on this event. The complement has \(G\)-probability at most \(4v\); on it \(\mathbb E_{Q_0}(|R-1|\mid G)\le2\), so its contribution to the first absolute moment of \(U\) is \(O(\sqrt v)\). This proves uniform integrability.

For any \(Q\), set \(c(Y)=(q(Y)-1)/\sqrt v\). Twice its TV cost divided by \(\sqrt v\) is at least \(\mathbb E_Y\mathbb E_G|U-c(Y)|\) (the singular part contributes nonnegatively). By (5) and uniform integrability,
\[
 \mathbb E_Y\sup_{c\in\mathbb R}
 \left|\mathbb E_G[|U-c|-|c|\mid Y]-\mathbb E[|Z-c|-|c|]\right|
 \longrightarrow 0 .
\]
Indeed the displayed functions of the integration variable are uniformly 1-Lipschitz and bounded by its absolute value. Clip the integration variable to a compact interval, use a finite uniform net of such Lipschitz functions on it, then send the clipping cutoff to infinity using uniform integrability. The expectation \(\mathbb E|Z-c|\) is minimized at \(c=0\), with value \(\sqrt{2/\pi}\). This gives the lower bound uniformly over all \(Q\), and \(Q_0\) attains the first-order value by the same convergence for \(c=0\).

For \(v\to\infty\), fix any \(a>0\) and project both the label and the output to \(p'\le p\) blocks and \(r'\le r\) rows in each. Along any subsequence pass to a further one where \(p/m\) tends to a value in \([0,\infty]\). If the limit is zero, take \(p'=p\), \(r'=\lfloor\sqrt{a m/p}\rfloor\), eventually at most \(r\). If the limit is positive, choose a fixed \(r'\le r\) with \(a/(r')^2\) strictly below that limit and \(p'=\lfloor a m/(r')^2\rfloor\); for an infinite limit use \(r'=1\). When the limit is positive and finite, \(r\to\infty\) since \(v\to\infty\). In all cases \(p'r'\to\infty\) and \(p'(r')^2/m\to a\). The projected target remains independent of the projected label. By data processing and the positive finite case, \(\liminf\Delta\ge g(a)\); take \(a\to\infty\).

### Typical labels and a uniform lower bound

For completeness, if \(v=O(1)\), condition instead on \(G\) in (4) and diagonalize the \(E_j\). Then \(A\) is a sum of independent centered exponential terms with coefficients the eigenvalues of the \(E_j\), variance \(F\) and largest coefficient \(o_{\mathbb P}(\sqrt F)\) by (2)–(3). The same normal limit, its corrections from (4), and the second-moment calculation when \(v\to0\) give the claimed convergence in probability for the conditional distance to \(Q_0\). For \(v\to v_0>0\) use the bounded overlap integrand \(\min(1,R)\); for \(v\to0\) use the second-moment bound to pass the conditional normalized absolute value to its expectation.

In fact there is a lower bound in probability uniform over every independent \(Q\). With two independent labels \(G,G'\), \(\sum_j\operatorname{tr}(E_jE'_j)\) is centered with variance \(pr^2/m^2\), by the Hermitian covariance identity. Thus \(\sum_j\|W_j-W'_j\|_F^2\sim 2v\) in probability. Whitening by \((W'_j)^{-1/2}\) changes Frobenius norms by \(1+o_{\mathbb P}(1)\) uniformly; the largest resulting relative eigenvalue is still \(o_{\mathbb P}(\sqrt v)\). The preceding deterministic conditional Gaussian calculation then gives \(d_{\rm TV}(P_G,P_{G'})\to g(2v_0)\) if \(v\to v_0>0\), and \(d_{\rm TV}(P_G,P_{G'})/\sqrt v\to1/\sqrt\pi\) if \(v\to0\), in probability. For any threshold \(u\ge0\),
\[
  \Pr_G[d_{\rm TV}(P_G,Q)<u]^2
    \le \Pr_{G,G'}[d_{\rm TV}(P_G,P_{G'})<2u].
\]
For example, if \(v\to0\) the probability that any given fixed \(Q\) has error below \(c\sqrt v\) tends to zero uniformly over \(Q\), for any \(c<1/(2\sqrt\pi)\). This is not a simultaneous statement about selecting \(Q\) after seeing the label.

## 5. A broad discrete dyadic transfer

Let \(d\ge2\) be a power of two, \(p=d/2\), \(N=dr\), and \(R_d=\mathbb Z[X]/(X^d+1)\). Choose one evaluation \(\sigma_j\) from each conjugate pair of roots, and write \(\Psi(a)=(\sigma_j(a)/\sqrt d)_{j=1}^p\), extended entrywise. The finite Fourier identity \(\sum_j|\Psi(a)_j|^2=\tfrac12\|a\|_{\rm coeff}^2\) for real coefficients shows that \(\Psi\) is a scaled real isometry and sends a unit-coefficient normal to independent standard complex normals.

Take a labeled \(r\times m\) matrix \(X\) over \(R_d\) whose coefficients are independent with masses proportional to \(e^{-k^2/(2s^2)}\), \(k\in\mathbb Z\). Define \(\widehat G_j=(\sigma_j(X_{ab})/(s\sqrt d))_{a,b}\), \(\widehat W_j=\widehat G_j\widehat G_j^*/m\). For a mesh \(h>0\), on the deterministic lattice \(h\Psi(R_d^r)\) compare the conditional discrete Gaussian with mass proportional to
\[
    \exp\!\left(-\sum_j y_j^*\widehat W_j^{-1}y_j\right)
\]
to an arbitrary fixed probability on the same lattice, independent of \(X\). For singular labels any fallback law on that lattice is allowed. Assume \(pr\to\infty\), \(v=O(1)\), and
\[
       Nm/s+Nh=o(\min(1,\sqrt v)).                              \tag{6}
\]
Then the first two lines of (1) hold for the optimal average TV here as well, with the fixed spherical discrete Gaussian on that lattice an asymptotically optimal candidate. These are broad-width sufficient assumptions, not claimed necessary for this discrete transfer.

Here are the details of the approximation. For an ordinary real normal density \(f\) in dimension \(D\) whose covariance eigenvalues are bounded above and below by constants, let \(x_h\) be the nearest point on an orthogonal mesh \(h\), using its cubes. Uniformly jittering one sample of its discretized mass proportional to \(f(x_h)\) in its cube gives density \(f(x_h)/M\), where \(M=\int f(x_h)\,dx\). If \(hD\) is small then
\[
 \int|f(x_h)-f(x)|\,dx=O(hD).
\]
In fact \(|\log(f(x_h)/f(x))|\le C(h\sqrt D\,\|x\|+h^2D)\). Under \(f\), use \(|e^u-1|\le |u|e^{|u|}\); on putting \(t=C h\sqrt D\), the bound \(\mathbb E[\|X\|e^{t\|X\|}]=O(\sqrt D)\) when \(t\sqrt D=O(1)\) follows by Cauchy–Schwarz and the Gaussian squared-norm moment generating function. For example \(t\|X\|\le c\|X\|^2/D+C'(t\sqrt D)^2\) for sufficiently small fixed \(c\). Normalizing \(M\) changes the \(L^1\) error by at most \(|M-1|\). In particular rounding a continuous normal to its cube center approximates the prescribed discrete Gaussian within \(O(hD)\). The same reasoning holds for the above scaled real isometry and complex density convention.

Use this estimate for the \(Nm\) real seed coefficients and mesh \(1/s\). Replacing the discrete seed by the rounded continuous seed changes any joint comparison by \(O(Nm/s)\). Under this coupling write \(\widehat G\) for the blocks from rounding, and \(G\) for the continuous blocks before rounding, with independent standard complex entries. The sum of squared Frobenius differences of \(\widehat G_j/\sqrt m\) and \(G_j/\sqrt m\) is \(O(N/s^2)\) deterministically. On \(\eta\le1/4\) the maximum operator norm of \(G_j/\sqrt m\) is uniformly bounded. Thus the block-diagonal covariance difference in Frobenius norm is \(O(\sqrt N/s+N/s^2)\) by expanding the Gram products, and for large indices all resulting covariance eigenvalues stay within fixed positive bounds. Ordinary Gaussian KL via the eigenvalue formula, followed by Pinsker, bounds the corresponding conditional Gaussian TV by a constant times this Frobenius difference.

Next jitter each discrete output uniformly in its own orthogonal cube. The jitter is a channel with rounding as a left inverse; hence applying it on both sides preserves TV on discrete outputs. The density of the jittered conditional ellipse is within \(O(Nh)\) of its continuous counterpart on the good covariance event. Augmenting the rounded seed label with its continuous preimage also preserves TV: the conditional law of the preimage given the rounded label is applied to both experiments without using the output. The resulting comparison is within \(O(Nm/s+Nh)+O(\Pr[\eta>1/4])\) of the continuous one. For \(v\to v_0>0\) the exceptional probability tends to zero by (3); for \(v\to0\), (2) gives \(\Pr[\eta>1/4]\le16v=o(\sqrt v)\). As every discrete independent target jitters to a continuous independent target, the lower bound follows. The fixed spherical discrete Gaussian jitters within \(O(Nh)\) of \(Q_0\), giving the matching upper bound.

## What this does and does not settle

In the continuous model with growing \(pr\), polynomially many columns in \(pr\) cannot give negligible TV (smaller than every inverse polynomial in \(pr\)) to a fixed output law. For instance, in the small-\(v\) regime the exact leading error is \(\sqrt{p r^2/(2\pi m)}\). Achieving an error of scale \(e^{-c pr}\) there requires column count on scale at least \(p r^2 e^{2c pr}\); negligibility alone asks for superpolynomial, not specifically exponential growth. The same obstruction passes to the stated broad dyadic regimes, including polynomial column counts in the bounded window with broad polynomial widths. It also passes through any separately established \(o(\min(1,\sqrt v))\) joint approximation of a linear image by the conditional ellipse, by triangle inequality. It does not show that every independent approximation fails at all discrete widths, that forgetting the label has the same cost, or that every way of changing the random-matrix or output model has this limitation.

[Albrecht et al., *A Gaussian Leftover Hash Lemma for Modules over Number Fields*](https://perso.jfelderhoff.fr/work/papers/AFLLW25.pdf), Theorem 6.4 and Remark 6.5 in the author-hosted version, bound a Rényi comparison and ask about negligible statistical distance. [Okada et al., *Spherical Gaussian Leftover Hash Lemma via the Rényi Divergence*](https://eprint.iacr.org/2023/479.pdf), Theorems 4.2 and 5.4, give fixed-order Rényi upper bounds that suffice for their reductions; their spherical comparison already identifies an output-dimension versus square-root-column scale for a single real block. The present result concerns the actual TV cost in the independent archimedean-block model, not a stronger Rényi lemma, conditional Gaussian generation, a decoding algorithm, or a statement about a concrete cryptosystem. The accompanying verifier checks the moment and covariance identities and illustrates the profile on generated scalar blocks; the proof is analytic.
