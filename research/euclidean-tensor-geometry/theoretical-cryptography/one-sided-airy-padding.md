# The optimal one-sided Rényi padding law at fixed mean

Lyubashevsky–Peikert–Regev use one-sided Rényi-2 comparison for a nonnegative random squared-width padding variable. At the level of that statistical comparison, the familiar shape-two gamma law has a logarithmic loss at small translations. The optimal leading constant over **all** nonnegative laws of fixed mean is instead the square of an Airy ground state. This includes laws that change with the shift and laws with atoms, not only smooth fixed-density optimizers.

We optimize the ideal statistical padding criterion, not the full computational reduction, any deployed parameter, or a procedure on cryptographic instances.

## 1. Statement

Let \(P-h\) denote the law of \(X-h\) for \(X\sim P\), and use
\[
 H^2(P,Q)=1-\int\sqrt{dP\,dQ},\qquad
 \chi^2(P\|Q)=\int(dP/dQ-1)^2\,dQ,\qquad
 \mathcal R_2(P\|Q)=1+\chi^2(P\|Q).
\]
If \(P\) is not absolutely continuous with respect to \(Q\), set the last two losses to infinity. The Hellinger affinity uses a common dominating measure. Write \(a_1>0\) for the first positive number with \(\operatorname{Ai}(-a_1)=0\), and define
\[
 E_*=\frac{4a_1^3}{27},\qquad I_*=4 E_*=\frac{16a_1^3}{27}.
\]
Let \(\mathcal P_1\) be the Borel probability laws on \([0,\infty)\) of mean at most one.

**Theorem.** As \(h\downarrow0\),
\[
 \inf_{P\in\mathcal P_1} H^2(P,P-h)\sim \tfrac12 E_* h^2,\qquad
 \inf_{P\in\mathcal P_1} \chi^2(P\|P-h)\sim I_*h^2.
 \tag{1}
\]
The same limits hold if each loss on the left is first replaced by its supremum over \(0\le z\le h\) in place of the fixed shift \(h\). A single mean-one density attains both asymptotics: \(p(x)=f_*(x)^2\) on \(x\ge0\), where
\[
 \kappa=\frac{2a_1}{3},\qquad
 f_*(x)=\frac{\sqrt\kappa\,\operatorname{Ai}(\kappa x-a_1)}
                         {|\operatorname{Ai}'(-a_1)|}.
 \tag{2}
\]
Moreover, every asymptotically optimal sequence of laws for either single-shift minimum converges weakly to this same law. Weak convergence is asserted, not total variation.

The direction \(P\|P-h\) is intentional. No corresponding finite two-sided Rényi guarantee is asserted; for example the right-translated version can lose positive mass at the lower end of the support.

## 2. The ground-state energy and the Airy upper bound

For real \(f\in H_0^1(0,\infty)\) with finite \(\int x|f(x)|^2\,dx\), the Dirichlet linear-potential inequality is
\[
 \int|f'|^2+\kappa^3\int x|f|^2\ \ge\ a_1\kappa^2\int |f|^2.
 \tag{3}
\]
The function in (2) solves the equality differential equation and is positive on the open half-line. One proof of (3) is the ground-state identity: for a smooth function compactly supported in the open half-line, subtract the right-hand side from the left to obtain \(\int f_*^2|(f/f_*)'|^2\) by integration by parts. Approximation extends the inequality; equality is attained only by a multiple of the positive ground state, by the same identity on compact subintervals or simplicity of the Dirichlet ground state. The normalization in (2) follows from
\(\frac{d}{du}(u\,\operatorname{Ai}(u)^2-\operatorname{Ai}'(u)^2)=\operatorname{Ai}(u)^2\).
For the mean, apply a normalized dilation \(f_*(x)\mapsto\sqrt{s}f_*(sx)\) to the attained minimum in (3). If its kinetic energy is \(E\) and its mean is \(m\), the energy of the dilation is \(s^2E+\kappa^3m/s\). Stationarity at \(s=1\) gives \(2E=\kappa^3m\), and equality in (3) gives \(m=2a_1/(3\kappa)=1\) and \(E=E_*\). Thus among unit \(L^2\) functions with mean at most one, the sharp lower energy is \(E_*\).

Extend \(f_*\) by zero to the negative half-line. It belongs to \(H^1(\mathbb R)\). The Hellinger loss of the displayed density is \(\tfrac12\|f_*(\cdot+h)-f_*\|_2^2\), giving \(\tfrac12 E_*h^2+o(h^2)\) by differentiation of translations in \(L^2\).

For the chi-squared loss, the part of the integral on \([-h,0)\) is \(\int_0^h p(x)\,dx=O(h^3)\), since \(f_*(x)\) vanishes linearly at zero. On \(x\ge0\), the integrand divided by \(h^2\) is
\[
 \left(\frac{f_*(x+h)-f_*(x)}h\right)^2
 \left(1+\frac{f_*(x)}{f_*(x+h)}\right)^2 .
\]
It tends pointwise on \(x>0\) to \(4|f_*'(x)|^2\). For sufficiently small \(h\) it is uniformly bounded on compact intervals, by linear vanishing and monotonicity sufficiently close to zero. On the tail, the standard real Airy asymptotics give for \(0<h\le1\) the ratio bound \(f_*(x)/f_*(x+h)\le C\exp(C h\sqrt{x+1})\) for large \(x\); this follows by subtracting the two \(z^{3/2}\) exponents and bounding their prefactors. The supremum of \(|f_*'|\) on \([x,x+h]\) is bounded by \(C(1+x)^{1/4}\exp(-c x^{3/2})\). Thus there is an integrable dominating function, and the upper constant is \(4E_*\). These limits also give the claimed uniform upper constants for \(0\le z\le h\).

## 3. Global lower bounds and rigidity

A smooth local Fisher-information computation alone cannot rule out optimizing a different, possibly singular law at every \(h\). To do so, bin any \(P\in\mathcal P_1\) into intervals \([jh,(j+1)h)\), \(j\in\mathbb Z\). Write \(p_j\) for its masses, \(b_j=\sqrt{p_j}\), with \(p_j=0\) for \(j<0\). Under the shift \(-h\), the binned masses are exactly \(p_{j+1}\). Both losses contract under this binning.

Put \(D=\sum_{j\ge-1}(b_{j+1}-b_j)^2\). The binned Hellinger loss is \(D/2\). The binned chi-squared loss is
\[
 \sum_{j\ge-1}(b_{j+1}-b_j)^2
                   \left(1+\frac{b_j}{b_{j+1}}\right)^2. \tag{4}
\]
Both-zero terms are zero; a positive numerator mass over a zero denominator gives infinity. In particular the loss in (4) is at least \(D\).

Interpolate linearly with node values \(b_j/\sqrt h\) at \(x=(j+1)h\), starting with \(b_{-1}=0\) at zero. Call the interpolant \(f_h\). Direct integration of each linear cell gives
\[
 \|f_h'\|_2^2=D/h^2,\qquad
 \|f_h\|_2^2=1-D/6,\qquad
 \int x f_h(x)^2\,dx\le 1+h. \tag{5}
\]
For the last inequality, \(f_h^2\) is bounded pointwise by the linear interpolation of its squared node values. Each associated triangular hat has area \(h\) and centroid at its node, so its total first moment is \(\sum_j (j+1)h\,p_j\le1+h\).

For any sequence with the losses divided by \(h^2\) bounded, (5) gives bounded \(H^1\) norm and a uniformly vanishing \(L^2\) tail by the first-moment bound. On bounded intervals the interpolants are equicontinuous by the \(L^2\) bound on the derivative, and have uniformly bounded values by the zero boundary condition. After a subsequence, they converge uniformly on compact intervals, strongly in \(L^2\) on the half-line, and weakly in \(H^1\) to a nonnegative unit function \(f\in H^1_0\) with mean at most one. For Hellinger, weak lower semicontinuity and (3) give the sharp lower constant \(E_*/2\).

For chi-squared, fix any compact set of subintervals within \(\{x:f(x)>0\}\). On cells contained in a slightly larger compact subset of the same open set, uniform convergence and the modulus of continuity give \(b_j/b_{j+1}\to1\) uniformly. There (4) divided by \(h^2\) is at least \((4-o(1))\) times the interpolated kinetic energy. Use weak lower semicontinuity on the fixed subintervals and exhaust the open positivity set. The derivative of the nonnegative absolutely continuous representative of \(f\) is zero almost everywhere on its zero set (at any interior zero where the derivative exists it is zero). This proves the lower bound \(4\|f'\|_2^2\ge I_*\). Unbounded-loss sequences do not affect the lower limits. The supremum over shifts includes its endpoint, giving the same lower bounds for worst-case losses.

If a sequence attains either leading constant, every subsequential limit \(f\) of its interpolants must attain the energy minimum, hence is \(f_*\). To transfer to the original measures, the binned atomic measure at the nodes moves each input by at most \(h\). Its replacement by the triangular hats also moves mass by at most \(h\), and the hat density differs from \(f_h^2\) in \(L^1\) by precisely \(D/6\), using the norm identity and pointwise inequality above. This proves weak convergence of the originals and the stated rigidity.

## 4. Sharp independent-place budget

Consider \(d\) independent nonnegative squared-width padding variables with average mean at most \(M\), not necessarily identically distributed. For each coordinate require comparisons from its nominal law \(P_i\) to \(P_i-z_i\), for all \(0\le z_i\le1\) independently. Define \(J_d(M)\) to be the infimum of the largest \(\log\mathcal R_2\) for the resulting product laws, using natural logs. Then as \(M\to\infty\),
\[
                  J_d(M)=(I_*+o(1))\,d/M^2,                \tag{6}
\]
where the relative error can be taken independent of \(d\). The upper bound uses i.i.d. copies of \(M X\) with \(X\) as in (2), since \(\mathcal R_2\) multiplies under products. For the lower bound let \(g(m)\) be the infimum worst-case log loss at single-coordinate mean at most \(m\). It is nonincreasing, and scaling (1) gives \(m^2g(m)\to I_*\). For any fixed \(\eta>0\), there is \(M_0\) such that \(g(m)\ge (I_*-\eta)/(m+M_0)^2\) for all \(m\ge0\): use the asymptotic bound for \(m\ge M_0\) and monotonicity for \(m<M_0\). The worst-case product log loss is a sum of coordinate worst-case log losses, and Jensen gives the lower bound \(d(I_*-\eta)/(M+M_0)^2\). This proves (6).

In particular, for a fixed \(\gamma>0\), the smallest average mean permitting the uniform constraint \(\mathcal R_2\le d^\gamma\) is
\[
        (1+o(1))\sqrt{\frac{I_*d}{\gamma\log d}}.
 \tag{7}
\]
The necessary budget tends to infinity: the preceding positive lower bound at bounded \(M\) makes the total log loss linear in \(d\). Equation (6) now gives the necessary asymptotics, and independent Airy laws with an arbitrarily small fixed slack give sufficiency.

For a simpler near-optimal fixed shape, the mean-one \(\Gamma(3,\mathrm{rate}\ 3)\) density has small-shift chi-squared constant \(9\). Indeed, for the density proportional to \(x^2 e^{-\lambda x}\),
\[
 \mathcal R_2(P\|P-h)=e^{\lambda h}\frac{\lambda^3}{2}
     \int_0^\infty \frac{x^4}{(x+h)^2} e^{-\lambda x}\,dx
 \le e^{\lambda h}\bigl(1-\lambda h+\tfrac32(\lambda h)^2\bigr).
\]
The inequality follows from \((1+z)^{-2}\le1-2z+3z^2\) for \(z\ge0\); the matching local leading coefficient is the integral of the squared score, or follows by differentiation and dominated convergence including the quadratically vanishing boundary. With \(\lambda=3\), replacing \(I_*\) by \(9\) therefore gives an attainable budget in (7). In contrast, the shape-two gamma with mean scaled to one has \(\chi^2\sim4h^2\log(1/h)\), from the exact one-sided formula in LPR. Within this fixed-shape family, obtaining the same polynomial bound uses mean of order \(\sqrt d\), losing a square root of the logarithm in the **squared-width** budget.

## 5. Statistical reduction ingredient, not a new hardness theorem

[Lyubashevsky–Peikert–Regev, *On Ideal Lattices and Learning with Errors over Rings*, Definition 3.5 and Claim 5.11](https://cims.nyu.edu/~regev/papers/ideal-lwe.pdf) compare a product shape-two gamma prior to its small left translates, so that a non-negligible event remains non-negligible in the padded experiment. With \(\mathcal R_2\le d^\gamma\), exactly the same Cauchy–Schwarz comparison gives \(Q(A)\ge P(A)^2/d^\gamma\). Equations (6)–(7) quantify the best mean budget for this **particular** transfer criterion in the independent-place class. A fixed baseline squared width can be translated into the two laws simultaneously without changing their divergence, and a different bound on shifts rescales the budgets linearly.

No assertion is made about optimizing correlated priors, about necessity for all possible event-transfer methods, or about the narrower noise in the different [Peikert–Regev–Stephens-Davidowitz reduction](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf). In particular the exact Airy law is an analytic optimizer, not a finite-precision sampling theorem. The gamma alternative already shows that the logarithm from shape two is not required for the shift-comparison ingredient.

The half-line Airy energy itself is classical. The corresponding nearest-neighbor square-root overlap and Airy constant occur in [Berry, Hall, Zwierz and Wiseman, *Optimal Heisenberg-style bounds for the average performance of arbitrary phase estimates*, §IV and Appendix D](https://arxiv.org/abs/1209.3547). The same constant in the binned Hellinger argument is not claimed new. [NIST DLMF §9.7](https://dlmf.nist.gov/9.7) and [§9.9](https://dlmf.nist.gov/9.9) give the Airy tail and zero facts. [Xiao, Wan, Shi and Devadas, *One-Sided Bounded Noise*, CCS 2025](https://people.csail.mit.edu/devadas/pubs/one_sided_noise.pdf) studies partial/bidirectional guarantees and different distortion constraints. [Alghamdi, *Estimation and Optimization of Information Measures with Applications to Fairness and Differential Privacy*, §2.14, Theorem 2.13 and Proposition 2.5](https://nrs.harvard.edu/URN-3:HUL.INSTREPOS:37375888), and [Alghamdi et al., *Schrödinger Mechanisms*](https://par.nsf.gov/servlets/purl/10533621), identify Fisher-information ground states for small-sensitivity privacy, including a full-line absolute-cost Airy law with the first zero of \(\operatorname{Ai}'\), rather than the half-line Dirichlet boundary used here. The scoped contribution here is the sharp full **one-directional** chi-squared minimax, including shift-dependent laws, and its independent-place LPR-style budget. The verifier is a synthetic numerical and exact arithmetic cross-check, not a proof by fitting the asymptotic.

Run `python3 verify-one-sided-airy-padding.py` with SciPy available to replay the companion checks. All inputs are generated from the formulas above.
