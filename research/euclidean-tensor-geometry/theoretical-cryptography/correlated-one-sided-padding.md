# How much correlation can improve a one-sided Rényi padding budget?

In the statistical comparison in [Lyubashevsky–Peikert–Regev, Claim 5.11](https://cims.nyu.edu/~regev/papers/ideal-lwe.pdf), a law of nonnegative squared-width padding variables is compared with its small negative coordinate shifts. Their law is a product of shape-two gammas. The [independent-place Airy result](one-sided-airy-padding.md) gives the sharp cost for independent laws at fixed average mean. Here we allow arbitrary dependence, including singular and shift-dependent choices in the lower bounds. Adding a *single common* nonnegative random offset to otherwise independent variables achieves a fourfold asymptotic improvement in the local leading Rényi cost. In the growing dimension polynomial-loss window it gives at least a twofold saving in the required mean, while a uniform lower bound rules out an improvement in order.

This concerns only the unwrapped, standalone padding-law comparison, not a new Ring-LWE reduction, efficient noise implementation, or a claim about a cryptosystem.

## 1. Statements

For probability laws \(P,Q\), set \(\mathcal R_2(P\|Q)=\int(dP/dQ)^2\,dQ\), with value \(+\infty\) without absolute continuity. The notation \(P-hz\) means the law of \(X-hz\) for \(X\sim P\). For \(d\ge2\), let \(\mathcal P_d\) be all Borel probability laws on \([0,\infty)^d\) satisfying \(\sum_i \mathbb E X_i\le d\). Define
\[
 B_d(h)=\inf_{P\in\mathcal P_d}\ 
            \sup_{z\in[0,1]^d}\log\mathcal R_2(P\|P-hz),\qquad h>0.
\]
Let \(a_1>0\) be the smallest positive number with \(\operatorname{Ai}(-a_1)=0\), and put \(I_*=16a_1^3/27\). All logarithms are natural.

1. For fixed \(d\), and every \(0<\epsilon<1\),
\[
 \frac{I_*}{d}\left\lfloor\frac{(d+1)^2}{4}\right\rfloor
 \ \le\ \liminf_{h\downarrow0}\frac{B_d(h)}{h^2}
 \ \le\ \limsup_{h\downarrow0}\frac{B_d(h)}{h^2}
 \ \le\ I_*\left(\frac{d}{4(1-\epsilon)^2}+\frac1{\epsilon^2}\right).
 \tag{1}
\]
In particular the iterated limit, taking \(h\downarrow0\) first in the liminf or limsup and then dividing by \(d\) and taking \(d\to\infty\), equals \(I_*/4\). For independent laws it is \(I_*\). We do not claim to determine the exact local minimax value at every fixed \(d\).

2. For every fixed \(C<\infty\) with \(C>0\) there exist laws \(P_d\in\mathcal P_d\) such that, uniformly for \(0<h\le \sqrt{C\log d/d}\),
\[
 \sup_{z\in[0,1]^d}\log\mathcal R_2(P_d\|P_d-hz)
       \le (I_*/4+o(1))\,d h^2 .
 \tag{2}
\]
The same \(P_d\) works at every \(h\) in the range. There is an absolute \(b>0\) such that *arbitrary* dependent laws, hence also their infimum, obey
\[
 B_d(h)\ge b d h^2-3\log 2\qquad(0<h\le1).
 \tag{3}
\]
The constant in (3) is not sharp. It does not establish that the constant \(I_*/4\) in (2) is optimal in the simultaneous limit.

To interpret these statements with average mean at most \(M\) and all actual shift coordinates in \([0,1]\), scale \(X\) by \(M\), i.e. use \(h=1/M\). For fixed \(\gamma>0\), let \(M_{\rm dep}(d,\gamma)\) be the infimum such that some joint law guarantees \(\mathcal R_2\le d^\gamma\) for all those shifts. Then \(M_{\rm dep}\) has order \(\sqrt{d/\log d}\) and
\[
 \limsup_{d\to\infty}
   \frac{M_{\rm dep}(d,\gamma)}
        {\sqrt{I_*d/(\gamma\log d)}}\le\frac12 .
 \tag{4}
\]
The denominator is the asymptotic minimum for independent coordinates from the independent-place result. The conclusion is an *achievable* factor relative to independence, not a matching simultaneous constant.

## 2. Scalar information inequality and a fixed-d lower bound

For a probability law \(P\) on \(\mathbb R^d\), and a direction \(v\), call \(g_v\) its weak score if
\(\int \partial_v\phi\,dP=\int\phi g_v\,dP\) for all \(\phi\in C_c^\infty\), with \(g_v\in L^2(P)\). This sign convention is harmless for its squared norm. The infimum of the squared score over scalar nonnegative laws of mean at most \(m>0\) is \(I_*/m^2\). For smooth densities \(p=f^2\) zero on the negative ray the score norm is \(4\|f'\|_2^2\), with \(f\in H^1_0(0,\infty)\) if the norm is finite. At mean one the half-line linear-potential inequality
\[
  \int |f'|^2+\kappa^3\int x f^2\ge a_1\kappa^2 \int f^2,\qquad
  \kappa=2a_1/3,
\]
gives \(4\|f'\|_2^2\ge I_*\). The positive Dirichlet ground state is proportional to \(\operatorname{Ai}(\kappa x-a_1)\); by dilation of the ground-state energy its squared density has mean one and attains the inequality. General \(m\) follows by scaling. For an arbitrary scalar probability law with weak score, convolve with a smooth probability supported in \([0,\eta]\), which preserves nonnegative support. The weak score after convolution is the conditional expectation of the old score given the sum, by testing and translating the test function. The smoothed law has mean at most \(m+\eta\) and Fisher information no greater than the old squared score. For its smooth density, finite \(\int (p')^2/p\) gives \(\sqrt p\in H^1\) by regularizing the square root on compact intervals and passing to the weak gradient; it vanishes on the negative half-line, so the same Dirichlet inequality applies. Let \(\eta\downarrow0\). This argument also shows that mean zero cannot have a finite weak score.

Fix \(d\). Take \(h_j\downarrow0\) and \(P_j\in\mathcal P_d\) along a bounded sequence of scaled costs, and pass to a subsequence on which those costs converge to \(L<\infty\). Tightness follows from the mean bound; let \(P_j\Rightarrow P\) along another subsequence. The mean bound passes by lower semicontinuity and the orthant remains the support. For fixed \(z\in[0,1]^d\) and \(Q_j=P_j-h_jz\), Cauchy–Schwarz gives
\[
 \left|\int\frac{\phi\,d(P_j-Q_j)}{h_j}\right|^2
 \le \frac{\mathcal R_2(P_j\|Q_j)-1}{h_j^2}\int\phi^2dQ_j .
\]
The left converges to \(|\int\partial_z\phi\,dP|^2\), using uniform difference quotients of the smooth test function. The limsup of the first right factor is at most \(L\) since the log losses are \(O(h_j^2)\). For \(z=e_i\), density of \(C_c^\infty\) in \(L^2(P)\) and Riesz give coordinate scores \(g_i\). By linearity and uniqueness the score for any \(z\) is \(\sum_i z_i g_i\). The positive semidefinite matrix \(J_{ij}=\int g_i g_j\,dP\) satisfies \(z^{\mathsf T}Jz\le L\) at every \(z\) in the cube.

Projecting \(P\) to its \(i\)-th coordinate contracts score norm by conditional expectation. Similarly, along the all-ones direction, project to \(\overline X=d^{-1}\sum_i X_i\), which translates by one per unit directional step and has mean at most one. These facts follow by testing functions of the scalar projection, with smooth cutoffs tending to one on the rest of the space to meet compact support. Thus \(J_{ii}\ge I_*/m_i^2\) where \(m_i=\mathbb E X_i\), and \(\mathbf1^{\mathsf T}J\mathbf1\ge I_*\). In particular \(\operatorname{tr}J\ge d I_*\) by Jensen and \(\sum m_i\le d\). For a uniformly chosen indicator \(z\) of exactly \(k\) coordinates,
\[
 \mathbb E z^{\mathsf T}Jz
  =\frac{k(d-k)}{d(d-1)}\operatorname{tr}J+
      \frac{k(k-1)}{d(d-1)}\mathbf1^{\mathsf T}J\mathbf1
  \ge I_*\,\frac{k(d+1-k)}d .
\]
Maximizing over \(k\) gives the lower bound in (1). The argument covers near-minimizers changing with \(h\) and singular candidates. Unbounded scaled costs are irrelevant to a finite lower limit.

## 3. A single shared offset achieves the smaller constant

For an arbitrarily small fixed \(\eta>0\) and an arbitrarily large fixed even integer \(L_0\ge4\), choose a mean-one density \(p\) on the half-line with Fisher information \(I(p)\le I_*+\eta\) and the following regularity: it is positive and smooth in the interior, behaves as \(x^{L_0}\) times a smooth strictly positive function near zero, and has an exponential tail times a power with bounded logarithmic derivative there. Here and below \(p\) is set to zero on the negative ray. To construct it, start with the Airy square root. Multiply it on a short interval at zero by a smooth cutoff equal to a constant times \(x^{L_0/2-1}\) very close to zero and to one outside the interval. Its effect on the Dirichlet energy tends to zero as the interval shrinks, since the original square root vanishes linearly. Add a small positive multiple of \(x^{L_0/2} e^{-x}\), then normalize the square root in \(L^2\) and dilate to mean one. The exponential term dominates the Airy tail, including its logarithmic derivative. Both the mean and the energy of the modified square root approach the original values. In particular \(p\) is \(C^1\) when extended by zero, and \((\log p)'\) is bounded below in the open half-line, since it is positive near zero.

We use two scalar facts. For \(p_b\) the law of \(bY\) with \(Y\) of density \(p\), write \(I(p_b)=I(p)/b^2\). For \(b\) in a compact subinterval of \((0,\infty)\), the following estimates are uniform:
\[
\begin{split}
 \int_\mathbb R \frac{p_b(x)^2}{p_b(x+t)}\,dx
     &\le 1+ (I(p_b)+o(1))t^2 , &&0\le t\le h,\quad h\downarrow0,\\
 \int_{2h}^{\infty}\frac{p_b(x)^2}{p_b(x+t)}\,dx
     &\le 1+(I(p_b)+o(1))t^2+O(h^{L_0+1}), && |t|\le h,\quad h\downarrow0 .
\end{split}
\tag{5}
\]
In the first bound, \(p_b(x+t)\ge e^{-K(t-u)}p_b(x+u)\) for \(0\le u\le t\) and fixed \(K\), by the logarithmic derivative bound, even across the zero support. Jensen's inequality on the integrated derivative over \([x,x+t]\) gives \(\int (p_b(x+t)-p_b(x))^2/p_b(x+t)\,dx\le e^{Kt}I(p_b)t^2\). Adding 1 gives that bound. For the second bound use \(p_b(x)^2/p_b(x+t)=2p_b(x)-p_b(x+t)+(p_b(x)-p_b(x+t))^2/p_b(x+t)\). On \(x\ge2h\), the integral of the first two terms is \(1+O(h^{L_0+1})\). The last term divided by \(t^2\) has integral \(I(p_b)+o(1)\), uniformly in \(0<|t|\le h\). To justify convergence by domination, for small \(x\) the shift lies in \([x/2,3x/2]\) and the integrand is bounded by \(O(x^{L_0-2})\); on a closed interior interval the density is bounded away from zero; on the tail the bounded logarithmic derivative and exponential decay give an integrable exponential majorant times a power. The case \(t=0\) follows directly. Dilation gives the stated uniformity in \(b\).

Take a common \(T\) of density \(p_\epsilon\) and independent \(Y_i\) of density \(p_{1-\epsilon}\), all mutually independent. Set
\[
 X_i=T+Y_i .
\]
They have mean one individually. For any \(z\in[0,1]^d\), write \(a=d^{-1}\sum_i z_i\) and \(w_i=z_i-a\). Thus \(a\in[0,1]\), \(w_i\in[-1,1]\), and \(\sum_i w_i^2\le d/4\), since the variance of a variable in \([0,1]\) is at most \(1/4\). The target law \(Q=P-hz\) is the image under the same addition map either of the independent shifted latent variables \((T-ah,Y_i-hw_i)\), or of \((T,Y_i-hz_i)\). In the first representation some \(w_i\) can be negative; we do **not** assert finite Rényi divergence of the full untrimmed law of the latent variables in that representation.

Split the numerator into subprobabilities \(P_{\rm g}\) and \(P_{\rm b}\) for the event all \(Y_i\ge2h\) and its complement. For a subprobability \(A\) write \(\mathcal R_2(A\|Q)=\int(dA/dQ)^2dQ\); this second moment contracts under a fixed map by conditional Jensen. For \(P_{\rm g}\) use the first representation of the denominator, which is positive on the trimmed numerator support, so the upper bound factors exactly into the first scalar integral in (5) for the \(T\) shift and the trimmed scalar integrals for the \(Y_i\) shifts. For \(P_{\rm b}\) use the second representation, where all its scalar shifts are nonnegative. The union bound after writing the joint integral of squared likelihood ratios gives
\[
 \mathcal R_2(P_{\rm b}\|Q)
   \le O(d h^{L_0+1})\exp(C_1 d h^2).
 \tag{6}
\]
Indeed, summing over each possible marked \(Y_i<2h\), its scalar integral over that interval is at most \(e^{Kh}\int_0^{2h} p_{1-\epsilon}(x)\,dx=O(h^{L_0+1})\). The unmarked integrals are bounded by the first line of (5), and the \(T\) integral is 1. This upper bound is uniform for \(\epsilon\le1/2\) and small \(h\); \(C_1\) can be chosen depending only on an upper bound for \(I(p)\), for example \(C_1=4I(p)+1\), by taking \(h\) sufficiently small for the fixed \(p\).

For \(P_{\rm g}\) the resulting second moment is at most \(e^{U}\) with
\[
 U=(I(p)+o(1))h^2
        \left(\frac{\sum_i w_i^2}{(1-\epsilon)^2}+\frac{a^2}{\epsilon^2}\right)
                +O(d h^{L_0+1})\ \ge 0 ,
 \tag{7}
\]
using the width-one version of (5) at \(t=ah/\epsilon\) for \(T\); thus the error tends to zero if \(h/\epsilon\to0\) and \(1-\epsilon\) stays bounded below. For fixed \(d\) and fixed \(\epsilon\in(0,1)\) the same estimates hold with constants depending on \(\epsilon\). Minkowski in \(L^2(Q)\) gives \(\mathcal R_2(P\|Q)^{1/2}\le e^{U/2}+\mathcal R_2(P_{\rm b}\|Q)^{1/2}\). In particular the extra log cost beyond \(U\) is at most \(2\mathcal R_2(P_{\rm b}\|Q)^{1/2}\).

For fixed \(d,\epsilon\), take \(L_0\ge4\) so this extra cost is \(o(h^2)\), then \(\eta\downarrow0\), giving the upper bound in (1). In large dimension one can take \(\epsilon=d^{-1/3}\) for all sufficiently large \(d\). In the entire range \(0<h\le\sqrt{C\log d/d}\), both \(h/\epsilon\to0\) and \(\epsilon^{-2}=o(d)\), so (7) is at most \(((I_*+\eta)/4+o(1))d h^2\). For the bad part, write \(v=d h^2\in(0,C\log d]\). Dividing the square root of (6) by \(v\) gives
\[
 O\left(d^{-(L_0-1)/4}v^{(L_0-3)/4} e^{C_1 v/2}\right)=o(1)
\]
by choosing the fixed even \(L_0>3\) with \((L_0-1)/4>C_1 C/2\). We may choose \(C_1=4(I_*+\eta)+1\) before picking the boundary order. The law for each \(d\) is independent of \(h\); letting the approximation accuracies \(\eta\) tend slowly to zero along a diagonal choice proves (2).

## 4. A dimension-uniform converse by binned overlap

This argument is different from taking the small-shift Fisher limit at a fixed dimension. Fix \(0<h\le1\), and bin the arbitrary joint input by coordinate cells of side \(h\), with masses \(p_j\) for \(j\in\mathbb N^d\) (including zero indices). For a shift vector \(z\in\{0,1\}^d\), the binned target mass at \(j\) is \(p_{j+z}\). Let \(G=\{j:h\sum_i j_i\le2d\}\), with \(p(G)\ge1/2\) by the mean bound. Put \(A_z=\sum_{j\in G}\sqrt{p_jp_{j+z}}\). Hölder on \(G\) gives
\[
 \mathcal R_2(P\|P-hz)\ge \frac{p(G)^3}{A_z^2}.
 \tag{8}
\]
For this, binning contracts \(\mathcal R_2\) and \(p_j=(p_j^2/p_{j+z})^{1/3}(\sqrt{p_jp_{j+z}})^{2/3}\). Zero denominators cause no problem: any positive numerator over zero gives infinite second moment.

Put \(f_j=\sqrt{p_j}\) on \(h\sum_i j_i\le3d\) and zero elsewhere. For \(j\in G\), all \(j+z\) used in \(A_z\) are within this larger set, because \(h\le1\). On \(\ell^2(\mathbb N)\) let \((U g)_j=g_{j+1}\), \(S=(I+U)/2\), and let \(M\) be the multiplier \(M_j=e^{-\beta h^2(hj)}\) for small fixed \(\beta>0\). Averaging over independent fair bits \(z_i\), and using \(f\le e^{3\beta d h^2} M^{\otimes d} f\) pointwise in the orthant, yields
\[
 \mathbb E_z A_z\le\langle f,S^{\otimes d}f\rangle
        \le e^{6\beta d h^2}\|MSM\|^d .
 \tag{9}
\]
Here all array entries and kernel coefficients are nonnegative for the weighting step; the norm bound uses \(\|f\|_2^2\le1\) and norms of finite tensor products.

For clarity, here is an elementary uniform spectral estimate. Let \(0<\beta\le1\), \(R=\beta^{-1/3}\), and take any unit sequence \(u\in\ell^2(\mathbb N)\). If at least half its mass lies at \(hj\ge R\), weighting gives
\[
 \|Su_M\|_2^2\le \|u_M\|_2^2
   \le 1-\frac12(1-e^{-2\beta h^2R}), \qquad u_M=Mu .
\]
Otherwise \(u_M\) has mass at least \(e^{-2}/2\) at \(hj<R\). For any \(g\) with \(g_{-1}=0\), telescoping and Cauchy–Schwarz give
\[
 \sum_{j<N}|g_j|^2\le
      N^2\sum_{j\ge-1}|g_{j+1}-g_j|^2,\qquad N=\lceil R/h\rceil .
\]
Also the elementary identity
\[
 \|Sg\|_2^2=\|g\|_2^2-\tfrac12|g_0|^2
                       -\tfrac14\sum_{j\ge0}|g_{j+1}-g_j|^2
\]
shows the loss includes one quarter of the entire difference sum with \(g_{-1}=0\). Since \(N\le2R/h\), using \(g=u_M\) yields loss at least \(e^{-2}\beta^{2/3}h^2/32\). The same bound holds in the first case since \(\beta^{2/3}h^2\le1\). Thus with \(a=e^{-2}/64\),
\[
 \|MSM\|\le e^{-a\beta^{2/3}h^2}.
\]
Choose \(\beta=(a/12)^3\), so \(6\beta=a\beta^{2/3}/2\). Now (9) implies some \(A_z\le\exp[-a\beta^{2/3} d h^2/2]\). Equation (8) gives (3) with \(b=a\beta^{2/3}\). This proof uses only binned finite-shift masses and the mean constraint, not independence or local smoothness.

Finally, by definition \(B_d\) is nondecreasing in \(h\), since the shift cubes are nested. Equation (3) rules out all \(h\ge1\) for a polynomial tolerance at sufficiently large \(d\), and implies \(d/M^2=O_\gamma(\log d)\) for feasible means. Equation (2) with \(M=(1/2+\delta)\sqrt{I_*d/(\gamma\log d)}\), each fixed \(\delta>0\), gives feasibility for large \(d\). This proves (4) and the matching order.

## Prior comparison and reproduction

The half-line Airy inequality and its scalar application are not new; the [independent note](one-sided-airy-padding.md) records earlier Airy and Fisher-information references. [Xiao–Wan–Shi–Devadas, *One-Sided Bounded Noise*](https://people.csail.mit.edu/devadas/pubs/one_sided_noise.pdf) addresses different one-sided/bidirectional privacy and distortion criteria, not this shift cube with a mean budget. Our conclusions extend the independent padding comparison to joint laws; even the positive construction does not give the equal-input simulation or cryptographic guarantees of a whole reduction.

Run \(\texttt{python3 verify-correlated-one-sided-padding.py}\). It checks exact shift-mask and operator identities, and controlled scalar trimmed integrals on small explicit nonnegative densities. These reproducible checks support the proof; they are not a sampler or evidence about any cryptographic deployment.
