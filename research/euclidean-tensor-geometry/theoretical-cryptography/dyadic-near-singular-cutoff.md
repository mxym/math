# Two near-singular regimes of the antiperiodic dyadic smoothing cutoff

The [nearest-neighbor cutoff](dyadic-dipole-cutoff.md) treats the antiperiodic kernel with correlation parameter \(\rho\) in a fixed compact subinterval of \((0,1)\). Its proof is not uniform when \(\rho\to1\), because the interaction range diverges and the normalized inverse form becomes nearly singular before a change of coordinates. We give the full critical Gaussian law in two near-singular regimes, including the macroscopic interaction range \((1-\rho)d=O(1)\). Some intermediate ranges remain open here.

This is a calculation for an abstract positive lattice Gaussian mass, not an algorithm for short vectors, a specified implementation, or a scheme-level statement. The motivating smoothing ingredient is the dual kernel mass in [Albrecht–Felderhoff–Lai–Lapiha–Woo](https://perso.jfelderhoff.fr/work/papers/AFLLW25.pdf) and [Düzlü–Gargava–Tairi](https://opencryptology.org/2026/2180). The analytic difference here is an exact change to antiperiodic prefix coordinates and integer sparsity estimates, not a new general kernel-smoothing theorem.

## 1. Result and exact coordinate change

Let \(P\) be the shift on \(d\) coordinates with one negative wrap, so \(P^d=-I\), and \(d\) tends to infinity through even integers. Put \(\epsilon=1-\rho\), with \(0<\rho=\rho_d<1\) and \(\epsilon\to0\), and write
\[
 K=\sum_{j\in\mathbb Z}\rho^{|j|}P^j,\qquad
 Q(x)=x^{\mathsf T}Kx,\qquad
 \tau=2\epsilon t.
\]
The sum is absolutely convergent for each \(\rho<1\). Fix \(c\in\mathbb R\) and set \(\tau=\log d+c\). Suppose that either
\[
  (\epsilon d)^2=o\!\left(\frac{\log d}{\log\log d}\right)
   \qquad\text{or}\qquad
  \epsilon^{-1}=d^{o(1)}. \tag{1}
\]
Then
\[
 \sum_{x\in\mathbb Z^d}e^{-t Q(x)}\ \longrightarrow\ \exp(2e^{-c}). \tag{2}
\]
Under the normalized weights, the distribution of \(u=(I-P)^{-1}x\) converges in total variation to the product on \(\mathbb Z^d\) with marginal weights proportional to \(e^{-\tau j^2}\), \(j\in\mathbb Z\) (view both on the common ambient space). In particular the number of nonzero prefix sites tends to \(\operatorname{Pois}(2e^{-c})\); with probability \(1-o(1)\) these are separated single \(\pm1\) spikes, each giving a signed adjacent dipole in the original coordinates, with the antiperiodic sign at the boundary. The total variation claim compares the actual evolving product with the actual evolving lattice Gaussian, not just their limiting support sizes.

For a dual Gram \(\kappa K\) with positive scale \(\kappa\), at a fixed Gaussian smoothing tolerance \(0<\varepsilon<1\), (2) gives
\[
 2\epsilon\pi\kappa\,\eta_\varepsilon^2
     =\log d+\log\!\bigl(2/\log(1+\varepsilon)\bigr)+o(1). \tag{3}
\]
Indeed bracket the nonzero mass by two fixed offsets before letting the bracket width go to zero. The correlated part of the Gram may vary with \(d\) as in (1), and \(\kappa\) may vary independently. The arguments also apply uniformly for \(c\) in any fixed bounded set (by the same estimates).

The map \(x=(I-P)u\) identifies \(\mathbb Z^d\) exactly with the union
\[
  u\in\mathbb Z^d\ \cup\ (\mathbb Z+\tfrac12)^d . \tag{4}
\]
In fact \(x_i=u_i-u_{i-1}\) for \(i>0\), and \(x_0=u_0+u_{d-1}\); hence \(2u_0\in\mathbb Z\) and all coordinates have its fractional part. Conversely every indicated \(u\) gives integer \(x\), and \(I-P\) is invertible since \(1\) is not an eigenvalue of \(P\).

Let \(L_P=2I-P-P^{-1}\) and \(A=\epsilon^2 I+\rho L_P\). The geometric series gives \(K=(1-\rho^2)A^{-1}\). Conjugating the quadratic form by \(I-P\) now yields
\[
 H(u):=\frac{Q((I-P)u)}{2\epsilon}
  =\frac{1+\rho}{2\rho}\,u^{\mathsf T}(I-W)u,\qquad
  W=\frac{\epsilon}{1+\rho}K. \tag{5}
\]
Indeed \((I-P)^{\mathsf T}(I-P)=L_P\), all these matrices commute, and \(\rho L_P A^{-1}=I-\epsilon^2 A^{-1}\). Both parts of (4) are included in the theta sum, each point once.

## 2. Macroscopic interaction range

For \(\rho\ge1/2\), the smallest eigenvalue of \(H\) as a quadratic form is at least
\[
 \gamma_d=\frac1{1+(\epsilon d)^2}.
\]
The smallest eigenvalue of \(L_P\) is \(4\sin^2(\pi/(2d))\ge4/d^2\), and (5) has eigenvalue \((1+\rho)L_P/[2(\epsilon^2+\rho L_P)]\) on each eigenspace. Also
\[
 |W_{ij}|\le\epsilon.
\]
For a displacement \(j\) with \(0\le j<d\), the signed series \(K_{0j}\) has value \((\rho^j-\rho^{d-j})/(1+\rho^d)\), up to the chosen sign convention, of magnitude at most one.

In the first regime of (1), \(\gamma_d\tau/\log\log d\to\infty\). The half-integer branch in (4) therefore has total weight at most \([C e^{-\gamma_d\tau/4}]^d=o(1)\), by the spectral bound and the product sum of shifted one-dimensional masses. On the integer branch set \(s_0=\lceil d e^{-\gamma_d\tau/2}\rceil\). The total weight of support size at least \(s_0\) is bounded by
\[
 \sum_{s\ge s_0}\binom ds
     \bigl(2\sum_{j\ge1}e^{-\gamma_d\tau j^2}\bigr)^s=o(1).
\]
To see the last estimate, the one-coordinate sum is \(O(e^{-\gamma_d\tau})\), and each binomial term is at most \([C e^{-\gamma_d\tau/2}]^s\) using \(d/s\le e^{\gamma_d\tau/2}\). Moreover \(s_0\to\infty\) since \(\gamma_d\le1\) and \(\tau=\log d+O(1)\).

For a support of size \(s<s_0\), use \(|u^{\mathsf T}W u|\le\epsilon s\|u\|^2\) by Cauchy–Schwarz, and \((1+\rho)/(2\rho)=1+O(\epsilon)\). Thus
\[
 |H(u)-\|u\|^2|\le C\epsilon(s_0+1)\|u\|^2,\qquad
 \tau\epsilon(s_0+1)=o(1).
\]
The latter follows from \(\epsilon d=O(\sqrt{\log d})\) and \(\gamma_d\tau\gg\log\log d\). The weights on this support range are sandwiched between the product weights at precisions \(\tau-\delta_d,\tau+\delta_d\) for \(\delta_d=o(1)\). The full unnormalized product theta at either precision tends to \(\exp(2e^{-c})\), from \(\sum_{j\in\mathbb Z}e^{-\tau j^2}=1+2e^{-\tau}+O(e^{-4\tau})\). Both product tails at \(s\ge s_0\) are \(o(1)\) by the same binomial bound. Consequently the sum of absolute differences of unnormalized weights tends to zero over all integer and half-integer \(u\) (the comparison law gives the latter branch zero weight). This proves total variation and (2) in the first regime.

## 3. A uniform line gap when \(\rho\) is large

For the other regime, use open-line energy
\(Q_\rho^{\rm line}(x)=\sum_{i,j}x_i x_j\rho^{|i-j|}\)
on finitely supported integer sequences. As in the compact-\(\rho\) note, this has the exact positive decomposition
\[
 Q_\rho^{\rm line}(x)=(1-\rho)^2\sum_{l\ge1}\rho^{l-1}
 \sum_j\left(\sum_{i=j}^{j+l-1}x_i\right)^2 .
\]
This follows by counting intervals containing each pair. If the sum of \(x_i\) is nonzero, the \(l\)-th squared-sum term is at least \(l\), since the interval sums are integers summing to \(l\sum_i x_i\); hence \(Q_\rho^{\rm line}\ge1\). In every case the Fourier symbol gives \(Q_\rho^{\rm line}\ge(1-\rho)\|x\|^2/(1+\rho)\). The cycle has the same spectral lower bound because it samples that symbol at its signed-shift eigenangles. After dividing by \(2\epsilon\) both spectral lower bounds are at least \(\|x\|^2/4\).

For \(\rho\ge3/4\), the adjacent unit dipoles are the only nonzero sequences of normalized line energy \(1\), and every other nonzero sequence has normalized energy at least \(5/4\). Indeed a nonzero net charge has energy at least \(1/(2\epsilon)\ge2\), and coefficient norm squared at least five has the required bound spectrally. It remains to examine neutral integer sequences of norm squared two or four (a neutral sequence has even squared norm). A norm-two opposite pair at distance at least two has normalized energy \((1-\rho^g)/(1-\rho)\ge1+\rho\). At norm four there are four unit coefficients, two positive and two negative. Denote the three successive gap factors by \(a,b,c_0\), each at most \(\rho\) and nonnegative. Up to reflection and overall sign, the unnormalized energies for the three patterns are
\[
\begin{array}{c|l}
 +-\!+- & 2(1-a)+2(1-c_0)-2b(1-a)(1-c_0)\\
 +--+   & 2(1-a)+2(1-c_0)+2b(1-a)(1-c_0)\\
 ++--   & 4+2(a+c_0)-2b(1+a)(1+c_0).
\end{array}
\]
The first is minimized by \(a=b=c_0=\rho\) and equals \(2\epsilon(2-\rho\epsilon)\) there. The second is at least \(4\epsilon\). The third is minimized at \(b=\rho\) and corners \(a,c_0\in\{0,\rho\}\) by linearity in each; the corner values are \(4-2\rho,\ 4-2\rho^2,\ 2\epsilon(1+\rho)(2+\rho)\), all at least \(4\epsilon\) for \(\rho\ge3/4\). This proves the fixed normalized gap even as \(\rho\to1\); the fixed-\(\rho\) additive gap in the cited note would not suffice.

## 4. Subpolynomial interaction lengths

In the second regime of (1) take \(R=\lceil\epsilon^{-1}(\log d)^2\rceil=d^{o(1)}\). Group the support of \(x\) on the cycle at gaps greater than \(R\), unfolding each cluster with the antiperiodic sign. If all gaps are at most \(R\), the support has size at least \(d/R\), and such vectors have total weight \(o(1)\) by the normalized spectral lower bound \(Q(x)/(2\epsilon)\ge\|x\|^2/4\) and the binomial estimate \(\sum_{s\ge d/R}(C R d^{-1/4})^s=o(1)\). The zero vector is separate and has weight one.

For a vector with a cut, the normalized cycle and sum of normalized open-line energies differ by a relative \(O(\rho^R/\epsilon^2)\) of the latter. To check this, from any included lift of a support index within its cluster, all omitted lifts (other clusters and other period copies) are at distance \(>R\). The absolute unnormalized tail row sum is at most \(2\rho^{R+1}/(1-\rho)\). Multiply by \(\|x\|^2\) in the quadratic form, divide by \(2\epsilon\), and use the open-line spectral lower bound. Since \(R\ge\epsilon^{-1}(\log d)^2\), the relative error times \(\tau\) tends to zero.

A cluster of \(s\) support positions has at most \(dR^{s-1}\) position descriptions. Use the smaller precision \(\tau(1-O(\rho^R/\epsilon^2))\) for an upper bound on activity. The total candidate activity from support sizes \(s\ge s_*\) is \(o(1)\) for any fixed \(s_*>8\): it is bounded by a geometric sum with terms \(dR^{s-1}(C d^{-1/4})^s\) using the normalized spectral lower bound. Likewise, for \(s<s_*\) the activity with any sufficiently large fixed coefficient magnitude is \(o(1)\), using its squared-energy cost and summing the remaining coefficients with the same bound. For the remaining finitely bounded coefficients and support sizes, the normalized \(5/4\) gap in §3 and \(R=d^{o(1)}\) give total \(O(dR^{s_*-1}d^{-5/4})=o(1)\), except for the \(2d\) signed adjacent dipoles. Their total activity stays bounded. Dropping separation constraints bounds the total cluster partition function by the exponential of the sum of activities, and the weight of configurations with any nonprimitive cluster by that exponential times the vanishing nonprimitive activity. These bounds, together with the no-cut estimate, show that outside the separated dipole configurations the **unnormalized** Gibbs weight tends to zero.

On the good configurations, \(x=(I-P)u\) means exactly one \(\pm1\) prefix coordinate per dipole, with the corresponding wrap sign, and the normalized open energy equals \(\|u\|^2\). Their weights are sandwiched by product precisions \(\tau\pm o(1)\), by the relative energy bound. Conversely product configurations have only separated spikes with probability \(1-o(1)\): the expected number of coefficient magnitudes at least two is \(O(d e^{-4\tau})\), and pairs of active sites within cyclic distance \(R+2\) have expected count \(O(R/d)\). These are exact union bounds using independent product coordinates of nonzero probability \(O(1/d)\). Thus the same sandwich and negligible complements prove convergence of unnormalized weights in summed absolute difference, then normalization gives the total variation result and (2).

The two regimes in (1) do not cover, for example, \(\epsilon^{-1}=d^\beta\) with a fixed \(0<\beta<1\). Neither proof bounds all intermediate ranges, where the spectral gap of the prefix form can vanish polynomially and the open-line cluster lengths are not subpolynomial. No claim of a phase change or a counterexample for those ranges is made.

**Replay.** Run `python3 verify-dyadic-near-singular-cutoff.py` for exact checks of the prefix form and two branches, the four-charge energy formulas and uniform gap, and the dipole/sign correspondence. The asymptotic estimates above are analytic.
