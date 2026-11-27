# A sharp weak-correlation phase for negatively correlated Gaussian repetition

The worst probability that a set of Gaussian perturbation calls all fail can depend on the directions of their correlations. In a regular simplex of negatively correlated scalar calls, the usual half-line extremizers have an odd–even split: at weak correlation an **odd** number of calls needs one central interval for the sharp second-order constant, while an **even** number has balanced half-lines as its limiting extremizers. For every positive admissible strength, not just weak dependence, the best half-line choice for odd arity is strictly suboptimal.

**Scope.** This bounds abstract probabilities of simultaneous binary outcomes. It is motivated by the positive probability-amplification step of [Peikert–Regev–Stephens-Davidowitz, §3](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf), with no decoder, implementation, challenge or cryptographic hardness claim. The [earlier repetition note](gaussian-perturbation-repetition-budget.md) gives an exact bound over all cross-covariances with a given norm cap by choosing a common direction; it does not give the exact optimum for fixed unlike directions. [Neeman, Theorem 1.4](https://emis.de/ft/42095) gives halfspace optimality in the case of nonnegative correlations, not the negative simplex pattern here. No general signed-covariance rearrangement is asserted below.

## 1. Model and complete second-order answer

Fix an integer \(m\ge2\), let \(0<r<1/(m-1)\), and let \(Y_1,\ldots,Y_m\) be standard Gaussian marginals with \(\operatorname{Cov}(Y_i,Y_j)=-r\) for \(i\ne j\). This is realizable by conditionally independent Gaussian perturbations of a common standard Gaussian \(X\): take regular-simplex unit directions \(u_i\) in \(\mathbb R^{m-1}\) with \(u_i\cdot u_j=-1/(m-1)\), independent standard \(Z_i\), and
\[
 Y_i=\sqrt{(m-1)r}\,u_i\cdot X+\sqrt{1-(m-1)r}\,Z_i .
\]
Let \(f_i:\mathbb R\to[0,1]\) be arbitrary measurable functions with \(\int f_i\,d\gamma=p=1/2\), where \(\gamma\) is standard Gaussian law. Put
\[
 S_m(r)=\sup_{(f_i)} \mathbb E\prod_{i=1}^m f_i(Y_i).
\]
As a failure-probability bound the same supremum holds if the marginal failure probabilities are only known to be at most \(1/2\), because each function can be increased to have exactly that mean. Indicator functions are admissible; permitting fractional values includes randomized calls.

Write \(k=\lfloor m/2\rfloor\), \(a=\varphi(0)=1/\sqrt{2\pi}\), and \(c=\Phi^{-1}(3/4)>0\). Here \(\varphi,\Phi\) are the standard Gaussian density and distribution function. As \(r\downarrow0\) with \(m\) fixed,
\[
\begin{aligned}
 S_m(r)={}&p^m+k p^{m-2}a^2r\\
 &+\left(3p^{m-4}\binom{k}{2}a^4
       +{\bf1}_{m\ {\rm odd}}\;2k p^{m-3}a^2 c\varphi(c)\right)r^2
       +O_m(r^3). \tag{1}
\end{aligned}
\]
For \(m=2,3\) the term with \(\binom{k}{2}\) is zero.

For even \(m=2k\), taking \(k\) left and \(k\) right half-line indicators attains (1) through second order. For odd \(m=2k+1\), take \(k\) left and \(k\) right half-lines **and** one central interval \([-c,c]\). Any family attaining \(S_m(r)-o(r^2)\) approaches these respective families, up to permutations, in the sum of the \(L^1(\gamma)\) distances. This is a limiting shape statement, not an assertion that these exact sets optimize the finite-\(r\) problem.

## 2. The uniform expansion and its first-order faces

Set \(u_i=\int y f_i(y)\,d\gamma(y)\) and \(v_i=\int(y^2-1) f_i(y)\,d\gamma(y)\). Then
\[
\begin{aligned}
 C_1(f)&=-p^{m-2}\sum_{i<j}u_i u_j,\\
 C_2(f)&=\tfrac12 p^{m-2}\sum_{i<j}v_i v_j
     +p^{m-3}\sum_i v_i\!\!\sum_{\substack{j<l\\ j,l\ne i}}u_j u_l
     +3p^{m-4}\sum_{i<j<l<h}u_i u_j u_l u_h. \tag{2}
\end{aligned}
\]
The probability is \(p^m+r C_1+r^2 C_2+O_m(r^3)\) uniformly over the functions. For a verification, let \(P_r(y)\) be the joint Gaussian density. Differentiating the Fourier transform of the density, or the Gaussian heat equation for changing covariance, gives \(\partial_rP_r=-\sum_{i<j}\partial_i\partial_jP_r\). At \(r=0\), a once-differentiated univariate density contributes \(-y\varphi(y)\) and a twice-differentiated one contributes \((y^2-1)\varphi(y)\). At order two, repeating one edge gives the factor \(1/2\); two different edges that share a vertex give the middle term; disjoint edges pair a fixed four-set in three ways. Taylor's remainder is bounded uniformly in \(L^1\): for \(|r|\le1/[2(m-1)]\) the covariance eigenvalues are uniformly in a positive compact interval, so the third derivative of \(P_r\) is bounded by a fixed polynomial times a fixed integrable Gaussian envelope. Multiplying by \(\prod f_i\le1\) preserves this remainder bound.

Each \(|u_i|\le a\), with equality exactly for the corresponding half-line indicator. Indeed the maximal integral of \(y f_i\) at mass one half is obtained by taking the top half of \(y\), with strictness away from equality; the minimum follows by reflection. Let independent signs \(\xi_i\) have means \(u_i/a\). Then
\[
 \sum_{i<j} u_i u_j=\frac{a^2}{2}
 \left(\mathbb E\Big(\sum_i \xi_i\Big)^2-m\right).
\]
The minimum is \(-k a^2\): for even \(m\) the square can be zero, while for odd \(m\) it is at least one. If \(m\) is even, attaining zero forces every sign deterministic and balanced, since any nondeterministic sign permits two different sums in the product support. If \(m\) is odd, attaining one forces at most one nondeterministic sign (two would permit sums differing by four), and all other signs must be balanced when there is one. The completely deterministic minimizers are the two adjacent balances with sums \(\pm1\), which also belong to these one-free-coordinate faces. Thus the first-order maximum of \(C_1\) is \(k p^{m-2}a^2\). For even \(m\) it has just the balanced configurations; for odd \(m\) it has the faces with \(2k\) balanced fixed half-lines and one free function of mean \(p\).

## 3. Optimizing the second order and stability

For fixed half-lines \(v_i=0\). The fourth elementary symmetric polynomial of \(2k\) balanced numbers \(\pm a\) is \(\binom{k}{2}a^4\), since their generating product is \((1-a^2 z^2)^k\). In the odd case the extra \(u_i\) can multiply only the third elementary symmetric polynomial of the fixed numbers, which vanishes. Hence the last term in (2) is the same as in the even case, with the corresponding \(p^{m-4}\). The first term is zero, and the shared-vertex term is zero except, for odd \(m\), at the one free coordinate \(i\), where its contribution is \(-k p^{m-3}a^2 v_i\).

Under the fixed mass constraint, the unique minimizer of \(v_i\) is the central interval of mass one half, by choosing the smallest \(y^2-1\) values. Integration by parts gives its value \(-2c\varphi(c)\); its first moment is zero. In particular the deterministic endpoints of the first-order faces do not maximize \(C_2\) in the odd case. This proves the stated second coefficients **on** the first-order optimizer set.

Here are the compactness and rate checks needed to pass to the supremum in (1). The feasible tuples are weak-* compact in the product of the unit balls of \(L^\infty(\gamma)\); the positivity and mean constraints are weak-* closed. The ball is sequentially compact here since \(L^1(\gamma)\) is separable. The moments in (2) are weak-* continuous. A family within \(o(r^2)\) of the supremum has first-order deficit \(O(r)\), because (2) is uniformly bounded and the indicated test family gives the lower bound. Every accumulation point therefore maximizes \(C_1\). Dividing the expansion by \(r^2\) after subtracting the known constant and maximal first-order term shows that this point also maximizes \(C_2\) on that set: the nonnegative first-order deficit can only reduce the probability. Its limiting functions are the indicators above, by the first- and second-moment strictness conditions. Weak-* convergence to an indicator for \([0,1]\)-valued functions implies \(L^1\) convergence to it by integrating on the set and its complement. The possible optimal indicator tuples form a finite family up to permutation, yielding the claimed distance conclusion. This argument alone would give an \(o(r^2)\) remainder for the optimal value.

To sharpen to \(O_m(r^3)\), work with families within \(o(r^3)\) of the supremum. The compactness conclusion implies that, for small \(r\), their half-line coordinates are uniformly close to their designated extremal first moments (relabel if necessary), and in the odd case the remaining first moment is bounded away from \(\pm a\). Let \(\Delta=C_1^*-C_1\). In this neighborhood the sum of the first-moment deficits of the designated half-line coordinates is \(O_m(\Delta)\). To see this directly with the independent signs above, their probability of all having their designated signs except one is bounded below by a constant times that one's error probability. In even arity such a single error gives a squared sum at least four. In odd arity, on each such event the free sign has probability bounded below of making a sum of absolute value three, since both of its values have probabilities bounded away from zero. Sum over the disjoint single-error events and use the formula for \(C_1\).

For a designated half-line \(H\), its first-moment deficit is \(\int |y|\,|f(y)-{\bf1}_H(y)|d\gamma\). Since the two masses agree, its error in the second centered Hermite moment is bounded by \(\int y^2|f-{\bf1}_H|d\gamma\), at most a constant times the square root of the first-moment deficit by Cauchy–Schwarz with the integrable third absolute Gaussian moment. Replace all designated moments in \(C_2\) by their limiting half-line moments while leaving the free coordinate as is; the change is \(O_m(\sqrt{\Delta})\). On the resulting face \(C_2\le C_2^*\), as already proved. The varying first- and second-order terms therefore exceed their claimed values by at most
\[
 -r\Delta+O_m(r^2\sqrt{\Delta})=O_m(r^3)
\]
by completing the square in \(\sqrt{\Delta}\). The uniform Taylor remainder and an asymptotically exact maximizing family give the upper bound in (1). The explicit test tuple gives its lower bound.

## 4. Strict failure of all-half-line optimality at every negative strength in odd arity

First identify the best half-line tuples for every admissible \(r>0\). The covariance is \((1+r)I-r{\bf1}{\bf1}^{\mathsf T}\), whose inverse is a positive scalar identity plus a **positive** multiple of \({\bf1}{\bf1}^{\mathsf T}\). Thus its density is proportional to a product of univariate Gaussian densities times \(\exp[-b(\sum y_i)^2]\) for some \(b>0\). On any orthant, integrate the product densities first in the magnitudes, obtaining a common constant times
\[
 \mathbb E \exp[-b(S_j-S_{m-j})^2],
\]
where each sum uses independent half-normal magnitudes of that common variance. Suppose the larger sign group has at least two extra magnitudes. Couple a balanced collection of pairs from the other group into a symmetric log-concave variable \(D\), the sum of independent differences of half-normal variables (or zero when there are no pairs). The function \(F(x)=\mathbb E e^{-b(D+x)^2}\) is even and log-concave by Prékopa, real analytic and tends to zero, hence strictly decreases with \(|x|\). For the remaining unpaired nonnegative magnitudes \(T,A,B\) (with \(T\) a sum or zero), compare \(F(T+A+B)\) to \(F(T+A-B)\). The latter is strictly larger almost surely, since \(|T+A-B|<T+A+B\) for these positive magnitudes. This is exactly flipping one sign towards balance. Thus the best orthants have the sign groups as equal as possible.

For odd \(m\), remove one coordinate from the larger group in such a best tuple. The remaining \(m-1\) half-lines are balanced. Their joint conditional probability \(g(y)\), given that the removed coordinate is \(y\), is even (exchange the two balanced groups and reflect), and log-concave in \(y\) because it is the probability of a fixed convex orthant under a Gaussian with fixed positive definite covariance and mean \(-ry{\bf1}\). It is positive, real analytic, and tends to zero as \(|y|\to\infty\), since at least one requirement then faces a diverging mean in the wrong direction. Thus \(g\) strictly decreases with \(|y|\). Analyticity in both uses of this argument follows from dominant Gaussian integrability on each bounded range of the real or complex shift; strictness follows because a plateau of an analytic nonconstant function is impossible, and even log-concavity first gives nonincrease. The integral of \(g\) over a set of standard Gaussian mass \(1/2\) is therefore strictly larger for the central interval \([-c,c]\) than for either half-line. This constructs a strict improvement over every all-half-line tuple at every \(0<r<1/(m-1)\). It does not prove the exact optimizing sets at a fixed nonzero \(r\).

**Replay.** Run `python3 verify-simplex-repetition.py` for exact checks of the regular-simplex covariance, the first-order face classification over a rational grid, and the grouping of second-order edge pairs and its constants. The comparison and asymptotic proof are analytic.
