# Gaussian rounding when the center is unavailable

A known real center can be used to define a discrete Gaussian directly. A different experiment, used in statistical discretization, starts with an ordinary Gaussian observation and supplies the observation, but not the mean, to a fixed randomized rounding rule. We prove an obstruction that applies to **every such rule**, and construct rules whose error uniformly beats ordinary Gaussian rounding on the line. These are statements about comparing two abstract probability experiments. They do not address real or contest instances, finite arithmetic, or a new reduction.

We use actual variances and covariance matrices, not widths scaled by \(2\pi\).

## 1. No exact center-blind rule, and a quantitative obstruction

Let \(\Lambda\subset\mathbb R^d\) be a full-rank lattice, and let \(S,T\) be real positive definite matrices. Write \(P_c=\mathcal N(c,S)\) and let \(Q_c\) be the law on \(\Lambda\) with
\[
 Q_c(y)=\frac{g_T(y-c)}{\Theta_T(c)},\qquad
 g_T(z)=\exp(-z^\mathsf{T}T^{-1}z/2),\qquad
 \Theta_T(c)=\sum_{v\in\Lambda} g_T(v-c).
\]
The input \(X\sim P_c\), but not the deterministic parameter \(c\), is given to one Markov kernel \(K\) with outputs in \(\Lambda\). Let
\[
 \Delta(S,T,\Lambda)=\inf_K\,\sup_{c\in\mathbb R^d}
       \|K P_c-Q_c\|_{\rm TV}.
\]
There is no assumption of equivariance, computability or additive independent noise.

**Theorem 1.** Exact equality cannot hold for every center in any nonempty open subset of the real center space. Moreover, take any \(v\in\Lambda\), \(\xi\in\Lambda^*\) with \(\xi^\mathsf{T}v\) odd, and set
\[
 w=\pi T\xi,\quad B=v^\mathsf{T}T^{-1}v/8,\quad
 D=w^\mathsf{T}T^{-1}w/2,\quad C=D+w^\mathsf{T}S^{-1}w/2,
 \quad Z=\log\Theta_T(0)+B-D.
\]
Then
\[
 \Delta(S,T,\Lambda)
 \ \ge\ \exp\{-2C-Z-2\sqrt{C(C+Z+\log 2)}\}>0.                 \tag{1}
\]
The pair \(v,\xi\) can always be chosen from any lattice basis and its dual. The impossibility also holds for any fixed finite number \(m\) of independent observations with the same covariance, and (1) then applies with \(S/m\) in place of \(S\).

**Proof.** The probability \(F(c)=(K P_c)(0)\) extends to an entire function of complex \(c\). The modulus of the shifted Gaussian density at \(c=x+i u\) is its real-\(x\) density times \(\exp(u^\mathsf{T}S^{-1}u/2)\); the integrand is bounded locally in \(c\) by an integrable Gaussian envelope, since \(K(0|z)\in[0,1]\). Thus
\[
 |F(x+i u)|\le e^{u^\mathsf{T}S^{-1}u/2}.                     \tag{2}
\]
Similarly \(\Theta_T\) is entire and
\[
 |\Theta_T(x+i u)|\le
 e^{u^\mathsf{T}T^{-1}u/2}\Theta_T(x)
 \le e^{u^\mathsf{T}T^{-1}u/2}\Theta_T(0).
\]
The last inequality follows from Poisson summation, whose dual coefficients for \(\Theta_T\) are positive. There is a zero at \(z_0=v/2+iw\). In the absolutely convergent sum at that point, pair the lattice sites \(y\) and \(v-y\). Their positive real magnitudes agree, while the phases are
\(\exp(\pm i\pi \xi^\mathsf{T}(y-v/2))\); these sum to zero since \(\xi^\mathsf{T}y\) is integer and \(\xi^\mathsf{T}v\) is odd. No site is fixed by the pairing (a fixed site would give an even pairing). The numerator of \(Q_{z_0}(0)\), however, is a nonzero exponential.

Thus \(G(z)=\Theta_T(z)F(z)-g_T(-z)\) is entire and \(G(z_0)\ne0\). If exact equality held on a real open set, \(G\) would vanish identically by applying the one-variable identity theorem to the coordinates successively, starting with a real open box. This proves nonexistence even without uniformity outside that box.

For the quantitative claim let \(\varepsilon=\sup_c\|K P_c-Q_c\|_{\rm TV}\), and put \(M=\Theta_T(0)\). Consider \(G(v/2+\zeta w)\) on \(0\le\operatorname{Im}\zeta\le a\) for any \(a>1\). On the real edge \(|G|\le M\varepsilon\), by the event \(y=0\). On the other edge \(|G|\le 2M e^{a^2 C}\), since \(M\ge1\). The same estimates show boundedness in the whole strip. At \(\zeta=i\) the modulus is \(e^{D-B}\). The three-lines inequality gives
\[
 -\log\varepsilon
 \le \frac{a^2 C+aZ+\log 2}{a-1}.
\]
Write \(s=a-1\); the right side is \(2C+Z+Cs+(C+Z+\log2)/s\). The last numerator is positive, since \(C-D>0\), \(M\ge1\) and \(B\ge0\). Minimizing in \(s\) proves (1) for every \(K\). Finally, for the finite sample version the mean has covariance \(S/m\) and the Gaussian centered residuals are independent of it, with a law not depending on \(c\); they can be incorporated into the rule's private randomness. There is no claim here about an unbounded sampling experiment.

## 2. A better uniform exponent in dimension one

Set \(\Lambda=\mathbb Z\), target variance \(t^2\), input variance \(\rho t^2\), with fixed \(0<\rho<1\) and \(t\to\infty\). Define
\[
 b=1-\rho,\qquad r^2=b t^2,\qquad a=e^{-2\pi^2t^2}.
\]
Let \(\phi_u(x)=(2\pi u^2)^{-1/2}e^{-x^2/(2u^2)}\) and let \(V_u(x)=\sum_{k\in\mathbb Z}\phi_u(x-k)\). In particular the target mass \(Q_c(k)\) is \(\phi_t(c-k)/V_t(c-k)\). An even nonnegative function \(w\) on the line with \(\sum_k w(x-k)=1\) is a rounding rule \(K(k|x)=w(x-k)\). With \(s=\sqrt\rho\,t\), its mass at output \(k\) is \((\phi_s*w)(c-k)\).

Ordinary Gaussian randomized rounding uses \(w_{\mathrm G}=\phi_r/V_r\). Its worst-center total-variation error has exactly the exponential order \(a^{1-\rho^2}\), that is, it is bounded above and below by fixed positive multiples of \(a^{1-\rho^2}\) for large \(t\). For comparison, the following kernel has **strictly larger exponent**, uniformly in the unknown center.

**Theorem 2.** For every fixed \(0<\rho<1\) and \(0<\delta<1/2\), there is a rule with worst-center error \(O(a^{E(\rho,\delta)})\), where
\[
 E(\rho,\delta)=\min\left\{1,\ 
        b[1-\delta^2+\rho(1+\delta)^2],\ b(2-2\delta)\right\}.   \tag{3}
\]
For some \(\delta\) this is strictly above \(1-\rho^2\), for **every** \(0<\rho<1\). When \(0<\rho<1/4\), one can instead obtain the exponent \(2-4\rho>1\). All constants are for fixed shape; no claim is made that these are the optimal exponents.

**Proof.** Introduce the unnormalized function
\[
 w_0(x)=\phi_r(x)
   [1-2a^{b(1-\delta^2)}\cos(2\pi(1+\delta)x)],\qquad
 W_0(x)=\sum_{k\in\mathbb Z}w_0(x-k).
\]
For sufficiently large \(t\) it is positive. Then \(w=w_0/W_0\) is nonnegative and has the exactly required partition, because \(W_0\) is periodic. We bound the effect of this normalization before comparing outputs.

Use the Fourier transform \(\widehat f(\eta)=\int f(x)e^{-2\pi i\eta x}\,dx\). The integer Fourier coefficients of \(W_0\) are
\[
 \widehat w_0(j)
  =a^{b j^2}
  -a^{b(1-\delta^2)}\left[
       a^{b(j-1-\delta)^2}+a^{b(j+1+\delta)^2}\right].
\]
At \(j=1\) the first term cancels the nearby translated term exactly; the remaining exponent is \(b(5+4\delta)\). At \(j=0\) the error from 1 is \(-2a^{b(2+2\delta)}\). At \(j\ge2\) the exponent of the nearer term is \(b[1+(j-1)^2-2\delta(j-1)]\), minimized at \(j=2\), where it is \(b(2-2\delta)\); the other two terms have no smaller exponent. Negative indices follow by symmetry. The series is absolutely convergent, with a Gaussian tail, so
\[
 \|W_0-1\|_\infty=O(a^{b(2-2\delta)}).                          \tag{4}
\]
In particular the normalized and unnormalized nonnegative functions differ by a relative \(O(a^{b(2-2\delta)})\) pointwise.

Completing the square in the convolution of \(\phi_s\) and \(\phi_r\) gives
\[
 (\phi_s*w_0)(c)=\phi_t(c)
   \left[1-2a^{b(1-\delta^2)+\rho b(1+\delta)^2}
          \cos(2\pi b(1+\delta)c)\right].                      \tag{5}
\]
Indeed the posterior argument of the cosine has mean \(b c\) and variance \(\rho b t^2\). On the other hand \(1/V_t(c)=1+O(a)\) uniformly, by its integer Fourier series. The output change from (4) is bounded by the same relative order times the expression in (5); summing over \(c-k\) preserves its order because \(\sum_k\phi_t(c-k)=V_t(c)\) is uniformly bounded. This gives (3). At \(\delta=0\) the middle exponent is \(1-\rho^2\); its derivative there is \(2\rho b>0\). The other two exponents are both strictly larger there. Thus a sufficiently small strictly positive \(\delta\) suffices, for example \(\delta=\min\{b/4,\rho\}\); for that choice \(b(2-2\delta)>b(1+\rho)\) and the increase in the middle exponent is \(b(2\rho\delta-b\delta^2)>0\).

If \(\delta=\rho/b\) and \(\rho<1/4\), then the exponent in (5) is exactly 1 and its cosine frequency is exactly 1. Thus (5) agrees with \(\phi_t(c)[1-2a\cos(2\pi c)]\), the first-order expansion of \(Q_c(0)\), with relative target remainder \(O(a^2)\). The normalization error (4) is \(O(a^{2-4\rho})\). This proves the stated stronger guarantee.

For the ordinary Gaussian kernel,
\[
 w_{\mathrm G}(x)/\phi_r(x)=1-2a^b\cos(2\pi x)+O(a^{2b})
\]
uniformly. Convolution and (5)'s completion formula, now with an unshifted carrier, give apparent leading correction \(-2a^{b+\rho b}\cos(2\pi b c)\) in the output, with relative error \(O(a^{2b})\); the target's relative correction is \(O(a)\). Both remainder exponents are strictly larger than \(b+\rho b=1-\rho^2\). At center zero the leading TV coefficient is bounded away from zero: \(\sum_k\phi_t(k)|\cos(2\pi b k)|\ge \sum_k\phi_t(k)\cos^2(2\pi b k)\ge1/2\). For the last inequality, the first half of the cosine-square expansion contributes \(V_t(0)/2\ge1/2\), and the second half is nonnegative by Poisson summation at a real shifted frequency. The upper bound follows from the same uniform expansion. This shows that the improvement is not just an improvement of a loose bound on that rule.

## 3. An independent Fourier lower bound on the line

Keep the scaling of Section 2. The explicit bound (1) works in every dimension and at every finite scale. Here a different argument yields a simpler exponent bound in dimension one. Put
\[
 j=\lfloor1/\rho\rfloor,\qquad
 \xi_*=\frac{j-\sqrt{j(\rho(j+1)-1)}}{1-\rho}.
\]
Then \(j\le\xi_*<j+1\), and
\[
 \limsup_{t\to\infty}
 \frac{-\log\Delta(\rho t^2,t^2,\mathbb Z)}{2\pi^2t^2}
 \ \le\ \rho\xi_*^2.                                         \tag{6}
\]
Equation (6) is an upper bound on the attainable exponent, not a sharp minimax claim. In particular the constructive and converse exponents need not coincide.

We may restrict the infimum to integer-translation-equivariant kernels even though none was assumed in the definition. To prove this, let a kernel have uniform error at most \(\varepsilon\) and average its integer shifts:
\[
 K_L(k|x)=\frac1{2L+1}
       \sum_{h=-L}^{L}K(k+h|x+h).
\]
Every average has error at most \(\varepsilon\) since the input and target families translate covariantly. For each output \(k\), the functions \(K_L(k|\cdot)\) lie in the unit ball of \(L^\infty(\mathbb R)\). That ball is sequentially compact in the weak-* topology because \(L^1\) is separable. A diagonal subsequence gives nonnegative limits \(u_k\) with \(\sum_k u_k(x)\le1\) almost everywhere, as can first be checked on finite sets. For any fixed integer shift, changing that many endpoint terms of the Cesàro average changes it by \(O((2L+1)^{-1})\), giving \(u_k(x)=u_0(x-k)\) almost everywhere. All pairs of integers may share a single exceptional null set.

These limits define a subprobability-valued kernel. For every \(c\) and every finite collection of outputs the error bound survives, since the input density is an \(L^1\) test function. The target-positive deficits \(Q_c(k)-(u P_c)(k)\) sum to at most \(\varepsilon\) over the indices where they are positive, by monotone exhaustion of finite sets. Fill the missing mass \(1-\sum_k u_k(x)\) with the deterministic nearest-integer kernel (choose one consistent tie convention), preserving equivariance almost everywhere. This decreases positive deficits and makes the output a probability, so its total variation is no more than \(\varepsilon\). Values on a null set do not affect any \(P_c\).

Let \(w(x)\ge0\) be the resulting equivariant kernel's probability of output zero. Its translates partition the line; integration over a unit interval therefore gives \(\int_{\mathbb R}w=1\). Set \(F=\phi_{\sqrt\rho t}*w\) and \(p_t(c)=\phi_t(c)/V_t(c)\). Integrating the uniform TV bound on \(0\le c\le1\) and summing over all integer outputs gives \(\|F-p_t\|_1\le2\varepsilon\). Hence for every frequency \(\xi\),
\[
 2\varepsilon \ \ge\
     |\widehat p_t(\xi)|-a^{\rho\xi^2},                       \tag{7}
\]
since \(|\widehat w|\le\int w=1\).

We calculate the leading term of \(\widehat p_t(\xi)\) away from the integer frequencies, where cancellation can occur. Write
\[
 \frac1{V_t(c)}
   =\sum_{u\in\mathbb Z}d_u(a)e^{2\pi iuc}.
\]
For each fixed integer \(u\), \(d_u=(-1)^{|u|}a^{|u|}(1+O_u(a))\). Indeed, expand the reciprocal of \(\sum_v a^{v^2}z^v\) near \(a=0\), with \(z=e^{2\pi ic}\). In the formal coefficient of \(z^u\) the minimum possible power is \(|u|\), since any list of nonzero steps adding to \(u\) has sum of squared step lengths at least \(|u|\). Equality uses only steps of size 1 and the same sign, giving exactly the displayed coefficient. The expansion is convergent for small \(a\) on the unit circle. For a uniform bound in \(u\), the same Laurent series for \(V_t\) differs from 1 by at most \(1/2+O(a^2)\) on the two circles \(|z|=2a,(2a)^{-1}\) and throughout the annulus for small \(a\). One can bound this directly by the absolute sum, whose maximum is at an endpoint of the log-radius interval. Cauchy's formula on these circles gives \(|d_u|\le C(2a)^{|u|}\).

Consequently
\[
 \widehat p_t(\xi)=\sum_{u\in\mathbb Z} d_u(a)\,a^{(\xi-u)^2}.
\]
At fixed \(\xi\in(i,i+1)\), \(i\) a nonnegative integer, \(|u|+(\xi-u)^2\) has its unique minimum at \(u=i\), by comparing consecutive nonnegative \(u\) and noting that negatives are larger. The uniform Laurent coefficient bound and the quadratic tail give
\[
 \widehat p_t(\xi)=(-1)^i\,a^{i+(\xi-i)^2}(1+o(1)).
\]
For \(i\ge1\), the ratio \([i+(\xi-i)^2]/\xi^2\) is strictly decreasing from \(1/i\) to \(1/(i+1)\) across that interval, as direct differentiation shows. It is 1 on \((0,1)\). The first interval with ratio strictly below \(\rho\) is therefore \((j,j+1)\), including the case \(1/\rho=j\) where the strict inequality starts just to the right of \(j\). Its crossing is \(\xi_*\). For each fixed \(\xi\in(\xi_*,j+1)\) the leading term in (7) dominates \(a^{\rho\xi^2}\), giving \(\Delta\ge(1/2+o(1))a^{j+(\xi-j)^2}\); this holds because (7) was uniform over kernels. Take the upper exponent limit and then let \(\xi\downarrow\xi_*\). This proves (6) without using the expansion at an integer.

## 4. Relationship to existing results and replay

[Peikert, *An Efficient and Parallel Gaussian Sampler for Lattices*, Theorem 3.1 and §4.1](https://web.eecs.umich.edu/~cpeikert/pubs/pargauss.pdf) proves statistical validity of Gaussian randomized rounding under a flatness hypothesis. [Lyubashevsky–Peikert–Regev, *A Toolkit for Ring-LWE Cryptography*, §2.4.2](https://sites.cc.gatech.edu/fac/cpeikert/pubs/toolkit.pdf) uses such rounding as a positive discretization step. [Luzzi–Ling–Bloch](https://opencryptology.org/2022/808) investigate flatness and randomized rounding including a dithered regime. Those sufficient bounds do not require the universal rounding question above. The [posterior-heat analysis](gaussian-rounding-posterior-heat.md) in this repository concerns the *specified* Gaussian kernel; the matching exponent used here for comparison is reproved in Section 2. Exactness at a special single known/selected center is consistent with Theorem 1, which has a real-open-set or global quantifier.

[Agostini–Améndola, *Discrete Gaussian Distributions via Theta Functions*, Definition 2.3](https://arxiv.org/abs/1801.02373) identify the complex theta divisor as the singular locus of the normalization. Its elementary half-period zero is not a new theta-function result. Here that zero is used with the entire-function growth of a Gaussian statistical experiment to obstruct arbitrary postprocessing, not merely Gaussian-shaped rules. The comparisons permit arbitrary internal randomness but do not claim the best finite-bit implementation or an implication about a concrete cryptographic construction.

Run `python3 verify-center-blind-gaussian-rounding.py` with mpmath for exact exponent checks and high-precision synthetic comparisons. The proofs and quantifiers are not based on numerical fitting.
