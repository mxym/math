# Independent analytic audit of the semiconvex Gaussian entropy comparison

Date: 7 October 2026

## Verdict

The main entropy comparison, conditional extension, sharpness claims, finite quartic counterexample, and threshold obstruction survive this independent written-proof audit under the hypotheses actually displayed in Theorem 1.1. I found no missing main-theorem hypothesis and no failed argument in the adaptive observations, comparison of minima, or ordered limits.

The submitted manuscript is not literally correct as a whole: Lemma 3.1 omits the nonnegative domain restriction on its square-exponential parameter. Its last clause must say 0 <= theta < a/2. The uncorrected clause is false for negative theta, with an exact Gaussian counterexample below. This is a genuine statement correction, but every downstream application already uses strictly positive theta < a/2. It does not weaken or alter Theorem 1.1.

The original six files remain unchanged. A separate one-line unified patch and corrected TeX copy are included. This audit is an analytic review with independent exact supporting calculations. It is not complete Lean verification, certification of priority, or an endorsement of journal level.

## 1 Provenance and frozen inputs

The original six-file submission was frozen before review. Its exact lengths and SHA-256 hashes are recorded below. The release preserves both the original mathematical TeX and the separately corrected TeX, and unchanged original and independent checkers. Administrative delivery files are represented by hashes only. Public release edits beyond the helper-domain correction affect the abstract, source-section title, and verification/scope prose only; the theorem, conditional statement, lemmas, and proofs are unchanged.

The six original files match the frozen byte counts and SHA-256 hashes:

- entropy.tex: 29712 bytes, fcc5e043e333b922a13e3b36c7a1e660d92c50210f240b2b634b568440c25a48
- check_exact.py: 10037 bytes, a2d7c72910b2f21ea45a9b01935fbd09b2f9769e29a6df494da778dd91dae643
- fetch_sources.py: 1475 bytes, 80463a66d14cd5e29129a9bdf1bc3c3ec3a5f7ec74853b5c8ac2a5ab313af76e
- sources.json: 1198 bytes, 1a45eab3feb1795d19be05c565a41ec67d6a97b793e4df4a21fd3cd87a7485a1
- verification.json: 2369 bytes, 562f508a5a43389e56edccfc164edf75b9d523733fffa334db6716d33cceb5c3
- README.md: 2829 bytes, aa9588f3d6b9fea3823ca1d76aa996f4810dd8e3cebee1bdf2c310aac45dc3ce

No original input was edited. The corrected TeX has SHA-256 362bdb991e3ee44ad5c52d43301d7834d7e246146e74f70c78120a294a6dd16c. The minimal patch has SHA-256 744d7be5b7651216e29495f8258f30ab58ee80aa1431bf798ca60d1813cf2cb5.

## 2 Exact helper-lemma counterexample and correction

The last clause of the original curvature lemma, entropy.tex line 160, reads

E exp(theta |X|^2) <= (1 - 2 theta/a)^(-k/2), with only 2 theta < a.

Take dimension k=1, a=1, pi=N(0,1/2), and theta=-1. This pi is smooth, positive, and its potential has Hessian 2 >= a. The centered signal is X itself. Direct Gaussian integration gives

E exp(-X^2) = 1/sqrt(2),
(1 - 2 theta/a)^(-1/2) = 1/sqrt(3).

The proposed upper bound is therefore false. Squaring compares the exact rational numbers 1/2 > 1/3, so no decimal approximation is involved.

The minimal correction is to replace the parenthetical domain by 0 <= theta < a/2. For theta >= 0, the Gaussian-averaging proof is valid: E_G exp(sqrt(2 theta) G dot X) = exp(theta |X|^2), and the linear subgaussian bound integrates to the stated Gaussian determinant. Theta=0 is immediate.

The downstream inventory is complete:

- Lines 218-221 are the derivation of the corrected clause itself and require theta >= 0.
- Line 232 defines theta=min{c/16,a/4}.
- The main theorem assumes c>0, and its proof chooses a=1/z-kappa>0.
- Thus 0<theta<=a/4<a/2 and 8 theta<=c/2.
- Lines 233-255 use precisely this theta for the reference exponential-square bound and the alternative conditional moment estimate.
- Lines 268-273 use the same positive theta to divide by theta and control the chi-square remainder.
- Line 299 refines the mesh until delta=u/m<=theta.
- There are no later square-exponential applications with a different or negative parameter.

The files square_exponential_domain.patch and entropy.corrected.tex contain this correction only.

## 3 Meaning and scope of the theorem

Let w=grad log(p/q), I=E_p |w|^2, H_r=D(p*N(0,rI) || q*N(0,rI)), and

J(r)=E_p |E_p[w(Y) | Y+sqrt(r)G]|^2.

J is the prediction energy of the initial relative score. It is not generally the relative Fisher information of the smoothed densities. The proof never identifies these two quantities, differentiates H_r through an unjustified de Bruijn equality, or assumes pointwise Fisher contraction.

The precise conclusions are

2(H_0-H_z) <= integral_0^z J(r)/(1-kappa r)^2 dr
           <= (1-kappa z)^(-1) integral_0^z J(r) dr

for kappa>=0 and z<1/kappa, with every z>0 allowed at kappa=0. The displayed hypotheses are smooth positive probability densities, Hess(-log q)>=-kappa I, finite H_0 and I, and an exponential-square moment under p for some positive parameter c.

This is an entropy-loss comparison, not an inequality bounding H_0 alone and not a general non-log-concave logarithmic Sobolev inequality. The finite positive horizon is essential for a uniform curvature-only scalar factor.

## 4 Positive-curvature input

Set pi=Z^(-1) exp(-V), with Hess V>=S>0. The change of variables y=S^(1/2)x gives Hess_y V>=I and changes the score energy into the quadratic form with S^(-1). No direction of the matrix inequality is reversed.

For S=I, write V=|x|^2/2+U with U convex. The bounded-Hessian case has globally Lipschitz drift for the diffusion dX=sqrt(2)dB-grad V dt. Its trajectory derivative satisfies dA/dt=-Hess V A, giving operator norm at most exp(-t). Weighted Cauchy-Schwarz gives the Fisher-gradient bound for P_t g. Integrating its entropy dissipation, and using the contractive coupling with a stationary trajectory to establish convergence, gives Ent_pi(g)<=1/2 integral |grad g|^2/g.

The approximation step is appropriate for the stated smooth finite convex U:

- Moreau envelopes are finite, convex, have Lipschitz gradient, and increase pointwise to U.
- A fixed affine lower bound on U gives a common affine lower bound on the envelopes.
- Centered compact mollification preserves that bound and bounded Hessian.
- Choosing the mollification radius to make the local error at most 1/j on the ball of radius j preserves pointwise convergence.
- All resulting normalized densities are dominated by a fixed Gaussian times a linear exponential.
- Compact-test entropy and energy pass by dominated convergence.
- For f=sqrt(rho/pi), cutoffs converge in L2 and in energy. The cutoff-gradient term is bounded by a constant times R^(-2) integral f^2, and the cross term vanishes by Cauchy-Schwarz.
- Entropy lower semicontinuity follows from its variational formula, after normalization of the cutoff squares.

This establishes 2D(rho||pi)<=E_rho <grad log(rho/pi),S^(-1) grad log(rho/pi)> for finite-energy rho, including the posterior densities used later. No unproved nonsmooth-prior extension is required here.

For S>=aI, linear exponential tests give the usual centered subgaussian moment bound. Gaussian tails justify the truncation and differentiation used for the covariance estimate. The square-exponential bound follows only on the corrected nonnegative domain.

## 5 Averaged matching-means entropy cost

The cost lemma is valid as an averaged estimate; it does not claim a uniform pointwise bound in the retained history.

Fix D=Nn and a retained history H. Let Q be an H-measurable orthogonal projection that kills the difference of posterior means. Subtract the common projected mean. Under each posterior, X is then centered in ran Q.

The reference posterior has curvature at least aI, so for theta=min(c/16,a/4),

E_q exp(theta |X|^2) <= (1-2theta/a)^(-D/2),
E_q |X|^2 <= D/a.

The use of D rather than the actual rank of Q only enlarges the bound. For the alternative, with m=E_p[Ybold|H],

|Q(Ybold-m)|^2 <= 2|Ybold|^2+2|m|^2.

Conditional Jensen first gives

E_p[exp(theta |X|^2)|H]
 <= (E_p[exp(2theta |Ybold|^2)|H])^2.

Another conditional Jensen inequality, followed by averaging, gives

E_H (E_p[exp(theta |X|^2)|H])^2
 <= E_p exp(8theta |Ybold|^2)
 = (E_p exp(8theta |Y|^2))^N < infinity.

These estimates apply to every conditioning sigma-field and therefore require no mesh-uniform posterior-tail assumption.

For h the density of sqrt(delta)X+G in ran Q and phi standard Gaussian there, exact Gaussian integration gives

chi^2(h||phi)=E exp(delta X dot X')-1,

where X' is conditionally independent with the same centered law. The linear term vanishes. Using |exp(t)-1-t|<=t^2 exp(|t|)/2, |X dot X'|<= (|X|^2+|X'|^2)/2, and

s exp(delta s/2) <= (2/theta) exp(theta s), 0<delta<=theta,

bounds this chi-square divergence by

(2 delta^2/theta^2) (E exp(theta |X|^2))^2.

There is no hidden requirement of a fourth moment of w. All moment demands are on Y, as explicitly assumed.

For the reference output, conditional Jensen yields the pointwise likelihood lower bound

h_q(x)/phi(x)>=exp(-delta D/(2a)).

Consequently

D(h_p||h_q)
 <= chi^2(h_p||h_q)
 <= 2 exp(delta D/(2a))
       [chi^2(h_p||phi)+chi^2(h_q||phi)].

After averaging, this is bounded by the manuscript's explicit C_(N,a,p) delta^2. Its constant is finite at fixed N,a,p, independent of the mesh and controls, and is not asserted to be bounded uniformly in N. The zero-dimensional output costs zero.

As a separate independent diagnostic, the checker expands the exact divergence between centered Gaussian outputs with variances 1+delta s_p and 1+delta s_q. Its linear coefficient is zero and its quadratic coefficient is (s_p-s_q)^2/4. This confirms the cancellation in a simple family but is not used to replace the general proof.

## 6 Adaptive likelihood and posterior curvature

Fix z in the permitted range, b=1/z, and a=b-kappa>0. The first full observation has precision bI. At step i, the projection P_i onto the difference of posterior means is chosen as a measurable function of the retained past. Q_i=I-P_i, and the retained observation is Q_i(sqrt(delta)Ybold+G_(i+1)).

A measurable frame in ran Q_i gives ordinary conditional Gaussian kernels even when the rank changes. Given a realized retained history, the control choices are already determined. Each observed Gaussian kernel contributes its normal likelihood factor; the deterministic choice of the control contributes no additional likelihood ratio.

The likelihood as a function of the signal has precision

B=bI+delta sum_i Q_i.

It is common under both priors. Thus the relative posterior score remains exactly W=(w(Y_1),...,w(Y_N)), and the reference posterior Hessian is at least

B-kappa I=aI+delta sum_i Q_i.

This is the correct curvature quantity. Replacing it by B would silently assume log-concavity and would give the false unweighted extension.

Properness and reference Gaussian tails follow from the affine lower bound on the convex function -log q+kappa |y|^2/2 and the positive matrix B-kappa I. The positive smooth priors and Gaussian likelihoods give positive smooth posterior densities. Alternative means and posterior score energies are finite almost everywhere; their averaged energy is controlled by NI/a.

Entropy chain rules give remaining entropy N(H_0-H_z) after the first observation. Additional matching-means observations consume at most m C delta^2=C u delta in averaged relative entropy. Applying the anisotropic curvature bound to the final posterior therefore gives

2N(H_0-H_z)
 <= E <W,(B-kappa I)^(-1)W> + 2 C_(N,a,p) u delta.

All posterior and history entropies are finite in expectation because the original joint divergence is NH_0. This avoids undefined subtraction of infinite conditional entropy terms.

## 7 True and comparison minima

In the Hilbert space of square-integrable vector fields on the signal and the full observation array,

M=min_v {a ||W-v||_2^2+delta sum_i ||Q_i v||_2^2}
 =aNI-a^2 E<W,(B-kappa I)^(-1)W>.

The true minimizer is v_*=a(B-kappa I)^(-1)W, with norm at most sqrt(NI). This identity holds pointwise even though the matrices are adaptive.

Let F_i be the full observation sigma-field through step i and e_i conditional expectation onto F_i. The retained history is a function of the full past, so P_i is F_i-measurable. Replace Q_i by I-e_i to obtain M_0.

The nested conditional-expectation projections commute with one another, but no commutation with P_i is assumed. A component first entering ran(e_j-e_(j-1)) receives j penalties. With alpha_j=a/(a+j delta), the minimizer is

v_0=alpha_m W+sum_(k=0)^(m-1)(alpha_k-alpha_(k+1))e_k W.

Its residual g_i=(I-e_i)v_0 is a nonnegative weighted combination of W-e_iW and e_kW-e_iW for k>i. The weights sum to alpha_(i+1)<=1.

Conditioning on the full past conditions each independent signal/noise copy only on its own full past. This leaves the copy kernels conditionally independent. Hence the blocks g_(i,j) are conditionally centered and independent, even though they include future observations. The retained histories need not factor; the proof correctly does not use their independence.

Conditional Jensen and the tower property imply

Z_(i,j)=tr Cov(g_(i,j)|F_i)
 <= E[|W_j-e_iW_j|^2|F_i]
 <= E[|W_j|^2|F_i].

The last variables are uniformly integrable over every possible observation sigma-field. For an arbitrary nonnegative integrable Z and M=E[Z|F],

E[M 1_(M>K)] <= 2 E[Z 1_(Z>K/2)].

The manuscript's proof of this tail inequality is correct. Since conditional covariance is block diagonal and P_i has rank at most one,

E|P_i g_i|^2 <= E max_j Z_(i,j)
 <= K+2N E_p[|w|^2 1_(|w|^2>K/2)].

Defining tau_N as the infimum of K/N plus this tail term yields tau_N->0. The proof fixes K after controlling the tail, then sends N to infinity; it does not need a fourth moment of w or a uniform pointwise bound on w.

For every v,

||Q_i v||_2^2 >= 2<v,Q_i g_i>-||g_i||_2^2.

The normal equation a(W-v_0)=delta sum_i g_i makes the corresponding linearized unprojected quadratic attain minimum M_0 at v_0. Test the lower bound at v_* and use Cauchy-Schwarz. This gives

M >= M_0 - 2uN sqrt(I tau_N).

The sign, factor two, minimizer choice, and power of a in the ensuing entropy error all check out. Random coordinate projections are never interchanged with conditional expectations.

The independent checker tests this logic on two exact three-copy models, each with 4096 finite states, a nonzero score mean, biased prior/noise probabilities, and genuinely past-adaptive rank-one directions depending on multiple copies. It verifies the pointwise normal equation, true inverse identity, spectral identity, signed dual bound, conditional centering, covariance off-diagonal cancellation, and rank-one covariance estimate. This differs from the submitted two-copy checker. Its discrete noise validates finite Hilbert-space algebra only, not the continuous Gaussian cost lemma.

## 8 Sufficient statistic and all three limits

The spectral decomposition gives

M_0/N = sum_i [a^2 delta/((a+i delta)(a+(i+1)delta))]
                     [I-||e_i W_1||_2^2].

The coefficient telescope equals a j delta/(a+j delta), the exact minimized penalty of a component first predicted at j. Independent symbolic checks verify this identity.

The full Gaussian observation precision is b+i delta, not a+i delta. Its sufficient statistic is sqrt(b)Z_0+sqrt(delta) sum_(k=1)^i Z_k. Completing the square identifies a scalar Gaussian observation with noise variance 1/(b+i delta); orthogonal remaining noise coordinates carry no signal information. Thus

||e_i W_1||_2^2=J(1/(b+i delta)).

Combining the entropy, minimum, and dual estimates yields exactly the submitted prelimit bound:

2(H_0-H_z) <= I/(a+u)
 + sum_i delta J(1/(b+i delta))/((a+i delta)(a+(i+1)delta))
 + (2u/a^2)sqrt(I tau_N)
 + 2 C_(N,a,p) u delta/N.

Every coefficient and denominator is correct.

J is bounded between zero and I by conditional Jensen. It is nonincreasing in noise variance because a higher-noise output can be generated from a lower-noise output by adding independent Gaussian noise. This uses equality in distribution and a Markov coupling; it does not assume the originally named noises at different r are on a nested sigma-field. Gaussian conditional-density formulas supply measurability.

The mesh coefficient is exactly integral_(i delta)^((i+1)delta) (a+t)^(-2) dt. J(1/(b+t)) is bounded and monotone in t, so the left-endpoint weighted sums converge. No continuity assertion about J at zero is needed.

The limit order is indispensable and is honored:

1. At fixed N,u, send m to infinity, so delta=u/m goes to zero. The finite constant C_(N,a,p) may depend badly on N; nevertheless its entropy error vanishes in this first limit.
2. At fixed u, send N to infinity. The rank-one error vanishes because tau_N->0.
3. Send u to infinity. I/(a+u) vanishes and the nonnegative integral increases to a finite value bounded by I/a.

With r=1/(b+t),

(a+t)^(-2)dt = -(1-kappa r)^(-2)dr,

so the limiting integral is exactly the claimed weighted integral over (0,z). Positivity a>0 is what creates the stated horizon. No limit involving the number of copies is exchanged with the mesh limit, and no uniform-in-N entropy-cost bound is used.

## 9 Scalar comparison

The weighted comparison implies the scalar one because J decreases while g(r)=(1-kappa r)^(-2) increases. Integrating

(J(r)-J(s))(g(r)-g(s))<=0

over [0,z]^2 gives

integral Jg <= (integral J)(integral g)/z.

The integral of g is z/(1-kappa z), including kappa=0 by direct evaluation or limit. The direction of this inequality is correct. The scalar factor is not obtained by the coarser pointwise maximum of g, which would yield an unnecessarily squared factor.

## 10 Conditional extension

The global finite nonnegative entropy, energy, and exponential-square expectations imply one-label finiteness almost everywhere with the same positive c. Smooth conditional densities and joint measurability give measurable channel and score quantities. Apply the main theorem separately at each label, completing its three limits there, and only then integrate in the label.

Tonelli applies to the nonnegative right-hand sides, and the stated integrated score energy controls them. The noise is independent of (L,Y), as required. There is no need for a common mesh-error constant over labels and no impermissible interchange between label integration and the finite-copy construction. The stated common curvature bound kappa is essential for one common horizon and scalar factor.

## 11 Quartic family and finiteness

For p_t=N(0,t) and q_R proportional to exp(kappa x^2/2-x^4/R^4), each finite R,t is a proper smooth positive density. Its potential curvature is -kappa+12x^2/R^4>=-kappa. Under p_t, all polynomial score moments and relative entropy terms are finite. An exponential-square moment exists for c<1/(2t).

The initial relative score is

w_R(Y)=-(kappa+1/t)Y+(4/R^4)Y^3.

Gaussian moments give

I_R=A^2 t-24 A t^2/R^4+240 t^3/R^8, A=kappa+1/t.

Independently expanding the conditional Gaussian cubic moment and averaging its square verifies

J_R(r)=(A-3d_R t)^2 t^2/(t+r)+6 d_R^2 t^6/(t+r)^3,
d_R=4/R^4.

The derivative in r is nonpositive. The expression at r=0 equals I_R. The full conditional prediction therefore satisfies all consistency checks.

For smoothed q_R, finite entropy also follows directly, besides data processing: its density is bounded above by the Gaussian kernel maximum, while integration over a fixed compact interval supplies a lower bound of the form c_R exp(-C_R x^2). Its logarithm is integrable under the Gaussian p_(t+z). No example hides an infinite smoothed entropy.

## 12 Weighted and scalar sharpness

At z<1/kappa, the unnormalized convolution h_R tends pointwise to

h_infinity(x)=(1-kappa z)^(-1/2)
 exp(kappa x^2/[2(1-kappa z)]).

The tilted Gaussian identity is correct:

h_R(x)/h_infinity(x)=E exp(-T_x^4/R^4),
T_x~N(x/(1-kappa z), z/(1-kappa z)).

Jensen yields 0<=log h_infinity-log h_R<=E T_x^4/R^4. Averaging over X~N(0,t+z) gives 3T^2/R^4 with the manuscript's T. This explicitly justifies the entropy limit without using a nonnormalizable density as a probability. Z_R cancels from the difference at every finite R.

The entropy-difference identity is

2(H_0-H_z)=log(1+z/t)+2E log h_R(X)-kappa t+6t^2/R^4.

Its limit is

A_t(z)=log(1+z/t)-log(1-kappa z)
       +kappa z(1+kappa t)/(1-kappa z).

An independent symbolic derivative check gives

A_t'(z)=(1+kappa t)^2/[(t+z)(1-kappa z)^2].

Both quantities vanish at z=0, proving equality with the limiting weighted integral. J_R converges uniformly on [0,z] to (1+kappa t)^2/(t+r). The weighted ratio tends to one with finite proper approximants. This establishes optimality of the leading coefficient.

For the scalar constant, its limiting denominator is (1+kappa t)^2 log(1+z/t). For kappa>0 and large t, the numerator has leading term kappa^2 t z/(1-kappa z), and the denominator has leading term kappa^2 t z. Their ratio tends to (1-kappa z)^(-1).

The order is legitimate: choose finite large t first to approach the desired ratio, then finite large R to approximate its fixed-t limit. Each selected p has a positive exponential-square parameter; the theorem does not impose a uniform c over the whole class. For kappa=0 both limiting expressions equal log(1+z/t)>0, giving optimality of factor one.

## 13 Exact finite failure of the unweighted extension

The supplied finite counterexample is valid:

p=N(0,1), q proportional to exp(x^2/2-x^4/256), z=1/2.

Here kappa=t=1, R=4, T=7. The rigorously justified entropy lower bound is

2(H_0-H_(1/2)) >= log 3 +109/128.

The exact prediction integral is

(15625/4096) log(3/2)+5/12288.

Strict convexity of 1/x gives log 3>1 from the midpoint rule on [1,3], and log(3/2)<5/12 from the trapezoid rule on [1,3/2]. Therefore the gap is strictly greater than

237/128-78145/49152=12863/49152>0.

All arithmetic was independently reconstructed using exact rational numbers. No normalizing constant, numerical integration, or uncertified logarithm estimate is needed. The reference potential has second derivative -1 at zero, so it is genuinely non-log-concave.

A separate non-certified Gauss-Hermite diagnostic stabilizes near entropy loss 2.423050647731318 and prediction integral 1.5471335402482265, with actual gap about 0.87591710748309. These decimals are illustrative only and are not used in the certificate.

## 14 Threshold obstruction

At z>=1/kappa with kappa>0, symmetry gives

h_R(x)=exp(-x^2/(2z))/sqrt(2 pi z)
       integral exp((kappa-1/z)y^2/2-y^4/R^4) cosh(xy/z) dy.

On |y|<=R, the quadratic coefficient is nonnegative, the quartic exponential is at least exp(-1), and cosh is at least one. Thus

h_R(x)>=2R exp(-x^2/(2z))/(e sqrt(2 pi z)).

The entropy-difference identity then yields a lower bound growing as 2 log R. Meanwhile

integral_0^z J_R(r)dr <= z I_R
 <= z[A^2 t+240t^3]

for R>=1, uniformly in R. This proves that no finite C(kappa,z) controls the entropy loss by that prediction integral at the exact threshold or beyond it. It establishes failure in dimension one with proper finite-entropy, finite-energy examples and fixed Gaussian p_t.

The lower bound uses only a compact part of the convolution integral, so it remains valid even when other parts grow much faster. It is sufficient for divergence of the ratio and does not require asymptotic evaluation of Z_R.

## 15 Primary-source audit

All four public PDF pins were independently downloaded, their exact bytes and SHA-256 hashes matched, and the relevant primary passages were read.

1. OpenAI, A dimension-free logarithmic Sobolev inequality for subgaussian log-concave measures, 23 September 2026, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.
   PDF: 712415 bytes; SHA-256 767a5eb7cd819af7e33c8b867c41403aac36ec015c89c1d2beb186abca9ec89e.
   Lemma 2.1, pages 6-7, gives the positive-curvature input and convex approximation. Lemma 4.2, pages 22-25, has the same finite-observation hypotheses at kappa=0 and the full independent-copy/minimum/three-limit argument. The candidate is an explicit curvature-shift adaptation of that lemma, not a use of the source's later tensor or freezing results.
   Link: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-dimension-free-logarithmic-Sobolev-inequality-for-subgaussian-log-concave-measures-September-23-2026/paper.pdf

2. Chen and Eldan, Localization Schemes, arXiv:2203.04163v2, 6 June 2022.
   PDF: 617203 bytes; SHA-256 4337c0aa9dc313e1ee20ff5568059a7730b343e9af35cd49b34a5e88b42ad16b.
   Section 2.4.2 uses positive-definite continuous-time controls and gives the Gaussian-quadratic likelihood in Equation (6). Section 3.2.3, Equation (27), expresses the entropy drift through the squared controlled difference of means. These passages support the conceptual background, but do not by themselves authorize a singular adaptive finite-observation limit.
   Link: https://arxiv.org/pdf/2203.04163v2

3. Eldan, Koehler and Zeitouni, A Spectral Condition for Spectral Gap, arXiv:2007.08200v2, 6 August 2021.
   PDF: 212344 bytes; SHA-256 ba6d2d463da33ba14bec6ad551c92456c7c0f52c6e8b795bf10eba72e82e8336.
   Lemma 2 and Section 2.0.1 construct Lipschitz/smooth approximations to projections orthogonal to a chosen direction for SDE existence. The candidate needs only measurable finite-step controls and proves its finite-step facts directly.
   Link: https://arxiv.org/pdf/2007.08200v2

4. Bakry and Emery, Diffusions hypercontractives, 1985.
   PDF: 2172466 bytes; SHA-256 4f06eda393ddcba2430d257f667aea395ecf817e0355b202cae076c98682301f.
   Proposition 3, printed pages 187-188, gives the Gamma_2 curvature formula, and Corollary 2, printed page 199, gives the hypercontractivity consequence. The candidate's anisotropic and finite-energy form is reproved, rather than asserted to follow from an uninspected bibliographic title.
   Link: https://www.numdam.org/item/SPS_1985__19__177_0.pdf

No claim about the correctness of the source's main LSI theorem or its unaudited later propositions follows from these dependency checks.

## 16 Exact-check and build evidence

The submitted checker was replayed unchanged both normally and under Python -O. It passes 192 Gaussian cubic cases, 48 weighted-derivative cases, 36 adaptive finite-minimum cases, 48 precision-kernel cases, four monotone-function cases, and the finite rational gap. The outputs are identical under optimization.

The independent checker uses symbolic Gaussian raw moments rather than copying the submitted Hermite test, verifies the weighted derivative and precision telescope, checks the first two matching-means Gaussian entropy coefficients, and performs the distinct three-copy adaptive finite-state tests described above. It also builds the one-line patch and records exact hashes. Its normal and optimized outputs agree.

Neither checker proves the infinite-dimensional or limiting analytic assertions. Those are audited directly in Sections 4-14 above.

The corrected manuscript built to nine pages with no unresolved references or overfull/underfull boxes in the final pass. All nine rendered pages were visually inspected and were readable without clipping or overlap. The standalone public derivative is rebuilt and visually inspected separately; its result is recorded in VERIFICATION.json. A reproducible build uses a normal TeX installation and performs all generated work outside the immutable package. Build checks concern readability and integrity, not mathematical correctness.

## 17 Formalization and significance boundaries

No Lean source is supplied in the six-file package, and no complete Lean verification was performed. Exact rational Python checks, symbolic algebra, PDF compilation, and source hashes must not be described as a formal proof of Theorem 1.1.

Complete formal coverage requires at least:

- The smooth-density and curvature framework on finite-dimensional Euclidean space
- Anisotropic positive-curvature LSI, its semigroup or another valid proof, and approximation to finite-energy densities
- KL data processing, disintegration, conditional chain rule, and measurable adaptive Gaussian kernels
- The exact Gaussian chi-square formula and conditional moment estimates
- Conditional expectation as Hilbert-space projection, finite nested spectral decomposition, and the rank-one dual comparison
- Conditional independence of copy arrays after full observations and uniform integrability tails
- Gaussian sufficient statistics and monotonic prediction energy
- The precise three-limit argument and change of variables
- Conditional-label integration
- Quartic normalizability, Gaussian cubic prediction, entropy estimates, sharpness limits, and the endpoint counterexample

Assuming these analytic components as axioms and formalizing only the displayed rational identities would not meet full theorem coverage.

The audited result is a sharp, dimension-free, local entropy-loss extension with a clean horizon obstruction. Its contribution is narrower than a general semiconvex LSI or the original source's dimension-free LSI theorem. The principal proof mechanism already appears in source Lemma 4.2; here the changed precision, optimal scalar constant, and proper quartic examples are the relevant additions. This audit does not establish whether those additions are absent from the literature. Priority and external publication assessment remain open, and no journal-tier claim is justified by this review.

## 18 Actionable result

Apply the one-line nonnegative-theta domain patch before treating the manuscript as statement-correct. After that patch, the submitted written analytic argument passes this audit under exactly its stated assumptions. Preserve the distinction between a passing analytic audit, a complete Lean proof, and an independently verified priority claim.
