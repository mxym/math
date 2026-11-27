# Sharp posterior-heat bounds for Gaussian randomized rounding

**Scope.** This is an abstract probability result about the ideal Gaussian rounding kernel, not deterministic nearest rounding, bounded unbiased rounding, finite-precision sampling, or a claim about any concrete scheme. It addresses the positive discretization step of [Lyubashevsky–Peikert–Regev, Toolkit §2.4.2](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf), specifically the continuous-input case of [Peikert, Theorem 3.1 and §4.1](https://web.eecs.umich.edu/~cpeikert/pubs/pargauss.pdf). Peikert proves a sufficient flatness bound at the rounding width. [Luzzi–Ling–Bloch, Proposition 1 and Theorem 2](https://eprint.iacr.org/2022/808.pdf) give an infinity-flatness bound and a different average bound with uniform dithering. Here the center is fixed; the result below uses the averaging in the same completed-square integral to get a strictly better exponential rate in the wide fixed-shape model, together with its exact leading constant and a complete one-dimensional exception. The cited bounds neither require nor assert these sharper statements. No claim of literature priority is intended.

## 1. Model and an exact identity

Let L be a full-rank lattice in R^n, L* its dual under the ordinary dot product, and V its covolume. For a positive definite symmetric matrix T put

    g_T(z) = (det T)^(-1/2) exp(-pi z^T T^(-1)z),
    Theta_T(v) = V sum_(z in L) g_T(z-v)
               = sum_(u in L*) exp(-pi u^T T u) exp(2 pi i u.v).

The covariance of g_T is T/(2 pi); T itself is a width matrix. On the affine lattice c+L, D_(T,m) is proportional to g_T(x-m).

Draw Y from g_B(y-m). Conditioned on Y=y, draw X on c+L with probabilities proportional to g_A(x-y). Let P be the law of X, and Q=D_(A+B,m) on the same coset. Put

    S=A+B,   C=(A^(-1)+B^(-1))^(-1),   M=B S^(-1),
    d=m-c,   F(v) = E_(W~g_C)[1/Theta_A(v+W)].

Then for every k in L,

    P(c+k)/Q(c+k) = Theta_S(d) F((I-M)d+Mk).                  (1)

In particular, for K distributed as Q-c,

    E F((I-M)d+MK) = 1/Theta_S(d),
    TV(P,Q) = (1/2) E |F((I-M)d+MK)/E F - 1|.                (2)

**Proof.** With z=x-m and b=y-m, completion of the square gives

    g_B(b) g_A(z-b) = g_S(z) g_C(b-Mz).

This identity also holds for noncommuting A and B: the precision of b is A^(-1)+B^(-1), its conditional center is C A^(-1)z=M z, and det S det C=det A det B. The conditional rounding probability is V g_A(x-y)/Theta_A(y-c). Integrate against g_B, then divide by Q(x)=Vg_S(x-m)/Theta_S(d). Normalization yields (2). Thus the Gaussian conditional smoothing acts on the reciprocal of the rounding normalizer, not on the normalizer itself.

Define the dual tail e_T=sum_(0 != u in L*) exp(-pi u^T T u). If e_A<1, (1) gives the finite-width estimate, uniform in c,m,

    TV(P,Q) <= (1+e_A) [ e_(A+C) + e_A^2/(1-e_A) ].           (3)

Indeed, if U=Theta_A-1 then 1/(1+U)=1-U+U^2/(1+U). Gaussian averaging of U changes Theta_A-1 to Theta_(A+C)-1 exactly, while the last term in supremum norm is at most e_A^2/(1-e_A). Thus |F-1| is bounded by the bracket, and E F >= 1/(1+e_A). Use E|F-EF|<=2 sup|F-1| in (2). The derivation does not assume the rounding normalizer is nearly constant at an individual realized input; small e_A is a sufficient condition only for (3), not for (1).

## 2. Sharp fixed-shape, wide-width asymptotic

Now keep L, A, B, c, m fixed and use tA,tB in the experiment, with t tending to infinity. Here C and M still denote the unscaled matrices; the conditional width is tC, and M is unchanged. Set

    alpha = min_(0 != u in L*) u^T A u,
    beta  = min_(0 != u in L*) u^T (A+C) u,
    U_0   = {u in L*: u^T(A+C)u=beta},
    H(v)  = sum_(u in U_0) exp(2 pi i u.v),
    G     = closure of {Mk mod L: k in L} in R^n/L,
    v_0   = (I-M)d mod L.

The polynomial H is real by symmetry of U_0. Integrals over G use probability Haar measure. Then

    alpha < beta < 2 alpha,                                 (4)

    lim_(t -> infinity) exp(pi beta t) TV(P_t,Q_t)
       = (1/2) int_G |H(v_0+g)| dg,                          (5)

    lim_(t -> infinity) exp(2 pi beta t) chi^2(P_t||Q_t)
       = int_G H(v_0+g)^2 dg.                               (6)

In particular, if the input center lies in c+L, the right side of (5) is strictly positive; the sharp rate is beta, rather than the exponent alpha in rounding-width flatness. A translate may make the whole first shell disappear. Such cancellation occurs exactly when, for every projected character class of U_0 modulo L* under u -> M^T u, the sum of exp(2 pi i u.v_0) in that class is zero. Equations (5)–(6) are limits with possibly zero right-hand sides; no next-shell assertion in such a case is implicit.

**Proof.** The inequalities 0<C<A as positive quadratic forms give (4); for the upper inequality test an A-minimizer directly. Let beta_2>beta be the next distinct positive value of the quadratic form A+C on L*. The tail starting at beta_2 is O(exp(-pi beta_2 t)), by absolute convergence at t=1. The reciprocal expansion above gives, uniformly in v,

    F_t(v)=1-s_t H(v)+O(exp(-pi min(beta_2,2 alpha)t)),
    s_t=exp(-pi beta t).                                     (7)

All constants in the proof of (7) are for fixed shape and lattice. With R=A^(-1/2) C A^(-1/2), one has 0<R<I and

    A^(1/2) M^T A^(-1/2)=R,
    u^T(A+C)u=(A^(1/2)u)^T(I+R)(A^(1/2)u).

Therefore M^T strictly decreases the (A+C)-length of each nonzero vector. Since M is invertible, M^T u is nonzero; if u is in U_0, M^T u cannot belong to L*. Thus each character in H is nontrivial on G and the Haar mean of H on v_0+G is zero.

For any u in L*, the expectation of exp(2 pi i u.MK) under Q_t tends to 0 if M^T u is not in L*, and equals 1 otherwise. To see the first assertion, apply Poisson summation to the Gaussian on L centered at d with a fixed modulation theta=M^T u; the ratio to the unmodulated sum is bounded in modulus by

    [ sum_(w in L*) exp(-pi t (w-theta)^T S (w-theta)) ]
        / Theta_(tS)(d),

which decreases exponentially at fixed theta outside L*. The character criterion and density of trigonometric polynomials imply weak convergence of Mk modulo L to Haar on G. From (2) and (7), uniformly in k,

    P_t(c+k)/Q_t(c+k)-1
      = -s_t [H(v_0+Mk) - E_Qt H(v_0+MK)] + o(s_t).

This yields (5) and (6). If d is in L, v_0 belongs to G modulo L, as it is d-Md. The Haar support on v_0+G then includes zero, where H(0)=|U_0|>0; continuity makes the integral positive. Finally, characters of G represented by u,u' coincide exactly when M^T(u-u') is in L*. Orthogonality proves the stated cancellation criterion. In particular, the right side of (6) is the sum of squared absolute grouped coefficients.

Two cautions. This argument is not a uniform asymptotic in changing lattice rank or changing shapes. It concerns TV of the output only, not an experiment also releasing Y. For instance a joint likelihood includes the unsmoothed factor 1/Theta_A(Y-c) and need not have the improved exponent.

## 3. Complete exactness criterion on a line

Take L=lZ with l>0. The experiment is **exactly** Q at a finite positive pair of widths if and only if

    B=A and (m-c)/l belongs to 1/2 + Z.                     (8)

Thus the exceptional model is exact at every common scale. Neither rounding width must be above a smoothing threshold for this equality. For an orthogonal lattice with both width matrices diagonal in its orthogonal coordinate system, exactness holds if and only if (8) holds on every coordinate separately.

**Proof.** Rescale to L=Z, write lambda=B/(A+B) in (0,1), and d=m-c. Poisson summation and the Jacobi triple product give

    Theta_A(v) = product_(j>=1)
       (1-q^(2j)) [1+2q^(2j-1) cos(2 pi v)+q^(4j-2)],
    q=exp(-pi A).

Each bracket is positive and its logarithmic derivative is strictly negative on 0<v<1/2. The series of logarithmic derivatives converges for the fixed q in (0,1), so 1/Theta_A is even, periodic, and strictly increasing on (0,1/2), with positive derivative there. The same is true of F. For the strict derivative assertion, convolving by g_C is the circle heat flow at time C/(4 pi). The derivative of the even initial function solves the heat equation on (0,1/2) with zero endpoint values; the strong maximum principle preserves strict positivity in the interior. Consequently each level set of F on R/Z contains at most two points, and a two-point level set consists of two opposite points modulo Z.

By (1), exactness is equivalent to constancy of F on the orbit (1-lambda)d+lambda Z modulo 1. Its closure has size at most two only when lambda=1/2 (lambda=0,1 are outside the model). For lambda=1/2 the two orbit points are d/2 and d/2+1/2. They are negatives of one another modulo 1 exactly when d is a half integer modulo 1. In that case evenness makes the values equal, and normalization gives P=Q, completing the argument. Independence and equality of marginals give the orthogonal product statement.

In this one-dimensional normalization the shortest-shell polynomial is 2 cos(2 pi v). If lambda is not 1/2, the coefficient in (6) is 2: the average of its squared cosine is 1/2 on the orbit because 2 lambda is not an integer. If lambda=1/2 it is 4 cos^2(pi d). Thus there are no additional one-dimensional cancellations of the first shell. With centered input and balanced widths, the coefficient in (5) is 1; with balanced widths at d=1/2 it is 0 because all orders, not just the first, vanish.

## 4. Independent repetitions of a fixed block

Let v_* be the right-hand side of (6); suppose v_*>0. For positive integers N_t and N_t exp(-2 pi beta t) tending to tau in [0,infinity], the independent-block TV has the limit

    TV(P_t^(tensor N_t), Q_t^(tensor N_t))
          -> 2 Phi(sqrt(v_* tau)/2)-1,                     (9)

with values zero at tau=0 and one at tau=infinity. Here Phi is the usual standard normal distribution function. The result also applies to an orthogonal tensor power of one fixed block, and not to shared inputs or shared rounding randomness.

**Proof.** Under Q_t let Z_t=P_t/Q_t-1; it has mean zero, |Z_t|=O(s_t) uniformly, and E Z_t^2=(v_*+o(1))s_t^2. If 0<tau<infinity, Taylor expansion of log(1+Z_t) has accumulated expected absolute cubic remainder at most O(N_t ||Z_t||_infinity E Z_t^2)=o(1). The sum of the squared terms converges in probability to v_* tau by independence and the same norm bound; the sum of the linear terms satisfies the triangular-array central limit theorem by bounded vanishing increments. Under Q_t^(tensor N_t) the log-likelihood tends to N(-v_* tau/2, v_* tau). For a log-likelihood ell, TV is E_Q (1-exp(ell))_+, a bounded continuous function of ell, which gives (9). At tau=0 the identity chi^2 for products, 1+chi^2(product)=(1+chi^2(single))^N_t, gives the result. At tau=infinity, E_Q sqrt(1+Z_t)=1-(v_*+o(1))s_t^2/8 and the product's overlap is at most this single-block affinity raised to N_t.

For the orthogonal power-of-two cyclotomic coefficient lattice the change to canonical Euclidean coordinates is an isometry up to scale, so the line calculation can be applied when the specified Gaussian inputs and rounding kernel really factor in that model. The result is an output-law transfer bound for those ideal assumptions; it does not identify the law of a finite-precision implementation, change the hypotheses of the Ring-LWE worst-case reduction, or imply anything about an actual scheme.

## 5. Reproduction

Run the accompanying standalone Node.js file:

    node verify-gaussian-rounding-posterior-heat.js

The verifier exercises exact identities on synthetic rational matrices and finite orbit character sums, independent direct quadrature for the rounded mass and its posterior-heat representation, exact-midpoint checks in floating point at several finite widths, and one-dimensional leading constants. The analytic arguments above, not numerical comparisons, are the proof for all lattices, widths and ranks stated here.
