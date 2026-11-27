# How many Galois rotations sphericalize a Gaussian variance profile?

**Scope.** [Lyubashevsky–Peikert–Regev, Lemma 5.6](https://cims.nyu.edu/~regev/papers/ideal-lwe.pdf) use the fact that field automorphisms permute canonical Gaussian widths. We quantify a separate positive noise-only operation: take independent copies of a Gaussian with a specified anisotropic covariance, rotate those copies, and combine them with nonnegative variance weights. In the dyadic cyclotomic case the best worst-case covariance discrepancy is exact even if the weights may depend on the input covariance, and it converts into a sharp total-variation limit. We do not transform public rows or secrets, pool available Ring-LWE samples, or infer a modification of the hardness proof. No fixed modulus, implementation, or scheme is considered.

## 1. Model

Let G be a finite abelian group of order d acting regularly on a set of canonical places. For K=Q(zeta_(2^a)) with a>=3, this is the group (Z/2^a Z)^*/{+1,-1}, cyclic of order d=2^(a-2); the places are the complex-conjugate pairs. Each place contributes h real Gaussian coordinates, with h=2 in this dyadic example, and h=1 for a totally real field with a regular indexing.

Write normalized mean and squared norm on G as E f=d^(-1)sum_x f(x) and ||f||_avg^2=E f^2. Fix B>=4 and take a real variance contrast f with

    E f=0,   ||f||_avg<=1,   ||f||_infinity<=B.

Use the centered Gaussian E_f with covariance (1+epsilon f(x))I_h in place x, and independence across places, where 0<epsilon<1/B. For a probability w on G with at most k nonzero weights take independent copies E_(f,g) of E_f, indexed by its support, and form the sum of sqrt(w(g)) times the copy rotated by g. This is exactly a centered Gaussian with place variance

    1+epsilon (w*f)(x),   (w*f)(x)=sum_g w(g)f(x-g).        (1)

A possible conjugation within a complex place preserves its isotropic two-dimensional block. We compare this law with the centered Gaussian of covariance I in all places. When considering several outputs, the design w is fixed and each output uses its own independent input copies. A mixture over an unobserved randomized design is a different experiment.

## 2. Exact best worst-case energy with the profile known

For any finite abelian G the worst optimum over profiles has the upper bound

    sup_f inf_(w: |supp w|<=k) ||w*f||_avg^2
                         <= A(d,k):=(d-k)/(k(d-1)).        (2)

In the dyadic G above, equality holds for every 1<=k<=d. It also holds when G is the cyclic group of odd prime order. Moreover, the profile witnessing equality in (2) can be chosen independently of k.

For the upper bound choose a uniformly random k-subset S and put uniform weights on its distinct elements. For each x, the population of f(x-g) over g has exact mean zero and variance ||f||_avg^2. The mean of a sample without replacement has variance A(d,k)||f||_avg^2, by summing its k diagonal covariances and k(k-1) identical offdiagonal covariances -||f||_avg^2/(d-1). Averaging over x gives (2) by the existence of a subset no worse than its average. This does not require a randomized output law after w is chosen.

For the lower bound use normalized Fourier coefficients fhat(chi)=E_x f(x) overline(chi(x)), and write what(chi)=sum_x w(x) overline(chi(x)). Suppose f has exactly flat nontrivial spectrum,

    fhat(1)=0,   |fhat(chi)|^2=1/(d-1) for every chi!=1.

Then Parseval gives, for every w,

    ||w*f||_avg^2 = (d sum_x w(x)^2-1)/(d-1)
                  >= A(d,k).                              (3)

The last inequality is Cauchy–Schwarz, and any uniform k-subset attains equality for this particular f. Thus allowing arbitrary nonnegative weights, or allowing the design to depend on f, cannot bypass the lower bound.

**An explicit admissible real profile for the dyadic case.** For d=2 let f be the nontrivial real character. For d>=4 put L=d/2. Form the [Rudin–Shapiro polynomials](https://doi.org/10.1090/S0002-9939-1959-0116184-5) of length L, with coefficients b_j in {+1,-1}. Their recursion starts P=Q=1 and replaces P,Q at length M by P+z^M Q,P-z^M Q, so |P|^2+|Q|^2=2L on the unit circle and |P|<=sqrt(d). On the cyclic group prescribe fhat(j)=b_j/sqrt(d-1) for j=1,...,L-1 and fhat(d-j)=fhat(j), take fhat(L)=1/sqrt(d-1), and set fhat(0)=0. Inversion gives a real f of mean zero, squared norm one, and

    ||f||_infinity <= (2 sqrt(d)+3)/sqrt(d-1) <=4  for d>=8.

The small d=4 case has bound sqrt(3) by the triangle inequality. Thus this f is admissible and proves exactness. Its Fourier prescription uses a bounded real variance contrast, not a hypothetical binary circulant Hadamard sequence.

**Odd prime case.** The quadratic character chi_2, extended by zero at zero, has mean zero and, at each nontrivial additive character, unnormalized Fourier coefficient of modulus sqrt(d). For instance its nonzero-shift autocorrelation is -1, by the standard quadratic-character calculation; applying Parseval to that autocorrelation gives the same modulus. Multiplying chi_2 by sqrt(d/(d-1)) gives the required f, bounded by sqrt(3/2).

## 3. Unknown profile: a different, sharply characterized equality case

If one single design must be chosen before learning f, then for each fixed w one has exactly

    sup_f ||w*f||_avg^2 = max_(chi!=1) |what(chi)|^2.         (4)

The upper bound is Parseval. A nontrivial maximizing character supplies a real mean-zero witness: use the character itself if it takes values +1,-1, or its real part multiplied by sqrt(2) otherwise. Its squared norm is one and its supremum norm at most sqrt(2).

The right side of (4) is at least the average over the nontrivial characters, hence at least A(d,k) by (3)'s formula for the sum of squared what. Equality is possible if and only if w is uniform on a size-k difference set in G: each nonzero group element occurs the same number lambda=k(k-1)/(d-1) of times as an ordered difference of distinct elements from its support. In fact, both Cauchy–Schwarz and the maximum-versus-average inequality must be equalities. The first requires uniform weights on k points (except for the trivial all-group endpoint, where the same conclusion follows). The second is equivalent by Fourier inversion to the autocorrelation of the indicator of the support being constant off zero, which is exactly the difference set condition. Conversely that condition gives equality. This is the familiar relation of difference sets to flat character sums; see, for example, [Carlet–Ding](https://cse.hkust.edu.hk/faculty/cding/JOURNALS/jcomp1.pdf) for related Paley–Hadamard constructions. The distinction here is its exact role in an *unknown-covariance* requirement, versus (2) where the design may adapt. In a prime cyclic group d=3 modulo 4, the quadratic residues form such a set for k=(d-1)/2. Indeed their indicator is (1+chi_2(x)-1_(x=0))/2. Its nonzero-shift autocorrelation sum equals (d-3-chi_2(a)-chi_2(-a))/4=(d-3)/4, from the character sum used in §2. In the dyadic group when k=d/2 and d>=4, no equality is possible at that k because k(k-1)/(d-1) is not integral. This is a strict finite-design statement, not a dimension-uniform lower gap.

## 4. Exact total-variation window

Suppose epsilon tends to zero along a sequence of designs, and compare N independent output draws with N independent reference Gaussians. The number N may vary. Write

    I(w,f) = (h N d epsilon^2/2) ||w*f||_avg^2.

Uniformly in d,N,w,f under the stated bound B, the TV distance differs by o(1) from

    V(I(w,f)) = 2 Phi(sqrt(I(w,f))/2)-1,                    (5)

with V(0)=0 and V(infinity)=1. In particular, in dyadic groups and odd prime cyclic groups the adaptive minimax TV has the exact asymptotic value

    V((h N d epsilon^2/2) A(d,k)) + o(1),                 (6)

with no assumed limit needed for the argument of V. In the unknown-profile model, replace A(d,k) by the optimal value of inf_w max_(chi!=1) |what(chi)|^2; when a size-k difference set exists, (6) holds there too.

**Proof of (5).** In the reference coordinates, the individual relative variance changes are t_i=epsilon (w*f)(x), repeated hN times for each x. Their maximum absolute value is at most B epsilon, which tends to zero. Under the reference law their log likelihood is the sum of independent terms

    -(1/2) log(1+t_i) + (1/2) [t_i/(1+t_i)] Z_i^2,
    Z_i independent N(0,1).

Writing I=(1/2)sum_i t_i^2, its deterministic mean is -I/2+O((max|t_i|)I), and its variance is I+O((max|t_i|)I). If I tends to a strictly positive finite limit, a centered triangular-array CLT applies since the sum of the absolute third moments is at most C max|t_i| sum_i t_i^2=o(1). Evaluating TV as E_reference (1-exp(log likelihood))_+ gives (5). If I tends to zero, the sum of the centered Gaussian KL terms is O(I), giving TV tending to zero. If I tends to infinity, multiply the Gaussian Hellinger affinities: the negative logarithm of affinity is (1+o(1)) sum_i t_i^2/16, by the scalar affinity formula and the vanishing maximum. The overlap thus tends to zero. These three cases imply the claimed uniform o(1) by the subsequence characterization of uniform convergence: every violating sequence has a subsequence on which I has a limit in [0,infinity]. Since V is increasing, combining this uniform statement with the exact finite energy optimizations proves (6) and the stated nonadaptive conclusion.

Any common wrapping or discretization contracts the TV upper bound from the unwrapped model. The optimal lower profiles need not survive such processing. Nor does this Gaussian noise synthesis preserve the distribution of secret-dependent samples under a change of outer ring or modulus.

## Reproduction

    node verify-galois-gaussian-sphericalization.js

The exact verifier checks the finite averaging identity, the bounded dyadic construction's flat cyclic autocorrelation, and the Paley difference-set equality on generated small groups. The limiting TV statements use the direct Gaussian likelihood proof.
