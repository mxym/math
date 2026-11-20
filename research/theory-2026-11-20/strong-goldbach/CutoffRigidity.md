# Semiprime savings force positive three-factor terms

Write the normalized small-divisor weight as a continuous profile f on [0,1], with f=0 on [1/2,1] and f'(0+)=-1. For example, this includes finite signed combinations of (b-t)_+ with 0<b≤1/2 and coefficients summing to one. For the factor proportions t_i>0 of a squarefree m (sum t_i=1), define

    U_f(t_1,...,t_k)=Σ_{I⊆[k]} (-1)^|I| f(Σ_{i∈I}t_i).

The small-side term is (log m) U_f. The sign convention is the small side of [the symmetric divisor reduction](SymmetricParityReduction.md), so positive composite values are a cost when lower-bounding the prime term.

**Rigidity.** If U_f(a,b,1-a-b)≤0 for every a,b>0 with a+b<1/2, then U_f(t,1-t)≥t throughout 0<t≤1/2. If all those ternary contributions are zero, then necessarily f(t)=(1/2-t)_+.

Indeed, since the third factor exceeds 1/2, the ternary expression is f(0)-f(a)-f(b)+f(a+b). Hence d(t)=f(t)-f(0) is subadditive on the lower half. Dividing t into n equal pieces gives d(t)≤n d(t/n)→−t. As U_f(t,1-t)=−d(t), the bound follows, including t=1/2 by continuity. If every ternary value is zero, d is additive on that half; division into equal pieces now gives d(t)=−t, and f(1/2)=0 fixes f(0)=1/2. The centered profile also cancels every ternary tuple, including balanced tuples, by complementary subsets.

There is a direct quantitative witness. If U_f(t,1-t)≤(1−ε)t at some 0<t<1/2, let D(t)=d(t)+t. Put h=t/n with n large enough that D(h)≤εh/2, using D'(0+)=0. The sum of U_f(jh,h,1-(j+1)h) over 1≤j<n telescopes to D(t)-nD(h)≥εt/2. At least one term is ≥εh/2, and continuity yields an open positive region. If the saving occurs at t=1/2 it persists at a nearby interior t.

**The open region has actual prime mass on average.** For fixed k≥2 put
`I_k(G)=(1/k!)∫_{Σt_i=1} G(t) dt_1…dt_{k−1}/∏t_i`,
where G is continuous, nonnegative, symmetric, and supported away from the coordinate faces. The unconditioned factor-box count in [the six-factor note](SixPrimeNegativeSector.md) and partial summation imply
`Σ_{m≤Y} (log m)G(t(m)) = Y I_k(G)+o(Y)`
over squarefree m with exactly k factors. Here t_i(m)=log p_i/log m; normalizing instead by log Y changes nothing in the leading term, since m≤Y^(1−δ) is negligible for fixed δ>0 and then δ can tend to zero. Odd m alone give the same leading term: for G's support, every factor of large m is a fixed positive power of m. For each odd m, sum odd prime p with X<p+m≤2X. The prime number theorem gives this log-weighted sum as (2X−m)_+−(X−m)_++o(X), uniformly in m≤2X. Thus on summing over even targets,

    Σ_{X<N≤2X, N even} Σ_{p+m=N} (log p)(log m) G(t(m))
         = (3/2) X² I_k(G)+o(X²).

Here the constant follows by partial summation since the integral of the prefix-length weight is 3X²/2. Also Σ_{X<N≤2X, N even} NS(N)~3X²/2. For example expand
`S(2n)=2 C₂ Σ_{d|n, d odd squarefree} ∏_{r|d}(r−2)^−1`;
the reciprocal-weighted divisor coefficient sum converges to 1/C₂, giving mean 2 over even targets and the stated weighted asymptotic. Choosing G nonzero and bounded by the positive ternary weight on its open chamber shows that the new costs are nonnegligible on some even targets. This is not a prediction for the signed sum across chambers, nor a pointwise lower bound for every N.

## Exact check on the reference model

The signed sine integral from [the six-factor calculation](SixPrimeNegativeSector.md), for all even factor counts, gives the entire generating function

    F(z) = Σ_{s≥1} z^(2s) I_(2s)(K)
         = (1/π) ∫₀^∞ [cos(2z arctan(t/2))−1] dt/t² .

Interchanging powers and integral is justified by the O(t²) behavior of the absolutely summed numerator at zero and compact-z boundedness at infinity. For a positive integer j, substitute v=arctan(t/2) and integrate by parts to obtain

    F(j) = −(j/π) ∫₀^(π/2) sin(2jv) cot(v) dv = −j/2.

The trigonometric polynomial under the last integral has constant coefficient 1 and only nonconstant cosine modes of even frequency, by the sine addition identity. In particular the total signed reference sum at z=1 is −1/2. The semiprime reference deficit alone is log 2, so the factor-four upper sieve on that term alone gives 4 log 2>1. The signed reference integral is not a target-uniform estimate for the actual primes.

This is a profile-specific obstruction, narrower than [Tao's parity obstruction](https://terrytao.wordpress.com/2014/11/21/a-general-parity-problem-obstruction/). For related signed factor-state analyses see [Arneth, PIHR-Goldbach VII](https://doi.org/10.5281/zenodo.23011047) and [XII](https://doi.org/10.5281/zenodo.23016346); those investigate different weights and transportation conditions. The result here does not rule out a weight above the square root, allowing signed compensation, or other methods.
