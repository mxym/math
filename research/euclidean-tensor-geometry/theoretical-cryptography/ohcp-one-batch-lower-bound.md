# A one-batch lower bound for the hidden-center step of the Ring-LWE reduction

[Peikert–Regev–Stephens-Davidowitz, Definition 4.3 and Proposition 4.4](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf) use an adaptive oracle with a hidden center in their security reduction. The oracle’s acceptance probability depends on a log-radius plus a chosen scale. Their proposition gives a polynomial adaptive query bound under a gap, a tail and a Lipschitz condition. Section 6.1 uses it in dimension 1 or 2, according to the real or complex embedding. [Bombar–Couvreur–Debris-Alazard](https://inria.hal.science/hal-04308091/document) extract the oracle comparison step for a different model; [Massimino–Davenport](https://jmlr.org/papers/v22/18-105.html) study adaptive localization with paired comparisons. Here the location/scale measurements are precisely of the hidden-center type, not paired comparisons. We ask whether those analytic promises alone allow preselecting all calls in one batch. The answer is negative even for a fixed, known, real-analytic profile with no nuisance parameter other than the center.

This is a lower bound on an abstract sensing experiment. It does not construct or analyze an oracle from cryptographic samples, assert that the hard profile occurs in a Ring-LWE reduction, or place a lower bound on any Ring-LWE algorithm. Code checks elementary bounds only; no locator is supplied.

## Statement

Normalize the scale d to 1. Take k≥1, κ≥20, 0<ε≤1/(128k), and 0<δ≤1/4. A fixed known oracle family on (z,t)∈R^k×R_{≥0} returns fresh independent Bernoulli responses with probability

    p_θ(z,t) = 1/2 + (2/κ) exp(-e^(2t) ||z-θ||²),

where θ ranges in the annulus 1/4≤||θ||≤1/2. A one-batch procedure first chooses all its queries, possibly using arbitrarily correlated private randomness, independently of the responses. It then receives the responses and outputs a vector. If it succeeds for each center, with probability at least 1-δ of Euclidean error at most ε, then its number of queries T satisfies

    k = 1:  T ≥ c κ² log(1/δ)/ε;
    k ≥ 2:  T ≥ c κ² k [k + log(1/δ)]/ε²,

where c>0 is an absolute constant. The lower bounds still hold if the exact profile and known baseline are given to the procedure, and its queries can use arbitrary real positions and scales. A deterministic upper bound T on its batch size is sufficient; the same proof uses its expected precommitted batch size when this is finite.

Verify the original OHCP promises: with t*=0 the acceptance gap at z=0 is at least (2/κ)e^(-1/4)>1/κ above the baseline 1/2. The bound (2/κ)exp(-e^(2t)/16)≤2 exp(-t/κ) for t≥0 follows from e^(2t)≥1+2t and κ≥20. The first derivative in t is bounded in absolute value by 4/(eκ). The formula is globally radial with a common log-distance profile for all centers, and extends at zero radius by continuity. Under the original parameter choice κ≥max(20,20log(k+1)), ε=δ=e^(-κ), the theorem applies. In dimension 1 it yields Ω(κ³ e^κ) queries, and in dimension 2 it yields Ω(κ³ e^(2κ)), versus the published polynomial adaptive bound. This does not dispute the published result or show a separation for a specific Ring-LWE oracle; it prevents turning that subroutine into a one-batch black box under only its stated promises.

## Information estimates for nonadaptive calls

Let s=e^(-t), g_s(z,y)=exp(-||z-y||²/s²), and P_y denote the full random query and response transcript (include the independent seed). For one fixed query, its Bernoulli KL divergence between centers y,y' is at most

    C κ^(-2) (g_s(z,y)-g_s(z,y'))².

Indeed the probabilities lie in [1/2,3/5], and for Bernoulli probabilities p,q the elementary log inequality log u≤u-1 gives D(p||q)≤(p-q)²/[q(1-q)]. Since the query seed is independent of the center, the KL chain rule in a nonadaptive batch sums the per-call divergences, averaged over the precommitted seed. This identity is where full nonadaptivity enters.

Put x0=(3/8)e_1, R=1/16, and let X be uniform on B(x0,R). Every perturbation X+h with ||h||≤4ε remains in the allowed annulus. Such a translated distribution is pointwise bounded by twice the uniform density on B(x0,R+4ε): indeed its ball is inside that larger ball, and the volume ratio (1+4ε/R)^k≤exp(64kε)<2. This comparison also permits any interpolation of such shifts. Importantly the larger ball is independent of the shift or direction.

For k≥2 and any ball B of radius at least R, for U uniform on B the following bound is uniform in z,s and in the dimension:

    E ||∇_U g_s(z,U)||² ≤ C/R².

For k=2 the integral of the squared gradient over the entire plane is exactly π: direct polar integration of 4r²s^(-4)exp(-2r²/s²). Dividing by the ball area gives the claim. For k≥3, write u=||z-U||²/s² and use ||∇g||=(2/||z-U||)u e^(-u)≤(2/e)/||z-U||. If the ball has radius ρ, the probability that ||z-U||≤r is at most min(1,(r/ρ)^k). Integrating the tail of ||z-U||^(-2) bounds its expectation by [k/(k-2)]ρ^(-2)≤3R^(-2). This dimension-uniform bound works even at arbitrarily small query scale. Finally, Cauchy–Schwarz along a segment gives

    (g_s(z,y+h)-g_s(z,y))²
           ≤ integral_0^1 <∇g_s(z,y+uh),h>² du.

## Confidence lower bound, with direction averaging

Two centers at distance 4ε have disjoint success balls. If the procedure succeeds with probability 1-δ at both, the event that its estimate lies in the first success ball gives, by KL data processing,

    D(P_y || P_y') ≥ (1-2δ) log((1-δ)/δ) ≥ c0 log(1/δ).

The first inequality follows by comparing the binary event probabilities, which are at least 1-δ and at most δ, respectively. This applies to every pair used below.

For k≥2 take y=X and y'=X+4ε V, where V is uniform on the 2k signed coordinate unit vectors, independent of X and the query seed. For each interpolation parameter u, bound the shifted X density by twice the uniform measure on the fixed enlarged ball before integrating V. Now under that common ball measure the evaluation point and V are independent; E_V (a·V)²=||a||²/k. The segment estimate and gradient bound therefore give

    E_{X,V} D(P_X || P_{X+4ε V}) ≤ C T κ^(-2) ε²/k.

Comparison proves T≥c κ² k log(1/δ)/ε².

For k=1 take the fixed shift h=4ε. For any z,s, completing the square gives the exact unweighted integral

    integral_R (g_s(z,y)-g_s(z,y+h))² dy
        = 2 sqrt(π/2) s (1-exp(-h²/(2s²))).

This is bounded by C min(s,h²/s)≤C |h|. Averaging over X costs at most its uniform density 1/(2R), so E_X D(P_X||P_{X+h})≤C Tκ^(-2)ε. The confidence inequality proves the first claim. This case uses the bounded finite difference rather than a squared-gradient bound, which would not be uniform at tiny s in one dimension.

## Dimension lower bound by cube perturbations

For k≥2 take g=4ε/sqrt(k), a uniform sign vector U∈{-1,1}^k, and θ=X+gU. The shift has norm 4ε. We use the standard neighboring-bit testing argument, with the base X disclosed for the test only after the query batch; the procedure itself never had X when choosing queries. For a fixed realized X and estimate Y, label each coordinate by the sign of Y_i-X_i. Every mislabeled coordinate contributes at least g² to squared error relative to θ. On the success event there are at most k/16 mislabeled coordinates, and otherwise at most k. Thus the expected Hamming error is at most k/16+δk≤5k/16.

Write U^{(i)} for U with bit i flipped. For each pair differing in direction i, the two error probabilities of any binary label decision sum to at least 1-d_TV(P_{X+gU},P_{X+gU^{(i)}}), conditional on X and the bit pattern apart from the flip. Uniformly averaging over bits and X gives an average TV over directions i of at least 3/8. Pinsker and Jensen then imply

    sum_{i=1}^k E_{X,U} D(P_{X+gU} || P_{X+gU^{(i)}}) ≥ c1 k.

On the other hand, every connecting segment has direction ±e_i, length 2g, and all its shifts relative to X have norm at most 4ε. For each query and direction i use the segment inequality, then the pointwise density bound by the common enlarged ball. Summing the k coordinate derivative squares gives the trace, not k times a trace bound:

    sum_i E_{X,U} D(P_{X+gU} || P_{X+gU^{(i)}})
        ≤ C T κ^(-2) g² E_{seed,typical query,U'} ||∇g_s(z,U')||²
        ≤ C' T κ^(-2) ε²/k,

where U' is uniform on the common enlarged ball; the first bound denotes the average over the T per-query gradient estimates, or their sum before factoring out T. Thus T≥c κ²k²/ε². Combining it with the separately derived confidence lower bound and using max(a,b)≥(a+b)/2 proves the stated formula.

## Scope and checks

The conclusion concerns all preselected one-batch locations and scales, not just a grid or fixed scales, and applies to a simple monotone radial profile. It does not rule out two or more batches, and says nothing about computational difficulty of actual noisy ring samples. The neighboring-testing step is only an information lower bound and is not a prescription for localizing any hidden lattice point. The adjacent checker verifies elementary exact inequalities used in the proof (5,358 cases) and illustrates the analytic constants and Gaussian integrals (843 floating cases), with no samples from cryptographic distributions.
