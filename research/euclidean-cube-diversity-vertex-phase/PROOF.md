# First vertex phase of maximum diversity on Euclidean cubes

This note determines exactly the vertex phase in dimension two and the sharp uniform-in-dimension range. It does not describe the maximizing measure on a square above the transition or all the phases in higher dimensions.

Let C=[0,1]^d, d≥2, with similarity kernel K_s(x,y)=exp(−s‖x−y‖₂), equivalently a Euclidean cube of side s with the unscaled kernel. Let V={0,1}^d and μ give mass 2⁻ᵈ to every vertex. Define s₀ as the unique positive root of

    exp(−s₀)+exp(−√2 s₀)/√2=1.                              (1)

**Theorem.** For every d≥2 and 0<s≤s₀, μ is the unique simultaneous maximum-diversity measure on C, and

    D_max(C)=2ᵈ / [Σ_{k=0}^d binom(d,k) exp(−s√k)].

For d=2 this holds **if and only if** 0<s≤s₀: for every s>s₀ no measure supported only on the four corners maximizes diversity on the full square. Thus s₀ is the best side-length bound valid for every d≥2 at once. This is not an assertion that every higher-dimensional cube loses its vertex measure at s₀. We find 0.46019<s₀<0.46020.

**Energy optimality.** For a finite signed measure η on C write E_s(η)=∬K_s dη dη. This quadratic form is strictly positive for nonzero η: the Fourier transform of exp(−s‖·‖₂) is a positive multiple of s(s²+‖ξ‖²)^−(d+1)/2 with the frequency convention exp(−i x·ξ). Thus Fourier inversion expresses the energy as a strictly positive weight integrated against |η̂|²; continuity and uniqueness of Fourier transforms of finite measures give strictness. The order-two diversity of a probability ν is 1/E_s(ν), and the general [Leinster–Roff theorem and Corollary 7.3](https://doi.org/10.1093/qmath/haab003) identify order-two maximizers with simultaneous maximizers. In particular the common maximizing measure is unique; this makes no claim that zero-order optimization alone has no other solutions. Minima exist by compactness and continuity.

Let U(x)=∫K_s(x,v)dμ(v); its common value at all vertices equals E_s(μ). The following standard equilibrium test is included for completeness; see also [Dajani, §2, (4)–(5)](https://arxiv.org/abs/2610.38031). The condition U(x)≥U(v) for all x∈C is sufficient because

    E_s(ν)−E_s(μ)=E_s(ν−μ)+2∫U d(ν−μ).

It is also necessary: the directional derivative from μ toward a point mass at x is 2(U(x)−E_s(μ)). Among vertex-supported probabilities, the unique minimizer is μ by the same expansion (U constant on V) and positivity. The displayed maximum value follows by grouping a vertex's distances from the other vertices by Hamming weight.

**Descent to the edges.** For s≤s₀ we have s<1/√2 by the enclosure below. In the relative interior of any face of dimension m≥2, for any v∈V put r=‖x−v‖>0 and L equal to the norm of its component parallel to that face, that is, the length of the projection of x−v on the free coordinate directions. Direct differentiation gives

    Δ_face exp(−sr) = [s exp(−sr)/r] [(1+sr)L²/r²−m].

Since L≤r and L≤√m, the bracket is ≤1+s√m−m<0 for m≥2: (m−1)/√m is increasing and equals 1/√2 at m=2. Thus U cannot attain a minimum in the relative interior of any such face (the Hessian would have nonnegative trace). This reduces the global minimum to the edges, without a bound that deteriorates with the ambient dimension. Singularities at vertices are never differentiated in this argument.

**The square edge at the critical parameter.** Write the edge coordinate as 0≤t≤1. Define

    H_s(t)=exp(−st)+(t/√(1+t²)) exp(−s√(1+t²)),
    F_s(t)=H_s(1−t)−H_s(t).

For the square, 4U(t,0)=exp(−st)+exp(−s(1−t))+exp(−s√(1+t²))+exp(−s√(1+(1−t)²)). Its derivative in t is s F_s(t) on (0,1), also as a right derivative at zero. By symmetry it suffices to show F_s(t)>0 on (0,1/2). For fixed t in [0,1/2), F_s(t) is decreasing in s for 0≤s≤s₀: indeed

    ∂_s H_s(u)=−u[exp(−su)+exp(−s√(1+u²))].

Both positive summands after removing the minus sign increase strictly in u∈[0,1]. Their derivatives have signs of 1−su and 1−s u²/√(1+u²) respectively, both positive for s≤s₀<1. Hence it suffices to test s=s₀, for which F(0)=F(1/2)=0.

Here is a reproducible interval lemma (complete integer algorithm in [verify.py](verify.py)). For s in J=[46019/100000,46020/100000] it certifies

| interval for t | expression | rigorous lower bound |
|---|---|---|
| [0,1/16] | F′_s(t) | 28/1000 |
| [1/16,3/8] | F_s(t) | 15/10000 |
| [3/8,1/2] | −F′_s(t) | 13/1000 |

It also certifies opposite signs (+,−) of F_s(0) at the two endpoints of J. Since F_s(0) is the left side of (1) minus one, a strictly decreasing function starting positive and tending to −1, s₀ is well-defined in the interior of J. The three rows, together with F_{s₀}(0)=F_{s₀}(1/2)=0, show strict positivity between those endpoints at the exact critical parameter.

**Reconstructing the interval proof.** Partition [0,1/2] into the 2048 closed cells [i/4096,(i+1)/4096], 0≤i<2048, and evaluate the applicable row above over the complete cell and all s∈J, not just at sampled points. Use F′_s(t)=−H′_s(1−t)−H′_s(t) and, writing r=√(1+t²),

    H′_s(t)=−s exp(−st)+exp(−sr)[1/r³−s(t/r)²].

All endpoints are rounded out to multiples of 10⁻¹⁶ after each operation: products use the extrema of the four endpoint products, positive reciprocals interchange bounds, and integer square roots give outward square roots. For exp(−z), 0≤z≤1, use the odd/even alternating Taylor sums through 15 and 16 at the right/left endpoints, respectively. Each finite sum is also evaluated outwards. This proves that each calculated bound encloses every true value. The unrounded integer lower bounds in units of 10⁻¹⁶ are 281044178743189, 15254435762967, 139747639729053 for 256, 1280, 512 cells respectively. They imply the displayed weaker rational bounds. No fitted numerical parameter or unchecked root is used.

**Other dimensions.** On an edge with the other coordinates zero, the derivative of the unnormalized corner potential 2ᵈU divided by s is the sum, for 0≤k≤d−1, of

    binom(d−1,k)[h_k(1−t)−h_k(t)],
    h_0(u)=exp(−su),
    h_k(u)=(u/√(k+u²)) exp(−s√(k+u²))   (k≥1).

Here k is the Hamming weight of the other d−1 vertex coordinates. For k≥1,

    h′_k(u)=exp(−s√(k+u²))[k/(k+u²)^(3/2)−s u²/(k+u²)]>0,

since k≥1, 0≤u≤1 and s<1/√2≤k/√(k+1). Thus for t<1/2 the k≥1 differences are all strictly positive. The k=0 summand plus one copy of k=1 is the square expression F_s(t); all the remaining terms in higher dimension are nonnegative. Consequently every edge has its minima at its endpoints, also at the critical parameter. This proves the required potential inequality. Off the vertices it is strict, by edge monotonicity and exclusion of an interior minimizer on faces.

**Sharpness and finite grids.** If d=2 and s>s₀, F_s(0)<0, so already points arbitrarily close to a vertex along an edge have lower potential. The directional test above excludes μ, and no other vertex-supported probability can minimize. For any d≥2 and 0<s≤s₀ the conclusion also holds after restricting the domain to any compact subset of the cube containing its vertices, including every full finite grid. For every fixed s>s₀ all sufficiently fine equally spaced square grids contain an edge point violating the test (the first non-corner point eventually does). Consequently the same side length is the sharp cutoff when required uniformly over all finite square grid resolutions. This is not a claim that each fixed finite grid has exactly that critical side length.

A second proof of the only interval lemma uses strict concavity of F on [0,1/4] and strict decrease on [1/4,1/2], with a different exponential enclosure; see [the independent review, §2](REVIEW.md) and [its certificate](independent.py).
