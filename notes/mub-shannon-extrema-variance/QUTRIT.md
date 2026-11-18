# The sharp lower endpoint for four qutrit bases is not maximized by MUBs

For L=4 orthonormal bases of C³ define m=min_{||ψ||=1} (1/4)Σ H_b(ψ), H_b the Shannon measurement entropy in nats. The same minimum over all density matrices equals the pure-state minimum by concavity. The unperturbed bases below are the standard complete MUB. For ω=exp(2πi/3), let B_∞ be the coordinate basis and B_a have vectors u_{a,b}(x)=ω^{a x²+b x}/√3, a,b,x∈{0,1,2}. Use

$$
 \mathcal B(t)=(B_\infty,B_0,B_1,D_t B_2),\qquad
 D_t=\mathrm{diag}(1,e^{it},e^{2it}).
$$

We obtain

$$
 m(0)=\log 2,\qquad m(t)=\log 2+\frac{t^2}{48}\log(1/t^2)+O(t^2)\quad(t\to0).
 \tag{Q1}
$$

In particular m(t)>log 2 for all sufficiently small nonzero t. [The explicit certificate](#a-fully-specified-algebraic-unitary) below supplies a strict, concrete algebraic example without relying on the error term. Thus the standard complete MUB is not even a local maximizer of the sharp lower bound. Every complete qutrit MUB is equivalent to it (Brierley–Weigert–Bengtsson). This contradicts the sharp-lower-endpoint assertion in Conjecture 1 of Puchała et al. It does not decide the assertion concerning the upper endpoint, does not claim the global maximizing tuple, and does not concern extrema of a particular non-sharp, analytically derived bound.

**1. Equality cases at zero (known; see [prior work](README.md#prior-work-and-scope)).** Mutual unbiasedness follows by expanding the squared quadratic Gauss sum: in the off-diagonal terms x=y+h, h≠0, summing the nontrivial character with linear coefficient 2(a−a')h over y gives zero. Within a basis, Fourier orthogonality gives orthonormality.

For pure ψ the collision identity is Σ_{b,i}p_{bi}²=2. Indeed the four real two-dimensional spaces of traceless diagonal Hermitian matrices in each basis are orthogonal by mutual unbiasedness, and their dimensions sum to eight. Decompose ρ−I/3 into the corresponding diagonal projections; its squared Hilbert–Schmidt norm is 2/3 and each projection has squared norm Σ_i(p_{bi}−1/3)². For x>0 put g(x)=x(2x−1−log(2x))≥0 and g(0)=0. Then exactly

$$4(\bar H_0(\psi)-\log 2)=\sum_{b,i}g(p_{bi}).$$

Thus equality requires exactly one zero and two halves in each basis. With computational missing index k and support i<j, the required zero Fourier amplitude fixes the relative phase. The nine possible rays are v=(e_i−ω^m e_j)/√2 (m=0,1,2). Conversely in every B_a the three relative phases are {1,ω,ω²}, so their outcome probabilities are 0,1/2,1/2. The nine rays exhaust the minimizers.

**2. Local analysis at a minimizing ray.** Fix one such v and its uniquely zero outcome w_b in each basis b at t=0. Each w_b is perpendicular to v. On the tangent space v^⊥ set A z=(〈w_b,z〉)_b. The frame operator A*A=2I on v^⊥ since it has trace 4 and squared trace moment 4+12/3=8 on a space of dimension 2. Hence the projection onto ran A is P=AA*/2, with every diagonal entry 1/2. Denote the last coordinate vector of C⁴ by e_4. The first derivative of the fourth zero amplitude at (t,z)=(0,0) in t is β=−i〈w_4,h v〉, h=diag(0,1,2), and |β|=|i−j|/√6 (i,j here are the coordinate indices, not the imaginary unit). This follows because the two supported terms in 〈w_4,v〉 cancel and each has modulus 1/√6.

In a neighborhood of v use ψ(z)=(v+z)/√(1+||z||²), z∈v^⊥. Write r=(||z||²+t²)^{1/2}. The vector of the four formerly zero amplitudes satisfies, uniformly nearby,

    a(t,z)=A z+t β e_4+O(r²).

The real-linear map (z,t)↦Az+tβe_4 is injective: (I−P)e_4 has norm 1/√2, β≠0, and A has trivial kernel. Consequently c r²≤Σ_b |a_b|²≤C r² for small r, with fixed c>0. The two other probabilities in each basis equal 1/2+O(r) and sum to 1−|a_b|². For h₀(x)=−x log x the linear Taylor terms around 1/2 therefore sum to O(r²), and the second derivative is bounded in the neighborhood. For q_b=|a_b|², one also has

    Σ_b (−q_b log q_b) = (Σ_b q_b) log(1/r²)+O(r²)

because q_b/r² lies in a fixed compact interval including zero and x log x is bounded there. It follows that, for the four-basis entropy sum,

$$
4(\bar H_t(\psi(z))-\log 2)
=\|Az+t\beta e_4\|^2\log(1/r^2)+O(r^2).
\tag{Q2}
$$

Here the O(r³) error in Σ q times log(1/r²) is O(r²). Since there are only nine rays, take uniform constants in their neighborhoods.

**3. Minimizing over moving states, not just the nine rays.** By compactness/continuity, any minimizer for t→0 lies in the union of the above neighborhoods and approaches the nine-ray set: H̄_t converges uniformly to H̄_0, and outside any fixed neighborhood there is a strict gap. At z=0 the upper cost is O(t² log(1/t²)). By (Q2) and injectivity the lower cost for a minimizer is ≥c' r² log(1/r²) for r sufficiently small. Together these imply r=O(|t|): x²log(1/x²) increases near zero, and for any fixed K its value at K|t| divided by its value at |t| tends to K², so take K larger than the ratio of the comparison constants permits.

Write z=t y, with y uniformly bounded. Equation (Q2) now reads

    4(H̄_t(ψ(t y))−log 2)=t² ||Ay+βe_4||² log(1/t²)+O(t²)

uniformly for bounded y. At v the minimum of ||Ay+βe_4||² over complex y is |β|²||(I−P)e_4||²=(i−j)²/12. Fitting the least-squares y provides the matching upper test state. Taking the minimum over the nine rays gives 1/12 before the factor of four, proving (Q1). ∎

## A fully specified algebraic unitary

Use the four bases above with D=diag(1,z,z²), z=(1+iu)/(1−iu), u=2^{−1000000}. All basis entries are algebraic. Equivalently D=D_t with 0<t=2 arctan u≤2^{−999999}. The intentionally small angle makes the estimates simple, not numerically optimal. This independent direct inequality does not require any optimization or floating-point computation.

Suppose a pure state ψ has H̄_t(ψ)≤log 2. The derivative of −x² log(x²) on [0,1] extends continuously at 0 and has absolute value at most 4 (indeed at most 2). Each outcome amplitude modulus in the fourth basis changes by at most ||D_t−I||≤2t. The entropy average therefore changes by at most 6t. The gap identity above gives Σ g(p)≤24t for the unperturbed probabilities, and each summand is nonnegative. On (0,2] the function y−1−log y has second derivative ≥1/4, hence

    g(p) ≥ p(2p−1)²/8.

Thus p<1/4 implies p≤768t, while p≥1/4 implies (2p−1)²≤768t. Each basis must have at least one p<1/4: otherwise each probability is ≥(1−√(768t))/2>1/3. Select one such coordinate outcome and one such Fourier outcome. Let v be the ray orthogonal to these two vectors. It is one of the nine listed rays by solving the coordinate/Fourier equations. Fix the phase so that ψ=a v+η, η⊥v, a≥0; put s=||η||. The two chosen vectors span v^⊥, and the sum of their projectors has minimum eigenvalue there 1−1/√3>2/5. Hence

    s² ≤ (5/2)(768t+768t) ≤ 4096t,           a=√(1−s²)>1/2.

For each basis let q_b be the perturbed probability of the formerly zero outcome of v, and put R=Σ q_b, D²=s²+t² (here D² names a scalar, not the unitary). From the first two fixed outcomes s²≤(5/2)R. For the fourth basis vector w at its former zero, the two original nonzero terms in 〈w,v〉 canceled. Thus |〈D_t w,v〉|=2|sin((j−i)t/2)|/√6≥t/4 (e.g. sin x≥3x/4 on [0,1/10]). This gives √R≥a t/4−s and t≤8(s+√R)≤24√R. In particular 0<D²≤600R. Also ||ψ−v||≤2s, so every formerly zero probability satisfies q_b≤(2s+2t)²≤8D². Each of the eight formerly nonzero probabilities p' differs from 1/2 by at most 4(s+t), since squared moduli of unit-bounded amplitudes are 2-Lipschitz. All are in [1/4,3/4] by s²≤4096t.

On [1/4,3/4], h(x)=−x log x has h''≥−4. The linear Taylor terms at 1/2 in each of the four pairs sum to −h'(1/2)q_b≥0. Their eight quadratic remainders in total are at least −2·8·16(s+t)²≥−512D². The four remaining entropies total ≥R log(1/(8D²)). Therefore

    4(H̄_t(ψ)−log 2) ≥ R [ log(1/(8D²))−512·600 ] > 0,

where D²≤4097t, 8·4097<2^16, t≤2^{−999999}, and (999999−16)log 2>307200. This contradicts the supposition. The minimum strictly exceeds log 2 by compactness. This proof also works for the full nonzero interval 0<t≤2^{−999999}. ∎
