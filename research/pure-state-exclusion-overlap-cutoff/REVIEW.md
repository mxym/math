# Independent mathematical review: the maximum pure-state overlap cutoff

**Internal AI review, not external peer review. PASS on the stated qualitative cutoff; emphasize the prior-art specialization below.** Reviewed initial proof snapshot SHA256 c14ed008cbfb4084182881202fd8b5a81e1eb8bd772021dcb341febf9c4cad27. The version of PROOF.md distributed here adds the checked prior-work clarifications below and edits the presentation, so its file digest differs. No claim of priority, optimal positive gap, or new exclusion criterion.

## 1. Problem and limiting argument

The original problem is in [Johnston–Russo–Sikora, §6](https://arxiv.org/html/2311.17047), concerning their Corollary 5.4 and ordinary exclusion of pure states by one joint POVM, not exclusion of measurements, strong exclusion, or the Frobenius criterion. Zero effects are permitted. Their cap on the *absolute* pairwise inner product is the square root of the cap s=(n−2)/(2(n−1)) in the draft. The existing [trureturing formal result](https://github.com/the-omega-institute/trureturing/blob/74acadd20e08e9582da3ab1767a129b2145a8695/D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight.lean) gives a stronger, quantitative gap for n≥10. No Lean replay was performed for this review.

A sequence of bad tuples with maxima decreasing to the infimum always exists (identical tuples are bad, so this is a nonempty infimum). Its fixed-size Gram matrices lie in a compact set independent of Hilbert-space dimension, and continuity of the Gram entries and eigenvalues suffices. The strict reverse of the JRS sufficient spectral criterion holds for each failure, hence its **closed**, non-strict version holds in the limit. It is unnecessary and would be incorrect in general to assume failure of the limit tuple. For T=p₀, u=∑yᵢ², yᵢ=√pᵢ over tails, the expansion

    2∑pᵢ²−(∑pᵢ)² = (T−u)²−4∑_{i<j}yᵢ²yⱼ²

is exact. By the closed reverse spectral inequality, T−u≥2∑_{i<j}yᵢyⱼ≥0. Purity is at most 1/2 by the cap; the displayed quantity must be zero. If three tails are positive there are at least two strictly positive pair products and the square of their sum strictly exceeds their sum of squares. Hence rank at most three; purity saturation makes each individual squared overlap equal s. The projectors have invertible Gram (1−s)I+sJ, so rank of G is exactly three for n≥5. The top normalized eigenvalue b belongs to (1/2,2/3]: the lower endpoint is excluded by positivity of three masses with purity 1/2, while √b ≤ √(2(1−b)) follows from equality in the square-root formula. There is no common positive uniform margin asserted over all n.

## 2. Why the qutrit projection works, including n=6

In Herm(3) over the real scalars, the centered projectors Tᵢ=Pᵢ−B sum to zero, are orthogonal to I and B, and are a simplex with frame constant 1−s. Thus for a real orthonormal basis {Hₐ} of their span, ∑Hₐ²=n(B−B²)/(1−s). This expands in matrix order as ∑ₐᵦ (DDᵀ)ₐᵦHₐHᵦ; off-diagonal terms genuinely cancel, with no commutativity assumption. Let e be a top unit eigenvector of B. For an orthonormal basis of all Herm(3), ∑‖H e‖²=3 (in a basis diagonalizing B, the diagonal matrix unit contributes 1, and four off-diagonal terms contribute 1/2 apiece). Orthogonal to the Tᵢ, I/√3 and √6(B−I/3) are orthonormal since tr B²=1/2 and tr B=1. Bessel therefore gives

    0 ≤ 3−1/3−6(b−1/3)²−2(n−1)b(1−b)
      = 2(1−b)(1−(n−4)b).

Since 1/2<b<1, this is impossible for every n≥6, including n=6. This scalar check independently avoids any concerns regarding the order of noncommuting operators in the draft. For n≥9 there is even the dimension shortcut dim W=n−1 and dim(W perpendicular)≥2 in the real 9-dimensional Herm(3). The compactness contradiction proves a nonzero gap for each fixed n; it does not estimate the gap.

## 3. Five states: positivity, endpoint and strict perturbation

In the formula of the manuscript, a(1−a)=bc=1/8, b+c=1−a, and b>1/2 follows by evaluating the defining quadratic at 1/2. The positive discriminant and product guarantee c>0, and c=1/(8b)>1/[8(1−a)]=a. The distinct fifth-root Fourier offsets each yield squared overlap 3/8. At purity 1/2, (b−a−c)²=4ac and b>1/2 selects the positive sign. After transferring a positive fraction of weight into the b coordinate the strict reverse triangle inequality holds for the amplitudes. This makes the perturbed tuples **actually non-excludable**, not just outside a sufficient spectral test: averaging any POVM over the cyclic group produces a covariant seed with all three diagonal entries 1/5; zero response forces a combination of three columns of equal norm with amplitude coefficients to vanish, inconsistent with the strict reverse triangle inequality. The same argument is unchanged if one begins in a larger space and compresses to the span. The unperturbed tuple is excludable, as required.

As an independent algebra check: use *amplitudes* proportional to (1,1+t,t) for t the unique real zero in (1,2) of t⁴+2t³−t²−2t−1. For A=1,H=(1+t)²,C=t²,D=A+H+C one obtains A(H+C)=HC=D²/8 and (A²+H²+C²)/D²=1/2. Apply the same cyclic phases to the second and third coordinates. This gives the four required overlaps by reduction modulo the fifth cyclotomic polynomial. Replacing the dominant amplitude by 1+t+η and normalizing, for η>0, violates the amplitude triangle strictly while approaching the endpoint. independent.py verifies these identities without calling the author's verifier; it also checks the scalar projection inequality algebra and 2,047 exact spectra. It was run under python -B -O and uses explicit exceptions, not Python assert.

## 4. Attribution correction: cases n=7,8,9 via prior spectral tools

[Balla, *Equiangular lines via matrix projection*, arXiv:2110.15842v5](https://arxiv.org/abs/2110.15842v5), Theorem 2.3 and **Lemma 4.3** in the complex section, give a previous spectral constraint. Here r is the ambient complex dimension, n is the number of vectors, α is the common **modulus** of the inner product, and λ is an eigenvalue of the ordinary unit-diagonal Gram matrix. Set s=α², d=1+(n−1)s and k=(1−s)/s. Summing Theorem 2.3 over vector labels for a unit λ-eigenvector gives

    λ³−d(n+k)λ + ndk ≥ 0.

Lemma 4.3 states it for the largest eigenvalue, all that is needed. At the present s=(n−2)/(2(n−1)), d=n/2, k=n/(n−2), λ=nb, the prior inequality reduces to

    f(b)=b³−[(n−1)/(2(n−2))]b+1/[2(n−2)] ≥ 0.

For n≥6 it is increasing on [1/2,2/3]; at 2/3 its value is (13−2n)/(54(n−2)). This excludes every n≥7 by the limiting argument of §1. For n=6 this endpoint value is positive and this particular cubic comparison does not suffice. The author's projector proof covers n=6 as well. Accordingly, identify 7–9 as readily deduced by combining older spectral ingredients; distinguish this observation from finding a prior paper explicitly answering JRS. No determination of priority for five lines in complex dimension three is possible from the public abstract alone of [Et-Taoui–Lehbab–Makhlouf (2024)](https://doi.org/10.1515/advgeom-2024-0025). An equiangular tight-frame classification is not by itself applicable: the limiting qutrit frame is non-tight since its nonzero normalized eigenvalues are not all 1/3. The centroid/frame projection method has precedents and is not itself new.

## 5. Prior-tool addendum to the independent review

The author subsequently identified a prior-tool route that covers six states too. Independently checked: PASS. This refines the attribution, not the verdict on the manuscript's direct centroid argument.

For unit vectors in three complex dimensions the positive semidefinite projective zonal kernel on squared overlaps t is K(t)=P₂^{(1,0)}(2t−1)=10t²−8t+1. See Delsarte–Goethals–Seidel, *Bounds for systems of lines* (1975), Theorem 3.3 (addition formula), or [Cohn–Kumar–Minton (2016), §2 before Proposition 2.5](https://msp.org/gt/2016/20-3/gt-v20-n3-p03-s.pdf). Off-diagonal overlaps of a boundary code are all s=(n−2)/(2(n−1)); summing every entry of the kernel matrix and dividing by n gives

    3+(n−1)K(s) = −n(n−6)/(2(n−1)).

For n≥7 this contradicts positivity directly. For n=6 the sum vanishes. Append an arbitrary unit test vector e, and extend the all-ones vector with one zero. Its quadratic form still vanishes, so the extended positive matrix annihilates that vector. Looking at its last row gives 0=∑K(|⟨e,vᵢ⟩|²). For a unit top eigenvector e of the mean projector B, the mean of these six overlap squares is b=λmax(B). Convexity gives K(b)≤0, so b≤(4+√6)/10<13/20. On the other hand [Balla, arXiv v5, Lemma 4.3](https://arxiv.org/abs/2110.15842v5) above gives g(b)=8b³−5b+1≥0. This polynomial is strictly increasing on [1/2,2/3] and g(13/20)=−53/1000<0. This rules out six as well.

Thus on the quantum boundary reduction, the six-through-nine obstructions may also be deduced by combining prior geometric inequalities. It does not follow that an earlier publication gave the stated exact qualitative JRS cutoff.

**Further simplification for six, independently checked.** The classical projective kernel in fact suffices by itself; the comparison with Balla is optional. Apply the same test at each unit eigenvector eⱼ of B. Jensen gives K(bⱼ)≤0 for all three eigenvalues; equiangularity at s=2/5 gives tr B²=1/2 directly. Consequently ∑K(bⱼ)=10tr B²−8tr B+3=0, so every eigenvalue must equal one of (4±√6)/10. If the plus sign occurs k times then 10tr B=12+(2k−3)√6 cannot equal 10 for k∈{0,1,2,3}. This rules out even the underlying six-line configuration at this angle in complex dimension three, without further quantum spectral assumptions. The branch connecting the quantum spectral limit to equiangular lines of dimension at most three is still required.
