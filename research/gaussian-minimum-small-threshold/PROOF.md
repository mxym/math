# The cosine covariance conjecture at all sufficiently small thresholds

AI-assisted research candidate; independently checked internally, not externally peer-reviewed. The target is D. Kunisky, arXiv:2605.02023, Conjecture 3.1, not the older simplex conjecture (disproved there), nor the spherical Conjecture 4.1.

**Theorem.** Fix an integer n≥2. There is a number t_n>0 such that for every n×n real correlation matrix Σ and every 0<t<t_n,
$$
 \Pr[M(Σ)\ge t]\ \ge\ \Pr[M(Σ_{\cos})\ge t],\quad
 M(Σ)=\min_i |X_i|,\quad X\sim N(0,Σ),\quad
 (Σ_{\cos})_{ij}=\cos((i-j)\pi/n).
$$
Equality occurs exactly for simultaneous signed permutations of the cosine Gram matrix. In rank at most two the comparison is true at every t>0. The n=1 statement is tautological. No uniformity in n, effective threshold, conclusion about all thresholds in higher rank, or consequent moment or spherical result is claimed.

Realize the normals u_i in R^n by a Gram factor and let G be standard Gaussian. The one-dimensional marginals have no atoms, so F(U,t)=Pr(min_i |G·u_i|≤t) has no atoms and it suffices to maximize this cdf. Put p(t)=Pr(|N(0,1)|≤t), and A_i={|G·u_i|≤t}. The loss from the union bound is
$$
 D(U,t)=np(t)-F(U,t)=\mathbb E (N-1)_+,\qquad N=\sum_i 1_{A_i}.
$$
Write V_* for the configuration of equally spaced unoriented lines in a plane. All constants below may depend on fixed n.

## 1. Localizing every asymptotic maximizer

Fix any sequence t↓0 and configurations U(t) converging coordinatewise to U^0. Sign and rotation of the normals are immaterial. If two limiting lines coincide, then D(U(t),t)/t²→∞. In fact D≥Pr(A_i∩A_j); write their Gaussian coordinates as Y, ρY+σZ for independent standard Y,Z and σ=√(1−ρ²)→0. The events |Y|≤t/2 and |Z|≤min(1,t/(2σ)) imply joint membership, with product probability at least c t min(1,t/σ) for t≤1 (use 1 when σ=0).

Otherwise all limiting lines are distinct. A flat here means a two-plane spanned by a pair of limiting normals together with the full set I of indices whose limiting normal lies in that plane. Distinct flats share at most one index and partition unordered pairs. In each flat cyclically order its m=|I| projective lines and denote successive gaps by δ_1,...,δ_m (positive, with sum π). Then
$$
 \liminf_{t\downarrow0} t^{-2}D(U(t),t)
 \ \ge\ B(U^0):=\frac1\pi\sum_I\sum_{j=1}^{|I|}\cot(\delta_j/2). \tag{1}
$$
Equality holds in (1) for the constant sequence U(t)=U^0.

To prove this, on the event that no triple of active indices is linearly independent **in the limit**, either ≤1 are active or all are in a unique flat. Thus (N−1)_+ agrees with the sum over flats of (N_I−1)_+ there. The exceptional event has probability O(t³): each independent limiting triple has a 3-variate Gaussian density uniformly bounded for the sequence, and there are finitely many triples. The discrepancy of the bounded counts has expectation O(t³).

On each cyclic flat we have the pointwise inequality
$$
 (N_I-1)_+\ \ge\ \sum_j 1_{A_j\cap A_{j+1}}-1_{\cap_{j\in I} A_j}. \tag{2}
$$
A proper active subset induces a forest in the cycle, and the full set gives equality; for m=2 count the one pair twice and subtract its full intersection. If all normals are precisely coplanar and distinct in their specified cyclic order, equality holds: the active lines are exactly those in one (possibly empty or full) projective-circle arc, hence form a contiguous cyclic block. The adjacent-pair probability divided by t² tends to 2/(π sin δ_j), by the joint Gaussian density continuous at zero with determinant tending to sin²δ_j.

For the all-way term decompose G into x in the limit plane W and independent z in its orthogonal complement. Conditional on z, put x=t y. The allowed set is a section of the strips |(P_Wu_j)·y+b_j|≤1 with offsets b_j=(P_{W⊥}u_j)·z/t. Its area cannot exceed that at zero offsets: if its set is K_b then (K_b−K_b)/2⊂K_0 and planar Brunn–Minkowski applies (empty and null cases are harmless). The Gaussian density of x is at most 1/(2π). Therefore Pr(all)/t²≤area(K_0)/(2π). As t→0 these centered sets are uniformly bounded by two independent projected strips; indicators converge off the finitely many boundary lines to the limiting circumscribed polygon. In the limit it has inradius 1 with outward normals ±u_j. The tangency lengths from successive vertices are tan(δ_j/2), so its area, the half perimeter, is 2Σ_j tan(δ_j/2). For constant coplanar flat data the normalized mass of the centered intersection tends exactly to this area/(2π), by scaling and continuity of the Gaussian density. Applying (2) and 4 csc δ−2 tan(δ/2)=2 cot(δ/2) gives (1).

Strict convexity of cot(δ/2) for δ∈(0,π) implies that the sum in a flat is ≥m cot(π/(2m)), with equality only for equal gaps. The quantity
$$
 r(m)=2\cot(\pi/(2m))/(m-1)
$$
is strictly decreasing for real m≥2: differentiating reduces the assertion to sin y>y(1−y/π) for y=π/m, 0<y≤π/2, which follows from sin y≥y−y³/6 and π²<12. Since Σ_I binom(m,2)=binom(n,2), (1) is at least
$$
 b_n=n\cot(\pi/(2n))/\pi ,
$$
with equality only for all n lines in one flat equally spaced. Equality is attained asymptotically by the constant regular pencil (n=2 included). Compactness of configurations and the preceding sequential statement imply two facts:
(i) sup_U F(U,t)=np(t)−b_n t²+o(t²);
(ii) any sequence t_k↓0 with D(U_k,t_k)≤D(V_*,t_k)+o(t_k²) has distance tending to zero from the regular orbit (signed permutations and O(n)). Otherwise pass to a convergent subsequence separated from that compact orbit and apply (1) or the collision bound. Only (ii) is needed below.

## 2. Exact planar comparison (prior lemma)

This is Proposition 2.1 of [Anonymous, Evidence Press (2026)](https://doi.org/10.5281/zenodo.23453252), including equality. We recall an elementary proof; see [SOURCES.md](SOURCES.md).

Represent n projective directions in a plane by cyclic gaps δ_i≥0 totaling π, allowing repeats. Conditional on the projected Gaussian radius R, the angle is uniform. Each active strip corresponds on the projective circle of circumference π to an arc about the perpendicular direction with half-width α=arcsin(min(t/R,1)). The total uncovered length is Σ_i (δ_i−2α)_+. This is minimized by all δ_i=π/n by Jensen. If the gaps are not all equal, the inequality is strict for an open interval of 2α between the smallest and largest gaps within (0,π), since for every such threshold there are gaps on both linear sides of the kink. The Rayleigh radius has positive density at every R>0, hence this strictness survives integration. This proves the all-t rank≤2 comparison, including coincident lines and the case n=2.

## 3. A strict local transverse estimate

Assume n≥3. Work in a sufficiently small fixed neighborhood of the regular orbit. Take W to be the top-two eigenspace of Σ_i u_i u_i^T, which is well-defined and close to the regular plane: at the latter the two eigenvalues are n/2 and the rest zero, and the corresponding spectral subspace varies continuously across this gap. In a suitable orthonormal basis, signed labelling and cyclic order, write u_i=(a_i,h_i) with a_i∈W, h_i∈W⊥, and use row matrices A,H. Then
$$
 A^T H=0,\qquad L^2=\|H\|_F^2,\qquad
 v_i=a_i/|a_i|,\qquad |a_i|=\sqrt{1-|h_i|^2}.
$$
Invariance of W gives the matrix identity. A is close to the regular row matrix A_* and L is small; this can be arranged uniformly near the orbit by compactness / orthogonal identifications. Write V for the normalized planar configuration v_i. In the chosen cyclic ordering denote Q(U)=Σ_i Pr(A_i∩A_{i+1}) and J(U)=Pr(∩_i A_i) at the given t. By (2), D(U,t)≥Q(U)−J(U), with equality for V.

Uniformly in this neighborhood and for t≤1,
$$
 |Q(U)-Q(V)|\le C t^2 L^2. \tag{3}
$$
Indeed |u_i·u_j−v_i·v_j|≤C L², while adjacent absolute correlations are bounded away from one; on such a compact correlation interval the derivative of the bivariate Gaussian density with respect to correlation is bounded for both coordinates in [−1,1]. Integrate over [−t,t]² and sum.

For real b∈R^n, put
$$
 K_A(b)=\{y\in W: |a_i·y+b_i|\le1\ \forall i\},\qquad
 G(A,t,b)=\frac1{2\pi}\int_{K_A(b)}e^{-t^2|y|^2/2}\,dy.
$$
Here t=0 is also allowed. Conditioning on Z standard Gaussian in W⊥ gives J(U)=t² E G(A,t,HZ/t); and J(V)=t²G(V,t,0) with V now also denoting its row matrix. The centered width inflation due to projection costs at most
$$
 0\le G(A,t,0)-G(V,t,0)\le C L^2: \tag{4}
$$
one has K_V(0)⊂K_A(0)⊂(min_i|a_i|)^{-1}K_V(0), and these polygons have uniformly bounded area.

The signed-cycle operator below also appears in Theorem 1.1 of the cited Evidence Press note for a different functional (absolute moments). No novelty is claimed for the matrix or its eigenvalues. Here the object to be controlled is a Gaussian polygon-section probability uniformly down to threshold zero.

**Offset lemma.** There exist c>0 and fixed neighborhoods of A_* and t=0 such that, for every b with A^T b=0,
$$
 G(A,t,0)-G(A,t,b)\ \ge\ c\min(|b|^2,1). \tag{5}
$$
Here 0≤t<t_0. To see the strict quadratic part, first evaluate at A_*,t=0. Write Δ=π/n, e_j=(cos(jΔ),sin(jΔ)), j=0,...,2n−1. A small perturbation of the 2n support distances s_j of the regular polygon preserves all edges and consecutive intersections as its vertices. For cyclic subscripts its area is
$$
 \sum_{j=0}^{2n-1}\left[s_js_{j+1}\csc Δ-\tfrac12(s_j^2+s_{j+1}^2)\cot Δ\right].
$$
Indeed the piece of edge j facing its two neighbors has length (s_{j-1}+s_{j+1}−2s_j cos Δ)/sin Δ, and area is half the sum of edge length times support when the origin is interior. For s_j=1+w_j, w_{j+n}=−w_j coming from the offsets (w_j=−b_j on the first half), the linear term vanishes. Its quadratic form is
$$
 \frac{1}{\sin Δ}\sum_j(w_j w_{j+1}-\cos Δ\,w_j^2).
$$
On the length-2n Fourier modes indexed by k its eigenvalues are [cos(kΔ)−cos Δ]/sin Δ; antiperiodicity selects exactly odd k. The two translation modes k=1,2n−1 are the columns of A_* on the first half. Every other odd k has a strictly negative eigenvalue, so the Hessian of G(A_*,0,0) is strictly negative definite on ker A_*^T.

The b-Hessian is jointly continuous for A near A_*, t and b small. In detail, at the regular polygon the intersection of each consecutive pair of supporting lines satisfies all nonincident inequalities strictly, all edge lengths are positive and the origin is interior. These conditions persist uniformly in a neighborhood. The 2n consecutive intersections, smooth in the oriented normal entries and offsets since their determinants stay nonzero, remain the vertices with unchanged cyclic order: the boundary segments join consecutive surviving vertices on their supporting lines and form a bounded convex polygon satisfying all inequalities. Triangulate it from the origin. On the fixed triangle {s,r≥0:s+r≤1}, each integral has integrand e^{−t²|s y_j+r y_{j+1}|²/2} times the positive determinant of adjacent vertices, all smooth. Differentiation under these bounded-domain integrals proves the continuity, including t=0. By compactness of the unit sphere, strict negativity persists with a uniform bound on all unit d∈ker A^T: otherwise take convergent parameters and unit directions tending to a vector in ker A_*^T. Evenness in b gives zero first derivative at 0. Integrating the second derivative along each such ray yields G(0)−G(b)≥c_1|b|² for |b|≤b_0, with the A,t arguments suppressed.

For larger offsets, G is nonincreasing along every ray from zero. For each centered disk B_R, the fiber K_A(λb)∩B_R contains the Minkowski combination ((1+λ)/2)(K_A(b)∩B_R)+((1−λ)/2)(−K_A(b)∩B_R) for 0≤λ≤1. Planar Brunn–Minkowski gives area at least that at b. Layer-cake in R gives this monotonicity for the centered Gaussian weight too (or just area at t=0). Truncating the ray at radius b_0 and adjusting c proves (5). This proof requires a bound only on the particular transverse rays, not uniform strictness along translations.

Now HZ lies in ker A^T. For L>0 the nonnegative Y=|HZ|² has EY=L² and EY²=L⁴+2 tr[(H^TH)²]≤3L⁴. By Cauchy–Schwarz on {Y≥L²/2}, this event has probability at least 1/12. Consequently (5) implies, shrinking constants if necessary,
$$
 \mathbb E[G(A,t,0)-G(A,t,HZ/t)]
 \ \ge c'\min(L^2/t^2,1). \tag{6}
$$
Combining (2)–(6) gives
$$
 D(U,t)-D(V,t)\ \ge\ t^2\left[c'\min(L^2/t^2,1)-C'L^2\right].
$$
Choose t_0 and the fixed configuration neighborhood so that C't_0²<c' and C'L²<c' throughout. This difference is strictly positive whenever 0<t<t_0 and L>0, in both regimes L≤t and L>t. When L=0, U is already planar and Section 2 gives the exact comparison with V_* as well as equality.

## 4. Conclusion

There cannot exist t_k↓0 and non-regular U_k with D(U_k,t_k)≤D(V_*,t_k): by Section 1 these approach the orbit and fall in the uniform neighborhood of Section 3, where that section and Section 2 give strict inequality in the opposite direction. This is the claimed uniform interval and the equality assertion. Existence of the optimum at each fixed threshold also follows from compactness and almost-sure continuity of the indicators off finitely many linear level surfaces. No limiting differentiation in a nearly singular covariance matrix is used.
