# Exact finite-dimensional APPT purity in sufficiently rectangular systems

Research working proof, 10 October 2026. No preprint or Release preparation. The proof below is analytic and does not rely on finite verification or the multiscale asymptotic lower bound. No Lean or external peer-review claim is made.

## 1. Result and its relation to the counterexamples

Let 3<=m<=n be integers, D=mn, and t=ceil((m-1)n/2). If

    n >= n0(m) := m^3-m-2,

then the unrestricted APPT maximum is EXACTLY

    Pmax(m,n) = [D(m-1)^2+4mt]/[D(m-1)+2t]^2.                  (E1)

Every maximizing state, and no other APPT state, has the spectrum

    (m+1 [t copies], m-1 [D-t copies])/[D(m-1)+2t].             (E2)

Equivalently all maximizers are the global unitary orbit of
`((m-1)I+2P)/[D(m-1)+2t]`, where rank(P)=t. This proves an exact finite-dimensional result, not just the first term of a limit or an optimization restricted to two levels.

The cutoff n0 is a sufficient cutoff for the actual APPT problem and is the exact cutoff for the single-witness outer-polytope method proved below. It is NOT claimed to be the smallest actual APPT cutoff. The previous qutrit theorem is sharper when m=3. This result does not undo the proportional-growth counterexamples; for example m=10,n=38 is below n0(10)=988.

## 2. One necessary physical inequality

Write R=m(m-1)/2 and S=m(m+1)/2, so R+S=m^2 and S-R=m. Let lambda be a decreasing APPT spectrum. For the Schmidt-rank-m maximally entangled unit vector, the partially transposed projector has R eigenvalues -1/m, S eigenvalues +1/m, and D-m^2 zeros. A global unitary assigns the largest R eigenvalues of the state to its negative eigenvectors and the smallest S to its positive eigenvectors. APPT therefore implies

    sum_{i=1}^R lambda_i <= sum_{i=D-S+1}^D lambda_i.            (E3)

This uses actual global-unitary freedom and an actual partial-transpose test, not a sufficient spectral criterion asserted without proof.

Define O(m,n) to be the set of decreasing probability vectors satisfying (E3). It is an OUTER polytope: APPT spectra lie in it, but membership is not sufficient for APPT. We prove the complete finite formula

    max_{lambda in O(m,n)} sum_i lambda_i^2
      =max{Qsp(m,D), Qt(m,D)},                                 (E4)
    Qsp=(D+m(m+2))/(D+m)^2,
    Qt=[D(m-1)^2+4mt]/[D(m-1)+2t]^2.

The new upper-bound mechanism is (E4). The formula Qt and its two-level attaining state are existing candidate spectra in Ahiable--Kothakonda--Winter; no first prediction of that value is claimed.

## 3. All vertices of the outer polytope

Let L=D-m and u_i=(1/i [i copies],0 [D-i copies]). The ordered probability simplex has the unique gap expansion

    lambda=sum_{i=1}^D x_i u_i,
    x_i=i(lambda_i-lambda_{i+1})>=0, sum_i x_i=1, lambda_{D+1}=0.

The left side minus right side of (E3), evaluated at u_i, is g_i=h_i/i, where

    h_i=min(i,R)-max(0,i-(D-S)).

It is positive for i<L, zero for i=L, and negative for i>L. A simplex cut by this one halfspace has only the following vertices: the surviving u_j (j>=L), and the boundary point on each edge [u_i,u_j] with i<L<j. To see completeness, a point with at least three positive gap coordinates can be perturbed nontrivially while preserving both affine constraints if on the cutting plane; if off that plane, two coordinates suffice to perturb. Thus such points are not vertices. The stated points exhaust supports of size one or two. The finite-dimensional convex-hull theorem then gives the desired decomposition of every point. Convexity of squared Euclidean norm reduces its maximum to these vertices.

For an edge vertex put j=D-z=L+s, where 0<=z<m and s=m-z is in {1,...,m}. Let h=h_i>0. The spectrum is

    alpha=(h+s)/(hj+si)  on the first i slots,
    beta=h/(hj+si)       on the next j-i slots,
    zero                on the remaining z slots.              (E5)

Indeed the uniform baseline on its support has constraint -s beta, while the increment on the first i coordinates has constraint h(alpha-beta). Equation (E5) satisfies both trace one and zero constraint. The pure surviving vertices have purity 1/j<=1/L.

### 3.1 The early indices i<=R

Here h=i, and the purity is

    [j+2s+s^2/i]/(j+s)^2 <= [L+3s+s^2]/(L+2s)^2 = f(s).

This inequality is strict for i>1. The derivative is

    f'(s)=[(2L-6)s-L]/(L+2s)^3.

Its numerator is increasing (L>=6). Thus f has no strict interior maximum on [0,m]; it first decreases and then possibly increases. Every such vertex is bounded by

    max{f(0),f(m)}=max{1/L,Qsp}.                                (E6)

### 3.2 The middle indices R<=i<=D-S

Here h=R. At fixed i the purity, extended to real 0<=s<=m, is

    F_i(s)=[R^2 L+(R^2+2Ri)s+i s^2]/[RL+(R+i)s]^2.

Its derivative has the sign of

    (2Li-R^2-3Ri-2i^2)s-LR^2.                                 (E7)

The constant term is strictly negative. If the coefficient of s is nonpositive, the function decreases throughout; otherwise its derivative changes sign at most once, from negative to positive. Therefore

    F_i(s)<=max{F_i(0),F_i(m)}=max{1/L,F_i(m)}.                  (E8)

For 0<s<m the inequality is strict relative to the larger endpoint value. Importantly i remains in the same valid middle interval when s changes; no infeasible endpoint is being substituted.

At s=m this is the full-support two-level spectrum, and

    F_i(m)=[D(m-1)^2+4mi]/[D(m-1)+2i]^2.

The derivative with respect to i is

    4m[(m-1)n-2i]/[D(m-1)+2i]^3.

Its unique real maximum is i*=(m-1)n/2. It belongs to [R,D-S]; its ceiling also belongs because the endpoints are integers. When i* is a half-integer, put H=(m^2-1)n. Exact subtraction gives

    F_{ceil(i*)}(m)-F_{floor(i*)}(m)=4m/(H^2-1)^2>0.             (E9)

Thus the unique integer maximizer is t=ceil(i*), and the middle maximum is Qt.

### 3.3 The late indices D-S<i<L

Here h=L-i, and (E5) simplifies to alpha=1/L, beta=h/[L(h+s)]. Its purity is

    [i+h^2/(h+s)]/L^2 <(i+h)/L^2=1/L.                         (E10)

The three cases prove a maximum of max{1/L,Qsp,Qt}. For m>=3,D>=m^2,

    Qsp-1/L=m[(m-1)D-m(m+3)]/[(D-m)(D+m)^2]>=0.                (E11)

At the smallest D=m^2 its numerator is m^2(m-3)(m+1)>=0. This proves (E4).

## 4. The exact branch transition of the outer bound

Put B=m^4-m^2-2m=m*n0(m), and u=m^2-1. The continuous middle maximum is C=m^2/(uD). Its difference from Qsp is

    C-Qsp=[D^2-BD+m^4]/[uD(D+m)^2].                            (E12)

If m<=n<n0(m), then m^2<=D<=B-m. The quadratic numerator is convex and negative at both endpoints:

    F(m^2)=-m^3(m-2)(m+1)^2<0,
    F(B-m)=-m^2(m^3-m^2-m-3)<0.

For the latter sign, at m=3+y the bracket is y^3+8y^2+20y+12. Convexity implies negativity throughout the interval. Therefore Qt<=C<Qsp for every integer n in this lower range.

If n>=n0(m), then D>=B and the numerator in (E12) is at least m^4. There is no parity loss when (m-1)n is even. In the other case, with H=un=uD/m, exact arithmetic gives

    Qt=m(H+2)/(H+1)^2,
    0<C-Qt=m/[H(H+1)^2]<=m^4/(u^3D^3).                        (E13)

Consequently

    Qt-Qsp >= m^4/[uD(D+m)^2]-m^4/[u^3D^3]>0,

where positivity follows from uD>D+m, true for m>=3,D>=m^2. Thus (E4) chooses Qt strictly if and only if n>=n0(m). These bounds include all rounding parities, not only even n.

## 5. Physical attainment and all equality cases

Let P be any rank-t orthogonal projection. The matrix A=(m-1)I+2P is positive definite and has the trace and spectrum in (E2). For an arbitrary unit Schmidt vector with coefficients s_i,

    sum_{i<j}s_i s_j=((sum_i s_i)^2-1)/2 <=(m-1)/2.

For W the partial transpose of its projector and any conjugated projection P', the trace Tr(P'W) is at least minus this sum, by diagonal weights in [0,1]. Hence every unitary conjugate of A has nonnegative partial transpose. Dividing by its trace proves actual APPT attainment of Qt.

For n>=n0, Qsp and every non-middle-endpoint vertex are strictly suboptimal by Sections 3-4. Among full-support middle vertices, (E9) gives the unique maximizer i=t. Squared norm is strictly convex: for distinct spectra u,v and 0<theta<1,

    theta||u||^2+(1-theta)||v||^2-||theta u+(1-theta)v||^2
      =theta(1-theta)||u-v||^2>0.

Thus no nontrivial convex combination of other vertices can also maximize. The unique decreasing maximizing spectrum in O(m,n), and therefore among APPT spectra, is (E2). This proves both (E1) and the complete state-level unitary-orbit classification in this dimension range.

For m<=n<n0, the outer maximum Qsp is attained by the single-spike spectrum `(m+1,1,...,1)/(D+m)` (with a possible surviving-uniform tie at m=n=3). This single-spike spectrum is not APPT: place its distinguished vector on a two-level antisymmetric Bell vector and test a Schmidt-rank-two maximally entangled vector; the unnormalized expectation is 1-m/2<0. Hence the early branch of the relaxation is not a new APPT maximum formula. The n0 cutoff describes this proof method, not a claim that the actual optimum changes precisely there.

## 6. Scope

Resolved: an exact finite-dimensional maximum and all maximizing spectra for every m>=3 and n>=m^3-m-2; and an exact formula for the one-Schmidt-test outer polytope at every m>=3,n>=m. This is independent of the compactness argument used for the joint-growth asymptotic.

Unresolved: the true minimal onset dimension for eventual two-level optimality, the exact maximum in the remaining multilevel regime, and APPT versus absolute separability. The old conjecture is globally false, but its broad-plateau value is exactly correct in the proved rectangular region. The previously frozen qutrit proof is not changed.

The existing candidate spectrum and formula are attributed to Ahiable--Kothakonda--Winter, arXiv:2608.03390v2, Theorem 6.3. Their input is not assumed as a proof of the new upper bound; the entire outer optimization and physical attainment are derived here. A direct primary-version check still showed v2 (18 September 2026); Tran's arXiv:2609.18568v1 is a different outer-polytope purity bound. Literature screening is not exhaustive historical-priority certification. Research used AI assistance.
