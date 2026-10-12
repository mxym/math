# A sharp source-scale / target-complexity envelope at the critical boundary

Research continuation, 8 October 2026. Complete candidate analytic argument, not independently reviewed or published. No new audit, formalization, or external write was performed. The potential estimate (P) remains an explicit imported theorem.

## 1. New statement, exact quantifiers, and inherited inputs

Fix d >= 2 and p > 2. Write

    s = p/(p-2), beta = s-1 > 0, s' = p/2.

Let L be positive and C^2 on (0,a_*), and put ell = log L. Assume

    x ell'(x) -> 0,    x^2 ell''(x) -> 0              (SV)

as x decreases to zero. Construct a single fixed probability density f on (0,infinity) which agrees, on a sufficiently short initial interval, with

    f(x) = c x^(s-1) L(x) exp(-x^2/2),

and whose negative logarithm is C^2, 1-strongly convex, and quadratic up to a linear term in the far tail. This is possible: the prescribed second derivative is

    1 + beta/x^2 - ell''(x) >= 1 + beta/(2x^2)

near zero. Extend this continuous second derivative while keeping it at least one, make it equal to one in the far tail, and integrate twice with the matching value and first derivative. Normalize afterward. The source in this note is the fixed product

    rho(dx) = f(x_1) product_(j=2)^d g(x_j) dx,
    g(z) = c_g exp[-1/(1-z^2)] 1_{|z|<1}.

It is absolutely continuous, 1-strongly log-concave on its extended convex support, and has all positive moments. It does not vary with N or w. No full-support smoothness across x_1=0 is asserted.

For a probability mu, T_mu denotes its quadratic Brenier map from rho. Let

    C_(p,N) = {mu: #supp(mu) <= N, integral |y|^p dmu <= 1},
    Omega_N(w) = sup { ||T_mu-T_nu||_(L^2(rho)):
                       mu,nu in C_(p,N), W_2(mu,nu) <= w }.

Support counts distinct positive-mass atoms. Coincident labels are merged and zero-weight labels discarded. Locations are unrestricted, the two supports need not agree, and no lower bound on atom masses is imposed.

Choose a sufficiently small FIXED a > 0. Its choice, made more precisely below, depends only on the fixed source and p. Define

    t_j = a 2^(-j),     a_j = L(t_j),                 j >= 1,
    A_N(K) = sum of the largest min(N,K) members of {a_1,...,a_K},
    W_(N,K) = t_K^(3/2) A_N(K)^(1/(2s)),             K >= 1.

The choice of a can ensure that W_(N,K) is strictly decreasing in K, tends to zero, and its adjacent ratios are bounded above and below by constants in (0,1), simultaneously for EVERY integer N >= 1. Moreover W_(N,1) is independent of N. For 0 < w < W_(N,1), set

    K_N(w) = min {K >= 1: W_(N,K) <= w}.

### Theorem A: sharp finite-complexity envelope for arbitrary (SV) factors

There exist c,C,w_0 > 0 depending only on p,d and this one fixed source, such that, simultaneously for every integer N >= 3 and every 0 < w <= w_0,

    c w^(1/3) A_N(K_N(w))^(1/(3s))
      <= Omega_N(w)
      <= C w^(1/3) A_N(K_N(w))^(1/(3s)).             (1.1)

The upper bound holds also for N=1,2. The matching general lower bound is claimed only for N>=3. For N=1 the exact modulus is min(w,2). A separate binary lower argument extends the logarithmic corollary below to N=2 when its logarithmic exponent gamma is nonnegative. No general binary classification or fixed/minimum-mass theorem is asserted here.

The source need not have a monotone L. The largest dyadic source weights may come from widely separated scales. In particular, (1.1) is not obtained by replacing L with its value at the smallest scale.

### Imported potential hypothesis

All upper bounds use the centered-potential statement

    inf_b ||U_mu-U_nu-b||_(L^2(rho)) <= K_rho W_2(mu,nu).       (P)

The displayed source is within the 1-strongly log-concave class of entry 001 v3, Theorem 1.1, which supplies K_rho=sqrt(2). That upstream theorem is not reproved here. The convex-gradient finite-difference estimate is also inherited, with a short derivation recalled in Section 5. Lower bounds use no (P).

The inherited critical-atom proof treats L=1. The earlier slowly-varying supplement treats unrestricted target complexity and sums ALL dyadic weights. The new claim is their jointly uniform, nonmonotone source-scale / finite-complexity envelope, including a matching convex-gradient realization of the selection of the largest source weights. Neither the unrestricted slowly-varying phase diagram nor the L=1 atom-budget law is counted as new.

## 2. Elementary uniform facts about the fixed source

Reduce a until all intervals used below lie inside the prescribed source formula. Choose

    0 < eta < min((s-1)/4, 1/4).

By (SV), a can be chosen so that |x ell'(x)| <= eta on (0,8a). Integration gives

    (x/y)^eta <= L(x)/L(y) <= (y/x)^eta,       0<x<=y<=8a.    (2.1)

In particular adjacent dyadic values have ratios between 2^(-eta) and 2^eta. All fixed-ratio comparisons of L, and hence of f at a fixed-ratio change of x, have constants independent of the scale.

Let F(x)=P(X<x) for X with density f, extended by F(x)=0 for x<=0. The derivative assumption gives

    F(x) ~ (c/s) x^s L(x),    x f(x)/F(x) -> s.             (2.2)

For completeness, integrate x^(s-1)L(x) after writing x=tv. For every fixed v>0, L(tv)/L(t)->1; (2.1) bounds the normalized integrand by v^(s-1-eta), integrable on (0,1). Dominated convergence proves the first assertion, with the exponential tending uniformly to one. The second follows from the displayed density formula. Thus no external regular-variation theorem is needed.

Further reduce a so that

    s/2 <= x f(x)/F(x) <= 2s,                    0<x<=4a,    (2.3)
    |f'(x)| <= C f(x)/x,                         0<x<=4a.

Choose any r satisfying 1/s < r < 1. Let q(u)=F^(-1)(u) for 0<u<=F(a), and q(u)=a for F(a)<u<=1. By (2.2), reducing a if necessary, the logarithmic derivative of q lies between positive constants and is at most r on (0,F(a)]. Across the compact continuation there is a fixed constant C such that

    q(v) >= C^(-1) q(u) (v/u)^r,                0<v<=u<=1. (2.4)

One can prove this directly by integrating d log q / d log u = F(x)/(x f(x)); the constant handles the constant continuation above F(a).

Set

    M(u)=u/q(u)^s.

For u=F(x), 0<x<=a,

    M(F(x)) ~ (c/s)L(x),                                  (2.5)
    d[-log F(x)]/d[log(a/x)] = x f(x)/F(x) in [s/2,2s].    (2.6)

The logarithmic derivative of M with respect to -log u is bounded, and tends to zero at infinity. Consequently M(e^(-B)) has bounded comparison constants on intervals of any fixed length in B. These observations also hold on the finite initial interval 0<=B<=-log F(a), with constants depending on the fixed source.

## 3. The overlap rearrangement and finite-step compression

Use the exact minimum-density weights from 001 v5 / the critical-atom proof. Extend rho's density r by zero. On {r>0}, for each coordinate j and h>0 put

    d_(j,+h)(x) = (1-r(x+h e_j)/r(x))_+,
    d_(j,-h)(x) = (1-r(x-h e_j)/r(x))_+,
    W_(j,h)=6|d_(j,+h)-d_(j,-h)|+2d_(j,+h),
    F_h=max_j W_(j,h).

Set these to zero off {r>0}. Always 0<=F_h<=8. A star denotes decreasing rearrangement on a probability space.

### Lemma 3.1: source quantile majorant

For all sufficiently small h and all 0<u<1,

    F_h^*(u) <= C min{1,h/q(u)}.                            (3.1)

Proof. Near zero, if x>2h, integrate the logarithmic derivative beta/x+ell'(x)-x to bound either first-coordinate deficit by min(1,Ch/x). If x<=2h use the trivial bound one. On the remaining first-coordinate region the fixed extension gives a bound min(1,Ch(1+x)). For a transverse coordinate, integrating the logarithmic derivative of g and treating distance to its boundary <=2h trivially gives min(1,Ch(1-|z|)^(-2)). Thus

    F_h <= C min(1,h B),
    B = 1 + X + 1/X + sum_(j>=2)(1-|Z_j|)^(-2).            (3.2)

The first marginal has a Gaussian tail after a fixed point; the transverse terms have tails bounded by C exp(-c sqrt(t)) for large t. By (2.1)-(2.2), these tails are bounded by C F(1/t). The 1/X term has exactly that tail, and the union bound and fixed-ratio comparisons of F give

    P(B>t) <= C F(1/t)                                   (3.3)

for all large t. Decrease the argument of F by a sufficiently large FIXED factor to absorb C; (2.1)-(2.2), or integration of (2.3), justifies that step uniformly. This gives B^*(u)<=C/q(u) for small u; enlarge C for the compact remaining probability interval. Rearrangement commutes with a nondecreasing continuous truncation, so (3.2) proves (3.1). QED.

### Lemma 3.2: the finite-step compression inequality

For every integer N>=1, every K>=1, and every nonnegative random variable b taking at most N values,

    integral F_(t_K) b d rho
       <= C t_K A_N(K)^(1/s) ||b||_(L^(s')(rho)).          (3.4)

All constants are independent of N,K, the step heights, and their masses.

Proof. The Hardy-Littlewood inequality, which follows immediately by layer cake and min{P(a>t),P(b>v)}, bounds the left side by integral_0^1 F_(t_K)^*(u)b^*(u)du. The decreasing rearrangement b^* is constant on a partition into at most N intervals I_i of lengths m_i. Finite Holder gives

    integral a_h b^* <= Q_h(partition)^(1/s)||b||_(s'),
    a_h(u)=min(1,h/q(u)),
    Q_h(partition)=sum_i m_i^(1-s)(integral_(I_i) a_h)^s.  (3.5)

We prove Q_(t_K)<=C t_K^s A_N(K).

First split the interval partition at u_h=F(h). Splitting a cell can only INCREASE the sum Q: this is the weighted Holder inequality

    (A_1+A_2)^s/(m_1+m_2)^(s-1)
       <= A_1^s/m_1^(s-1)+A_2^s/m_2^(s-1).

On (0,u_h), a_h=1, so the total contribution is u_h<=C h^s L(h). This is at most C h^s A_N(K) when h=t_K.

Consider each remaining interval (v,u) within [u_h,1]. Write B=-log u and z=log(u/v). Inequality (2.4) gives

    integral_v^u q(t)^(-1) dt
       <= C [u/q(u)] min(1,z).

For z<=1, use (2.4) to compare q(t) to q(u) throughout the interval; for z>=1 integrate (u/t)^r, using r<1. Since u-v=u(1-e^(-z)) and 1-e^(-z) is comparable to min(1,z), the contribution of this interval is at most

    C h^s M(u) min(1,z).                                 (3.6)

For each such interval select E_i=[B,B+min(1,z)] on the logarithmic-probability axis. The E_i are disjoint, each has length at most one, and there are at most N+1 of them. The bounded local ratios of M imply

    sum_i M(e^(-B_i))|E_i|
       <= C integral_E M(e^(-B)) dB,   E=union_i E_i.      (3.7)

All of E lies in [0,-log F(h)]. Its part in the fixed interval [0,-log F(a)] has integral bounded by a fixed constant, hence by C a_1 <= C A_N(K).

On the remainder make the change x=q(e^(-B)). Equations (2.5)-(2.6) compare the integrand to L(x) and logarithmic length dB to d log(a/x). An interval E_i of length at most one meets at most Q dyadic x-shells, where Q is a fixed integer depending on s. The union meets at most Q(N+1) shells. Its integral in any one whole shell is at most C a_j by (2.1); shells within [h,a] have indices 1,...,K, up to an irrelevant fixed endpoint convention. Consequently

    integral_E M(e^(-B)) dB
      <= C sum of the largest min{Q(N+1),K} dyadic weights
      <= C A_N(K).                                      (3.8)

The last inequality follows by grouping the decreasingly sorted weights into blocks of size N; at most 2Q+1 blocks are needed, each with sum at most the first block. This comparison keeps the multiplicative loss in N explicit and does not replace the actual transport by an arbitrary step-energy construction.

Equations (3.5)-(3.8), the low-probability cap, and Lemma 3.1 prove (3.4). QED.

The argument proves an upper envelope for actual atomic target energies. Its sharpness as a TRANSPORT estimate still requires the realizations in Section 6; an abstract extremizer of (3.5) is not assumed realizable by a convex gradient.

## 4. The dyadic distance scale is genuinely monotone

The definition of A_N gives

    1 <= A_N(K+1)/A_N(K) <= 1+2^eta.                      (4.1)

Indeed A_N(K) contains at least the last old term a_K, while adding a_(K+1) can increase the largest-N sum by at most a_(K+1)<=2^eta a_K.

It follows that

    2^(-3/2) <= W_(N,K+1)/W_(N,K)
       <= 2^(-3/2)(1+2^eta)^(1/(2s)) =: theta < 1.       (4.2)

The bound theta<1 follows from the stipulated eta; it is uniform in N,K. Thus W_(N,K) decreases to zero uniformly at a geometric rate. Its first value t_1^(3/2)a_1^(1/(2s)) does not depend on N. Set, for example,

    w_0 < min{1, W_(1,1)/2}.

For K=K_N(w), K>=2 and

    W_(N,K) <= w < W_(N,K-1) <= 2^(3/2) W_(N,K).         (4.3)

This establishes the inversion convention without a hidden monotonicity assumption on L. The map-scale sequence t_K^(1/2)A_N(K)^(1/(2s)) is also decreasing under the chosen eta, since 1+2^eta<2^s, although that extra monotonicity is not needed below.

## 5. Transport upper bound

For proper convex u,v finite on the source interior, with square-integrable gradients, the inherited exact minimum-weight estimate is

    ||grad u-grad v||_2^2
      <= 12d delta^2/h^2
         + integral F_h (|grad u|^2+|grad v|^2) d rho,
    delta=inf_b ||u-v-b||_2.                             (5.1)

Briefly, for m_h(x)=min(r(x),r(x+h e_j)), convexity puts the forward difference quotient between the two directional derivatives. The elementary inequality (b-a)^2<=2(b|b|-a|a|) for a<=b and a change of variables yield the weighted derivative error with coefficient 2|m_h(x-h e_j)-m_h(x)|. Three-term squaring supplies coefficient six; the missing weight r-m_h supplies coefficient two. The difference quotient of u-v-b costs at most 4h^(-2)||u-v-b||_2^2. Sum over coordinates. Segments with m_h>0 stay inside the convex source support; no value off that support is needed. Finite-atom potentials have bounded slopes, so all these integrals and representatives are legitimate.

Apply (P). For mu in C_(p,N), b=|T_mu|^2 takes at most N values and

    ||b||_(s')=(integral |y|^p dmu)^(2/p)<=1.

Lemma 3.2 therefore gives, at h=t_K,

    ||T_mu-T_nu||_2^2 <= C [w^2/t_K^2 + t_K A_N(K)^(1/s)]. (5.2)

Choose K=K_N(w). By (4.3), both terms are at most C t_K A_N(K)^(1/s). Since W_(N,K) is comparable to w,

    Omega_N(w) <= C w^(1/3) A_N(K_N(w))^(1/(3s)).          (5.3)

This holds for every N>=1. It includes variable masses, coincident support points after merging, and locations with no individual bound.

## 6. Selecting arbitrary source scales by genuine convex-gradient maps

This is the critical-strip construction of 008, with a new arbitrary-subset moment estimate. The global convex geometry and the two cumulative mass matches are retained exactly.

Fix a nonempty finite set J of dyadic indices and let M=#J. Let K>=max J and choose 0<h<=epsilon t_K, with one sufficiently small epsilon>0 independent of J,K,h. For j in J write

    R_j=t_j^(-beta/2),       S_J=sum_(j in J)L(t_j),       k=1/4.

All windows [t_j-3h,t_j+3h] are positive and disjoint. Their separation is valid even for adjacent dyadic indices; removing some indices only improves it.

### 6.1 Exact masses and local changes

Let Z have density g and be independent of X. Define H_h(y)=E F(y+khZ) and

    ell_j=H_h^(-1)(F(t_j-h)),
    r_j=H_h^(-1)(F(t_j+h)),
    d_j=(ell_j+r_j)/2,        gamma_j=(r_j-ell_j)/(2h).

Bracketing H_h by F(y-kh),F(y+kh) gives endpoint errors <=kh. Symmetry E Z=0, Taylor's theorem, the derivative estimate in Section 2, and a positive lower bound for H_h' on the local window improve this to

    ell_j=t_j-h+O(h^2/t_j),
    r_j=t_j+h+O(h^2/t_j),                                (6.1)

uniformly over ALL selected indices. Let

    A_j={t_j-h<X<t_j+h},
    C_j={ell_j-khZ<X<r_j+khZ}.

The two EXACT identities

    E F(ell_j-khZ)=F(t_j-h),
    E F(r_j+khZ)=F(t_j+h)                                (6.2)

use symmetry for the first equation. They preserve both neighboring cumulative masses, not merely each central mass. Write m_j=rho(A_j)=rho(C_j) and D_j=rho(A_j triangle C_j). Uniformly,

    c h f(t_j) <= m_j,D_j <= C h f(t_j).                  (6.3)

For the lower bound on D_j, the leading symmetric-difference length is 2kh|Z|; the endpoint and density errors are O(f(t_j)h^2/t_j). Thus

    D_j=2kh f(t_j)E|Z|+O(f(t_j)h^2/t_j).

One fixed decrease of epsilon makes the error at most half the positive main term.

### 6.2 Global potentials and all labels

Define convex broken lines

    Phi(x)=sum_(j in J) 2R_j(t_j-x)_+,
    Phi_tilde(x)=sum_(j in J) 2R_j(d_j-x)_+.

They have the same ordered slopes. At each selected cusp let q_j be the midpoint of its two adjacent slopes, and let L_j,L_tilde_j be the corresponding supporting affine lines through the cusps. Set

    U_h(x)=max{Phi(x_1), L_j(x_1)+R_j h : j in J},
    V_h(x)=max{Phi_tilde(x_1),
                L_tilde_j(x_1)+R_j h gamma_j+R_j h k x_2 : j in J}.

These are finite GLOBAL convex functions. The inequality Phi-L_j >= R_j|x_1-t_j|, with equality between neighboring cusps, shows that the raised plane is active exactly on A_j. The analogous assertion gives C_j for V_h. Distinct windows cannot compete. There are M+1 outer slope labels and M central labels, all with positive masses and distinct locations: exactly 2M+1 atoms in each target.

All outer labels are the same in U_h and V_h. Central labels are respectively q_j e_1 and q_j e_1+R_j h k e_2. The separate cumulative matches (6.2) preserve every outer label's mass, including across large skipped-scale gaps, as well as every central label's mass. Therefore the same-label coupling is an actual target coupling and

    ||grad U_h-grad V_h||_2^2
        = sum_(j in J) R_j^2 D_j + k^2 h^2 sum_(j in J) R_j^2 m_j,
    W_2((grad U_h)#rho,(grad V_h)#rho)^2
        <= k^2 h^2 sum_(j in J) R_j^2 m_j.               (6.4)

On a central mismatch the horizontal difference is R_j. The intervals overlap, so no direct crossing between the two outer labels occurs. Their gradients are the actual Brenier maps to the gradient laws, by global convexity. Optimality of the same-label TARGET coupling is not required.

### 6.3 Moment bound that does not pay for skipped scales

Using an integral over every scale between the first and last selected index would be too crude for this theorem. Instead exploit the geometric growth of the selected jumps.

The numbers R_j increase by a factor at least 2^(beta/2)>1 as j runs through J in increasing order. Thus for every subset of such jumps,

    (sum R_j)^p <= C sum R_j^p,                          (6.5)

with C depending only on beta,p. Every active horizontal slope of either potential is bounded by C sum_(j in J) R_j 1_{X<=2t_j}. Endpoint shifts and central cells obey the same bound; their vertical components R_j h k are also absorbed, since h is small and X is comparable to t_j there. Hence pointwise,

    |grad U_h|^p+|grad V_h|^p
       <= C sum_(j in J) R_j^p 1_{X<=2t_j}.             (6.6)

Integrating and using beta p/2=s together with (2.2),

    integral (|grad U_h|^p+|grad V_h|^p) d rho
       <= C sum_(j in J) R_j^p F(2t_j)
       <= C sum_(j in J) L(t_j)=C S_J.                  (6.7)

This estimates only the selected scales. It is the required moment justification for sparse, nonconsecutive scale selection.

Multiply both potentials by lambda=(C_0 S_J)^(-1/p), with one fixed sufficiently large C_0. Each target then has pth moment <=1. Since

    R_j^2 f(t_j)=c L(t_j) exp(-t_j^2/2) ~ L(t_j),

(6.3)-(6.4) imply

    ||T_mu-T_nu||_2 >= c h^(1/2) S_J^(1/(2s)),
    W_2(mu,nu) <= C h^(3/2) S_J^(1/(2s)).               (6.8)

These constants are independent of the selected set, its cardinality, its gaps, its last index, and h in the stated range.

## 7. Uniform matching lower bound and the real atom budget

Fix N>=3 and K=K_N(w). Put n=floor((N-1)/2), and select J from {1,...,K} to consist of the min(n,K) largest dyadic weights. Then

    #supp(mu)=#supp(nu)=2#J+1 <= N,
    (1/4)A_N(K) <= S_J=A_n(K) <= A_N(K).                 (7.1)

The comparison follows by sorting: n>=N/4 for N>=3, and the average of the largest n terms is at least the average of the largest N, with the obvious truncation when K<N. The replacement of N by roughly N/2 is thus a proved fixed-factor comparison, not a dropped atom count.

Set h=epsilon t_K. Decrease the FIXED epsilon, if necessary, so the upper coupling constant in (6.8) times epsilon^(3/2) is at most one. This is compatible with all local estimates. Then

    W_2(mu,nu) <= t_K^(3/2) A_N(K)^(1/(2s))=W_(N,K)<=w,

while

    ||T_mu-T_nu||_2 >= c t_K^(1/2) A_N(K)^(1/(2s))
       = c W_(N,K)^(1/3) A_N(K)^(1/(3s))
       >= c' w^(1/3) A_N(K)^(1/(3s)),                   (7.2)

where (4.3) gives the last inequality. This proves Theorem A.

For each fixed N, only finitely many atoms are used at every w; the selected indices may move with w, as they must when the most adverse source layers move toward the boundary. Source, constants, and the target class stay fixed. The atom weights themselves are permitted to tend to zero, exactly as in the definition of C_(p,N).

## 8. Explicit logarithmic corollary

Take, near zero,

    L(x)=[log(e/x)]^gamma,        gamma any real number.

The source extension above applies. Put B_w=log(e/w), m=min(N,B_w). Uniformly for N>=3 and sufficiently small w,

    Omega_N(w) ~ w^(1/3) times

       B_w^(gamma/(3s)) m^(1/(3s)),          gamma >= 0;
       m^((gamma+1)/(3s)),                   -1 < gamma < 0;
       [log(e+m)]^(1/(3s)),                  gamma = -1;
       1,                                   gamma < -1.  (8.1)

Proof. The sequence a_j is comparable to (j+c)^gamma. For gamma>=0 its largest min(N,K) terms sum to a quantity comparable to K^gamma min(N,K). For gamma<0 its largest terms are the first min(N,K), whose power sum has the three displayed orders. Uniformly in N, the logarithm of A_N(K) is O(log(e+K)), so (4.3) implies K_N(w) is comparable to B_w. Substitution into (1.1) proves (8.1).

At gamma=0 this reproduces the already completed critical atom-budget theorem. Letting N exceed the available scales reproduces the already completed unrestricted slowly-varying hierarchy. The new assertions are the JOINT cutoffs and, in particular, the very different finite-complexity behavior for positive and negative gamma.

### The binary addition for gamma>=0

For N=2 the upper bound just proved applies. Its matching lower bound follows from one rare cell, as in entry 008. Let u>0 be small, m_u=F(u), k=1/4, and choose c_u with

    E F(u(c_u+kZ))=F(u).

Regular variation of F with index s gives c_u->c_0, where E(c_0+kZ)^s=1. The symmetric difference of {X<u} and {X<u(c_u+kZ)} has mass comparable to m_u. The targets

    (1-m_u)delta_0+m_u delta_(-m_u^(-1/p)e_1),
    (1-m_u)delta_0+m_u delta_(m_u^(-1/p)(-e_1+ku e_2)/sqrt(1+k^2u^2))

have pth moment one and are realized by the corresponding two-plane hinge potentials. Their map distance is at least c m_u^(1/(2s)), and the same-label target coupling costs at most C u m_u^(1/(2s)). Since m_u~u^s[log(e/u)]^gamma, inverting the latter expression gives

    Omega_2(w) >= c w^(1/3)[log(e/w)]^(gamma/(3s)).

The inversion is valid for every small w because u F(u)^(1/(2s)) is continuous strictly increasing, with logarithmic derivative tending to 3/2. This matches (8.1) with N=2 when gamma>=0. For negative gamma the same binary lower bound does NOT match the N>=3 formula, and no equality is asserted.

## 9. A fixed-N criterion and optimal complexity constants

Let

    A_N(infinity)=sup_K A_N(K),

possibly infinite. For every fixed N>=3, Theorem A and K_N(w)->infinity imply

    c A_N(infinity)^(1/(3s))
      <= liminf_(w->0) Omega_N(w)/w^(1/3)
      <= limsup_(w->0) Omega_N(w)/w^(1/3)
      <= C A_N(infinity)^(1/(3s)),                        (9.1)

with the natural interpretation that if A_N(infinity)=infinity, the lower limit is infinity. The constants c,C remain uniform in N. No existence of an exact leading-coefficient limit is asserted.

For this source family, a fixed finite atom budget N>=3 restores a pure one-third estimate if and only if L is bounded near zero. Indeed A_N(infinity)<infinity is equivalent to sup_j L(t_j)<infinity, and fixed-ratio comparability (2.1) makes that equivalent to boundedness of L near zero. This differs from the unrestricted criterion, which involves integrability of L(x)dx/x.

When L is bounded, A_N(infinity) is the effective source-weighted complexity controlling the optimal fixed-N constant. It may grow as N, a fractional power of N, log N, or remain bounded; formula (8.1) gives examples. These are consequences for unrestricted atom MASSES, not results for prescribed mass vectors.

## 10. A genuinely nonmonotone example and why endpoint substitution fails

For sufficiently small x set tau=log(e/x) and

    L(x)=exp[sqrt(tau) sin(log tau)].                     (10.1)

The derivatives of log L with respect to tau are O(tau^(-1/2)) and O(tau^(-3/2)); the chain rule verifies both conditions (SV). Thus this determines one admissible fixed strongly log-concave source after extension.

Take valley parameters tau_n=exp(3pi/2+2pi n). At the corresponding x, L(x)=exp(-sqrt(tau_n)). A preceding peak lies at tau_n'=exp(pi/2+2pi n)=e^(-pi)tau_n, where L=exp(e^(-pi/2)sqrt(tau_n)). Choosing the nearest dyadic x-scales changes either value only by a multiplicative factor tending to one, because the tau-grid spacing is fixed and the logarithmic derivative tends to zero. Therefore, at valley cutoffs K_n,

    A_3(K_n)/L(t_(K_n))
      >= exp[(1+e^(-pi/2)+o(1))sqrt(tau_n)] -> infinity.  (10.2)

The three-atom lower construction can use a preceding favorable layer while taking a much thinner central strip. Theorem A detects this. A proposed law that replaced the top-N source envelope by N L(t_K) would fail on this one fixed source by an unbounded factor. It is likewise unsafe, for arbitrary (SV) factors, to replace the implicit distance inversion by h=w^(2/3).

## 11. Relation to other boundary powers and limits of the result

Entry 008 already proves the full unrestricted power-law classification for f_beta~x^beta, including subcritical and supercritical exponents. Its subcritical rare-cell lower bound uses only two atoms, and its supercritical interior lower bound uses three. Thus, aside from the critical line's slowly-varying corrections, simply imposing an atom budget N>=3 does not create a further power-law phase: the old unrestricted upper and bounded-atom lower already match. Those inherited observations are not counted as a new theorem here.

Theorem A resolves the critical family's arbitrary (SV) source-scale / cardinality interaction. It does not resolve:

- prescribed positive mass vectors or a lower atom-weight bound;
- a sharp general binary law for nonmonotone or vanishing L;
- a converse characterization for arbitrary, non-product sources;
- an independent proof of the imported potential estimate (P).

The law optimizes over genuine target measures, with the selected-scale realizations and their full moment and label accounting above. It does not claim that every step-energy profile is transport-realizable.

## 12. Predecessors and primary literature

Repository predecessors inspected locally:

- research_math/critical_atom_budget_20261008/PROOF.md: L=1, jointly uniform N,w law and original finite-level weak-L^s upper pairing.
- research_math/round6_regular_variation/CRITICAL_SLOW_VARIATION.md: unrestricted arbitrary-(SV) modulus through H(h)=1+integral_h^a L(x)dx/x.
- research_math/transport_synthesis_public_release_20261007/corrected_baseline/synthesis.tex: general rearrangement upper envelope, explicitly without a new sharpness claim.
- Entry 008 v1: full power phase diagram and the original global mass-matched multi-strip construction.

Public primary sources checked on 8 October 2026:

1. Mohit Bansil and Jun Kitagawa, Quantitative stability in the geometry of semi-discrete optimal transport, arXiv:2002.02022v2 (2021): https://arxiv.org/html/2002.02022 . It fixes a finite support and studies Laguerre-cell and potential stability, including a target-weight perturbation estimate. Its explicit N dependence and small-weight effects are relevant comparison points. The present class lets locations and masses vary without a common support or a minimum weight.
2. Alex Delalande and Quentin Merigot, Quantitative stability of optimal transport maps under variations of the target measure, arXiv:2103.05934: https://arxiv.org/html/2103.05934 . This is background for quantitative map stability and is already part of the predecessor manuscripts' context.
3. The repository's source phase paper: https://github.com/mxym/math/blob/c2281bc871c9bf60994985d6665ae45f4711d080/preprints/008-density-overlap-phase/v1/main.tex .
4. Imported potential theorem: https://github.com/mxym/math/blob/5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3/preprints/001-strongly-log-concave-brenier/v3/manuscript.tex .

The finite-step rearrangement and local regular-variation tools are elementary standard analysis; no historical novelty is claimed for them individually. The selected-scale sharp transport envelope is a candidate repository-level new result. This focused screening does not establish historical priority or a publication-tier claim.
