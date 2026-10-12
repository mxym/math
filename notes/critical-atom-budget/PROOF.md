# Critical Brenier stability with a finite target-atom budget

Research continuation, 8 October 2026. Status: complete candidate written argument for independent review; not published or independently audited. No priority or journal-tier claim is made.

## 1. Exact statement and dependencies

Fix an integer d >= 2 and a real p > 2. Put

    s = p/(p-2),    beta = s-1 = 2/(p-2),    alpha = 1/(3s).

The source is the following single fixed probability, exactly the critical member of entry 008:

    rho(dx) = r(x) dx,
    r(x) = f_beta(x_1) product_{j=2}^d g(x_j),
    f_beta(t) = c_beta t^beta exp(-t^2/2) 1_{t>0},
    g(z) = c_g exp(-1/(1-z^2)) 1_{|z|<1}.

The positive constants c_beta and c_g are the reciprocals of the indicated integrals, so each factor and rho have total mass one. The density is extended by zero off D=(0,infinity) x (-1,1)^(d-1). It has finite moments of every positive order. It is absolutely continuous and 1-strongly log-concave on its extended convex support, as verified in entry 008.

For every target probability mu with finite second moment, T_mu is the rho-a.e. unique quadratic-cost Brenier map. Define

    C_{p,N} = {mu: mu is a probability, |supp(mu)| <= N,
                     integral |y|^p dmu(y) <= 1},

    Omega_N(w) = sup { ||T_mu-T_nu||_{L^2(rho)}:
                      mu,nu in C_{p,N}, W_2(mu,nu) <= w }.

Here N is a positive integer. Support counts distinct positive-mass atoms; repeated locations are merged and zero-weight labels are discarded. There is no minimum atom weight, no bound on individual atom locations, and no fixed common target support.

### Theorem A: uniform two-parameter critical law

There are constants c,C>0 and w_0 in (0,1), depending only on p,d and the displayed normalized source, such that simultaneously for EVERY integer N>=2 and EVERY 0<w<=w_0,

    c w^(1/3) min{N, log(e/w)}^alpha
       <= Omega_N(w)
       <= C w^(1/3) min{N, log(e/w)}^alpha.                 (A)

The same c,C,w_0 work for all N. In particular, for each fixed N>=2 a pure one-third estimate holds; its best small-distance constant has order N^alpha, with comparison constants independent of N. For N=1,

    Omega_1(w)=min{w,2}  for every w>=0.                    (B)

The theorem does not assert numerical optimality of c or C. Its source depends on p through beta, but for each p it is fixed once and for all. It gives neither a classification of all sources nor a result for arbitrary slowly varying critical factors.

### Explicit imported analytic premise

The upper bound uses the following potential estimate, labeled (P): centered Brenier potentials U_mu can be chosen so that

    ||U_mu-U_nu||_{L^2(rho)} <= K_rho W_2(mu,nu)             (P)

for all P_2 targets, and their proper convex representatives are finite on D. Entry 001 v3, Theorem 1.1, supplies K_rho=sqrt(2) for the displayed 1-strongly log-concave source. This is an imported written theorem, not independently reproved here. Only finitely supported targets are needed for (A); their convex potentials have finite slopes and the domain/integrability conventions of the finite-difference argument below are automatic.

The lower bounds do not use (P). They refine, with an explicit atom budget, the two-atom and globally mass-matched multi-strip constructions already proved in entry 008. Those constructions are inherited, not claimed as a new mechanism. Sections 5-7 reproduce all the estimates needed to track N and w independently.

Public baseline inspected on 8 October 2026: mxym/math main commit c2281bc871c9bf60994985d6665ae45f4711d080; entry-008 source blob 3b2882cef1a65e890549332c5c9014af9dc5f245. Useful sources:

- https://github.com/mxym/math/blob/c2281bc871c9bf60994985d6665ae45f4711d080/preprints/008-density-overlap-phase/v1/main.tex
- https://github.com/mxym/math/blob/5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3/preprints/001-strongly-log-concave-brenier/v3/manuscript.tex
- https://github.com/mxym/math/blob/c2281bc871c9bf60994985d6665ae45f4711d080/notes/transport-source-tail-synthesis/synthesis.tex

## 2. An elementary weak-overlap pairing lemma

For a nonnegative random variable a on a probability space, define

    ||a||_{s,infinity} = sup_{t>0} t P(a>t)^(1/s).

Suppose this is at most H, with s>1, and set s'=s/(s-1)=p/2. If E is measurable of probability m, layer cake gives

    integral_E a <= integral_0^infinity min{m,(H/t)^s} dt
                 = s' H m^(1/s').                         (2.1)

The zero-mass and H=0 cases are immediate. If b is nonnegative and takes at most N distinct values b_i on disjoint level sets of masses m_i, then

    E[ab] <= s' H sum_i b_i m_i^(1/s')
           <= s' H N^(1/s) (E b^(s'))^(1/s').              (2.2)

The last step is Holder's inequality for the finite sequence b_i m_i^(1/s') and the sequence of ones. There is no lower bound on the nonzero m_i. Zero-valued levels may be omitted, and repeated b_i may be merged.

For a target mu=sum_i m_i delta_{y_i}, (2.1) also gives the more informative bound

    integral a |T_mu|^2 drho
       <= s' H sum_i m_i^(2/p)|y_i|^2.                    (2.3)

The sum on the right is bounded by N^(1/s) (integral |y|^p dmu)^(2/p). Thus the cardinality loss need not be paid when the moment contributions are very unbalanced. This is a finite-level Lorentz pairing argument; the general inequality itself is not proposed as a literature novelty.

## 3. Linear weak-L^s overlap at the critical source

For h>0 and each coordinate j, put, on {r>0},

    d_{j,+h}(x)=(1-r(x+h e_j)/r(x))_+,
    d_{j,-h}(x)=(1-r(x-h e_j)/r(x))_+,
    W_{j,h}=6|d_{j,+h}-d_{j,-h}|+2d_{j,+h},
    F_h=max_j W_{j,h}.

Give all these functions value zero where r=0. Always 0<=F_h<=8.

### Lemma 3.1

For a constant B depending only on p,d and the fixed source,

    rho(F_h>t) <= min{1,(B h/t)^s}

for all t>0 and 0<h<=1/4. Equivalently ||F_h||_{s,infinity}<=B h.

Proof. Product structure makes each relative loss a one-dimensional loss for its own factor. For the first factor and x>2h,

    |log f_beta(x +/- h)-log f_beta(x)|
       <= C_beta h (x+1+x^(-1)).

This follows by integrating beta/x-x along the segment; x-h>=x/2. Since (1-exp(-u))_+<=min{1,u_+}, either loss is at most the minimum of one and that bound. For 0<x<=2h the same conclusion holds after increasing C_beta, since h/x>=1/2. Thus, everywhere on the support,

    d_{1,+/-h} <= min{1,C_beta h (X+1+1/X)}.               (3.1)

Under f_beta, P(X<a)<=C a^(beta+1)=C a^s for every a>0 (for a>=1 increase C), while E X^s<infinity. Consequently X+1+1/X has bounded weak-L^s norm: apply the union bound to its three summands, use the displayed distribution estimate for 1/X, and Markov for X. This proves the required tail estimate for coordinate one.

For a transverse coordinate let a=1-|z|. If a>2h, integrate the logarithmic derivative of g along the segment, obtaining an upper bound C h/a^2. If a<=2h and h<=1/4, then h/a^2>=1/(4h)>=1, so the trivial bound one gives the same result. Therefore

    d_{j,+/-h} <= min{1,C h (1-|Z_j|)^(-2)}.              (3.2)

The variable (1-|Z_j|)^(-2) has a finite s-th moment under g, because the exponential boundary decay dominates every polynomial. Markov gives its weak-L^s bound. Finally W_{j,h}<=14 max{d_{j,+h},d_{j,-h}}, and a finite union bound over coordinates and signs proves the lemma. This proof retains all zero-extension boundary losses. QED.

Since F_h<=8, the same estimate also proves

    ||F_h||_s <= C h (1+log(1/h))^(1/s)                  (3.3)

for sufficiently small h, by integrating
s integral_0^8 t^(s-1) rho(F_h>t) dt and splitting at B h. The weak bound has no logarithm; the strong bound does.

## 4. Upper bound: finite target cardinality removes the logarithm

For finite convex potentials u,v on D with L^2 gradients, set

    delta=inf_a ||u-v-a||_{L^2(rho)},
    X=||grad u-grad v||_{L^2(rho)}.

The exact minimum-weight estimate of 001 v5 can also be proved directly here:

    X^2 <= 12d delta^2/h^2
           + integral F_h (|grad u|^2+|grad v|^2) drho.   (4.1)

For completeness, fix a coordinate and m_h=min{r(x),r(x+h e_j)}. Convexity gives z(x)<=D_h u(x)<=z(x+h e_j) for z=partial_j u wherever m_h>0. The signed-square inequality (b-a)^2<=2(b|b|-a|a|) for a<=b, followed by a change of variables, gives

    integral |D_h u-z|^2 m_h dx
      <= 2 integral |z|^2 |m_h(x-h e_j)-m_h(x)| dx
      = 2 integral |z|^2 r |d_{j,+h}-d_{j,-h}| dx.

Every integrand is integrable since the shifted minimum weights are bounded by r. For f=u-v-a,
integral |D_h f|^2 m_h<=4h^(-2) integral |f|^2 r.
Apply the three-term square inequality to z_u-z_v, and use
|z_u-z_v|^2<=2(|z_u|^2+|z_v|^2) on the missing weight r-m_h=r d_{j,+h}. These are exactly the coefficients six and two defining W. Sum over j and infimize over a to obtain (4.1). Segments with m_h>0 stay in D, so no value of the convex potential off D is needed.

Apply (P) and let u,v be transport potentials for mu,nu in C_{p,N}. By (2.2) and Lemma 3.1, each of the two weighted energies in (4.1) is at most s' B h N^(1/s). Thus, with A=12d K_rho^2,

    ||T_mu-T_nu||_2^2 <= A w^2/h^2 + 2s' B h N^(1/s).   (4.2)

Choose h=w^(2/3) N^(-1/(3s)). For all sufficiently small w, independently of N>=1, this h is in (0,1/4]. Both terms yield

    Omega_N(w) <= C w^(1/3) N^(1/(3s)).                  (4.3)

Alternatively Holder's inequality, the target p-moment bound, and (3.3) give (4.1) with its last term at most C h(1+log(1/h))^(1/s). Set

    L=log(e/w),   h=w^(2/3)L^(-1/(3s)).

For 0<w<=w_0 sufficiently small, log(1/h)<=C_s L and h<=1/4. Substitution gives

    Omega_N(w) <= C w^(1/3) L^(1/(3s)),                  (4.4)

uniformly over N, or indeed without a cardinality restriction. The minimum of (4.3) and (4.4) is the upper half of (A).

This argument more generally proves a pure one-third upper estimate for finite-atom targets at any source satisfying (P) and a linear weak-L^s bound for F_h. A strong Sobolev density-root assumption is unnecessary for that restricted target class. It does not establish the converse at arbitrary sources.

## 5. The inherited K-strip construction, with atom count tracked

The following detailed argument is a parameter-explicit reuse of entry 008, Section 7. It is included so the N quantifier is not hidden inside a growing-scale limit.

Let X,Z be independent with laws f_beta,g, and let F(t)=P(X<t), set to zero for t<=0. Fix k=1/4. For K>=1 put

    t_n=2^(-n),   R_n=t_n^(-beta/2),   1<=n<=K.

There is an epsilon_0>0 depending only on p and the source such that the construction below works for every integer K>=1 and every 0<h<=epsilon_0 2^(-K). Choose epsilon_0<=1/12 initially; decrease it below where indicated. The windows [t_n-3h,t_n+3h] are positive and disjoint.

### 5.1 Two exact cumulative matches at every strip

Put H_h(y)=E F(y+khZ), and define

    ell_n=H_h^(-1)(F(t_n-h)),
    r_n=H_h^(-1)(F(t_n+h)).

The inverses are well-defined at these levels: on the positive interval at issue H_h is continuous and strictly increasing. From
F(y-kh)<=H_h(y)<=F(y+kh) one gets

    |ell_n-(t_n-h)|<=kh,  |r_n-(t_n+h)|<=kh.              (5.1)

Symmetry of Z gives E Z=0. Taylor expansion of F, followed by the mean value theorem for H_h, improves this uniformly to

    ell_n=t_n-h+O(h^2/t_n),
    r_n=t_n+h+O(h^2/t_n).                                (5.2)

Indeed on |y-t_n|<=3h, f_beta(y) is comparable to f_beta(t_n),
|f_beta'(y)|<=C f_beta(t_n)/t_n, and H_h'(y)>=c f_beta(t_n). Taylor's remainder has size at most C h^2 f_beta(t_n)/t_n. These constants do not depend on K,n,h.

Write d_n=(ell_n+r_n)/2, gamma_n=(r_n-ell_n)/(2h), and set

    A_n={t_n-h<X<t_n+h},
    C_n={ell_n-khZ<X<r_n+khZ}.

The half-width h(gamma_n+kZ) is between h/2 and 3h/2. Both endpoint equations hold exactly:

    E F(ell_n-khZ)=F(t_n-h),
    E F(r_n+khZ)=F(t_n+h).                               (5.3)

The first uses symmetry of Z. Consequently the two central masses agree, as do the cumulative masses on each side; the latter fact is essential for preserving EVERY outer-cell label later.

Let m_n=rho(A_n)=rho(C_n) and D_n=rho(A_n symmetric_difference C_n). Density comparability and (5.2) show, uniformly,

    c f_beta(t_n)h <= m_n,D_n <= C f_beta(t_n)h.           (5.4)

In more detail, the two central intervals overlap. Ignoring endpoint errors their symmetric-difference length is 2kh|Z|. Equation (5.2) changes that length by O(h^2/t_n); variation of f_beta across the window has the same error order. Thus

    D_n=2kh f_beta(t_n)E|Z|+O(f_beta(t_n)h^2/t_n).

Since E|Z|>0, one fixed decrease of epsilon_0 makes the error at most half the leading term for all n,K,h.

### 5.2 Global convex realization and exactly 2K+1 atoms

Define convex broken lines

    Phi(x)=sum_{n=1}^K 2R_n(t_n-x)_+,
    Phi_tilde(x)=sum_{n=1}^K 2R_n(d_n-x)_+.

They have the same ordered slopes, with each jump equal to 2R_n. Let q_n be the average of the two slopes at the n-th cusp. The supporting lines there are

    L_n(x)=Phi(t_n)+q_n(x-t_n),
    L_tilde_n(x)=Phi_tilde(d_n)+q_n(x-d_n).

Between the neighboring cusps Phi-L_n=R_n|x-t_n|, and globally the left side is at least the right side; similarly for Phi_tilde. Define global finite convex maxima

    U_h(x)=max{Phi(x_1), L_n(x_1)+R_n h : 1<=n<=K},
    V_h(x)=max{Phi_tilde(x_1),
                  L_tilde_n(x_1)+R_n h gamma_n+R_n h k x_2 : 1<=n<=K}.

On the source, a central plane dominates exactly on A_n or C_n respectively. The global supporting-line lower bound excludes its activity outside its own window; window separation rules out competition between distinct central planes. These are actual convex potentials, not patched local gradients.

There are K+1 outer gradient labels and K central labels. All have positive source mass. Central labels are strictly between neighboring horizontal outer slopes for U_h, while for V_h they have positive vertical component R_n h k. Hence each induced target has exactly 2K+1 distinct positive-mass atoms. Counting at most 2K+1 would already suffice.

The outer labels are identical for U_h and V_h. The central labels are q_n e_1 and q_n e_1+R_n h k e_2. Equation (5.3) preserves each neighboring outer mass, because an intermediate outer mass is the difference of the relevant two cumulative endpoints; the extreme masses are also preserved. Thus EVERY corresponding atom label has the same mass in the two targets.

On a central mismatch the horizontal slope discrepancy is exactly R_n. The intervals overlap, so no point jumps directly between the two outer labels across a central interval. The vertical difference has size R_n h k on C_n and vanishes elsewhere. Therefore

    ||grad U_h-grad V_h||_2^2
       = sum_n R_n^2 D_n + k^2 h^2 sum_n R_n^2 m_n.       (5.5)

The same-label coupling of the target laws gives

    W_2((grad U_h)#rho,(grad V_h)#rho)^2
       <= k^2 h^2 sum_n R_n^2 m_n.                       (5.6)

Optimality of this target coupling is not required. The source maps themselves are optimal since they are gradients of global convex functions; for each finite K their bounded slopes make the supporting-plane optimality argument integrable.

### 5.3 Uniform p-moment normalization

Geometric summation of the jumps R_n (beta>0) shows that both gradient magnitudes are at most

    C min{x_1^(-beta/2), t_K^(-beta/2)}

on 0<x_1<1, and vanish on x_1>=1. Cusp shifts of at most kh and central vertical slopes of at most R_n h k change only the uniform C, because each active central point has x_1 comparable to t_n. Since

    beta p/2=beta+1=s,

integration of the p-th power gives a bounded contribution on (0,t_K) and a contribution at most C integral_{t_K}^1 dx_1/x_1=C K log 2 on (t_K,1). Consequently, for some C_0 independent of K,h,

    integral (|grad U_h|^p+|grad V_h|^p) drho <= C_0(K+1).

Scale both potentials by lambda_K=[C_0(K+1)]^(-1/p). The induced target probabilities mu_{K,h},nu_{K,h} each have p-th moment at most one and at most 2K+1 atoms. Moreover R_n^2 f_beta(t_n)=c_beta exp(-t_n^2/2) is uniformly bounded above and below. Equations (5.4)-(5.6) therefore imply

    ||T_mu_{K,h}-T_nu_{K,h}||_2 >= c_1 K^(1/(2s)) h^(1/2),
    W_2(mu_{K,h},nu_{K,h}) <= C_1 K^(1/(2s)) h^(3/2),    (5.7)

for every K>=1 and 0<h<=epsilon_0 2^(-K), with c_1,C_1,epsilon_0 independent of BOTH variables. Increase C_1 if necessary so C_1>=1.

## 6. Uniform lower bound for N>=3, and the order of limits

Choose w_0 small enough that (1/4)log_2(1/w)>=2 for 0<w<=w_0. For N>=3 set

    K=min{floor((N-1)/2), floor((1/4)log_2(1/w))},
    h=[w/(C_1 K^(1/(2s)))]^(2/3).                       (6.1)

Then K>=1, 2K+1<=N, and

    K >= c_2 min{N,log(e/w)}                             (6.2)

for a numerical c_2>0, uniformly in N,w in this range. For example floor((N-1)/2)>=N/4 for N>=3; the logarithmic floor is at least half its unfloored value, which is comparable to log(e/w) on this range.

Crucially, K <= (1/4)log_2(1/w), so

    h 2^K <= C_1^(-2/3) w^(2/3-1/4) K^(-1/(3s))
           <= C_1^(-2/3) w^(5/12).

A SINGLE further decrease of w_0 makes this at most epsilon_0, independently of N. Thus (5.7) applies for all pairs (N,w) under consideration. It gives W_2<=w and

    Omega_N(w) >= c_1 C_1^(-1/3) w^(1/3) K^(1/(3s))
                >= c w^(1/3) min{N,log(e/w)}^alpha.

For a fixed N, K eventually equals floor((N-1)/2) as w decreases. It then stays fixed; only h decreases. Thus the proof genuinely establishes the fixed-N lower constant, rather than taking N to infinity along with w. In the joint regime N grows sufficiently fast, the other cutoff gives the original critical logarithm.

## 7. The exceptional small budgets N=2 and N=1

### N=2: a separate rare-cell construction

The K-strip argument cannot be used at N=2. Instead fix k=1/4 and let a>0 be small. Write m_a=F(a). Choose c_a in (1-k,1+k) so that

    E F(a(c_a+kZ))=F(a).

Existence and uniqueness follow from continuity, strict monotonicity and bracketing by c=1-k and c=1+k. Since F(t)~c t^s at zero, uniformly over the compact positive range of c+kZ, one has c_a->c_0, where

    E(c_0+kZ)^s=1.

Let A_a={X<a} and C_a={X<a(c_a+kZ)}. These have the same mass m_a, and

    rho(A_a symmetric_difference C_a)/m_a
       -> E |(c_0+kZ)^s-1| > 0.                          (7.1)

Strict positivity follows from nondegeneracy of Z. Put R_a=m_a^(-1/p), b_a=ka, and

    v_a=(-e_1+b_a e_2)/sqrt(1+b_a^2),
    mu_a=(1-m_a)delta_0+m_a delta_{-R_a e_1},
    nu_a=(1-m_a)delta_0+m_a delta_{R_a v_a}.

Each target has exactly two atoms and p-th moment exactly one. Its source map is the gradient of, respectively,

    R_a(a-x_1)_+,
    R_a/sqrt(1+b_a^2) (a c_a-x_1+b_a x_2)_+.

The same-label coupling and (7.1) give

    W_2(mu_a,nu_a) <= C a m_a^(1/2-1/p) <= C' a^(3/2),
    ||T_mu_a-T_nu_a||_2 >= c m_a^(1/2-1/p) >= c' a^(1/2),

because m_a is comparable to a^s and 1/2-1/p=1/(2s). Taking a=(w/C')^(2/3), after decreasing w_0 once, proves Omega_2(w)>=c w^(1/3) for every 0<w<=w_0. Since min{2,log(e/w)}^alpha is bounded above and below by fixed positive constants on this range, this is the N=2 lower half of (A).

### N=1: exact isometry and attainability

The targets are delta_y,delta_z with |y|,|z|<=1. The maps are constant, so

    ||T_delta_y-T_delta_z||_2=|y-z|=W_2(delta_y,delta_z).

The largest distance subject to |y-z|<=w is min{w,2}, achieved by y=-t e_1/2, z=t e_1/2 with t=min{w,2}. Both norms are <=1, hence both p-th moments are <=1. This proves (B), including w=0. It uses rho being a probability; there is no dependence on its geometry.

## 8. Consequences, precise increment, and limitations

1. For the fixed critical source, a finite target-atom budget restores a pure one-third modulus. There are uniform c,C such that, for every N>=2,

       c N^alpha <= liminf_{w downarrow 0} Omega_N(w)/w^(1/3)
                 <= limsup_{w downarrow 0} Omega_N(w)/w^(1/3)
                 <= C N^alpha.

   The existence of a limit or an exact leading coefficient is not asserted.

2. The full-source global root r^(1/s) does not belong to W^{1,s}; near zero the derivative s-th power has a nonintegrable 1/x singularity. Thus that global root condition is not necessary for one-third stability on a FIXED finite-atom target class. This does not contradict the earlier root characterization of linear STRONG-L^s overlap or its sharp unrestricted-target theorem.

3. The new repository-level statement is the jointly uniform atom-budget/distance crossover (A), the weak-overlap finite-level upper bound, and the optimal growth of the fixed-N constant. The original critical logarithm, two-atom construction, global multi-strip geometry, cumulative mass matching, moment normalization and potential estimate retain their earlier attribution.

4. No lower atom-weight bound is used. Vanishing central weights as w->0 are allowed by C_{p,N}. A theorem requiring all weights bounded below would be a different question. Coincident and zero-weight target labels do not invalidate any upper estimate or create additional atoms.

5. The theorem concerns the displayed fixed source for each p, d>=2. It does not extend the source classification, the unrestricted pinned-distance programme, or the matrix results. Dimension one is different: the quadratic quantile representation is an isometry for every atomless source.

6. All claims are analytic written proofs. No new formalization, large computation, source mutation, external upload or publication was performed in this pass. The separate premise (P) retains its upstream verification status.

## 9. Focused literature screening

The finite-level pairing is standard weak/strong Holder (Lorentz) reasoning. Existing semi-discrete stability results are relevant and must not be ignored. Bansil--Kitagawa, *Quantitative stability in the geometry of semi-discrete optimal transport*, arXiv:2002.02022v2, fixes a common finite target support and proves, among other results, an L1-weight perturbation bound for symmetric differences of Laguerre cells (Theorem 1.3). The current theorem allows both atom positions and weights to vary without minimum weights and asks for a W2-to-L2-map modulus on an unbounded-location moment class. That source was checked directly at https://arxiv.org/html/2002.02022 .

Delalande--Merigot's broader transport-stability paper, https://arxiv.org/html/2103.05934 , is already acknowledged by the predecessor manuscripts and remains a relevant primary reference. The narrow searches and those sources did not certify historical originality of the precise atom-budget crossover. Full novelty comparison remains incomplete. The result is a rigorously specified candidate continuation, not a priority assertion.
