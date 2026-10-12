# Two-ended spectral hierarchies: an exact limiting APPT test

Research working proof, 10 October 2026. No manuscript or Release is prepared. This is an analytic result, not a Lean certificate or external mathematical review. The compactness argument is explicit below; exact finite checks support it but do not prove a limiting all-unitary statement by enumeration.

## 1. The new model and graph theorem

Fix FINITE integers p,q>=0. Fix rank exponents

    0<alpha_1<...<alpha_p<1/2,    alpha_{i+1}>2 alpha_i,
    0<delta_q<...<delta_1<1/2,    delta_{j+1}<delta_j/2.

Empty lists are allowed. Let M tend to infinity. The low ranks l_i satisfy l_i/M^alpha_i ->1; the high ranks r_j satisfy r_j/M^(2-delta_j) ->1. Let nonnegative coefficients obey

    l_i a_i^2 -> f_i,    r_j c_j^2 -> e_j,    M d_M -> u>=0.

For arbitrary simple graphs L_i,H_j on M vertices with at most l_i,r_j edges, put

    B_M = sum_i a_i A(L_i) + sum_j c_j A(H_j) + d_M A(K_M).

Define suffix and prefix energies

    F_{>i}=sum_{h>i} f_h,    E_{<j}=sum_{h<j} e_h,    E=sum_j e_j,
    low_i=(sqrt(2f_i)+sqrt(2f_i+4F_{>i}))/2,
    high_j=(sqrt(2e_j)+sqrt(2e_j+4E_{<j}))/2,
    broad=(u+sqrt(u^2+4E))/2,
    Lambda(f,e,u)=max({0,broad} union {low_i} union {high_j}).

**Theorem G.** The exact graph limit is

    lim_M max_{L_i,H_j} lambda_max(B_M)=Lambda(f,e,u).          (G1)

The same value is obtained if all low graphs, followed by all high graphs, must form ONE nested flag with exactly the specified ranks. The complete graph is the final background. The exponents, number of levels, and limiting energies are fixed before M grows. No arbitrary growing-level sequence is certified by (G1).

The low-rank constraints run in the reverse order to the previously studied high-rank constraints. The broad background also couples to the high hierarchy; it is not an independent extra energy budget.

## 2. A common amplitude-measure reduction for every rank exponent

Take any sequence of graph choices and nonnegative unit maximizing vectors x. Write p_v=x_v^2 and s_v=-log_M p_v>=0 when p_v>0. For a level with edge budget t~M^beta, coefficient c with tc^2->e, products x_v x_w smaller than M^(-beta/2-eta) contribute O(M^-eta) after multiplying by c. Products larger than M^(-beta/2+eta) occur on at most M^(beta-2eta)/2 unordered pairs, because sum_{v<w}p_vp_w<=1/2. Cauchy--Schwarz bounds their weighted sum by O(M^-eta) too. Thus only

    |s_v+s_w-beta|<=2eta                                     (G2)

can contribute at leading order.

The total p-mass on s_v>1+eta is at most M^-eta; incident edges give a vanishing contribution by Cauchy--Schwarz and c sqrt(t)=O(1). Clamp the remaining exponents to [0,1]. This changes a surviving sum by at most 2eta. The probability measures

    mu_M=sum_{p_v>0} p_v delta_{min(s_v,1)}

have a weakly convergent subsequence on [0,1], with limit mu. Product measures converge weakly. The upper bound on closed strips in (G2), then continuity from above as eta decreases to zero, yields for the same mu at every level

    limsup (1/2)x^T[sum graph levels]x
       <=sum_levels sqrt(e_beta Q_beta),
    Q_beta=(1/2)(mu x mu){s+t=beta}.                          (G3)

The subsequence and measure are common to all levels, which are finite in number. No separate maximizer is substituted for each label.

The complete-graph contribution also has a precise bound. Coordinates with s_v<=1-eta number at most M^(1-eta); their contribution to M^(-1/2)sum_v x_v is at most M^(-eta/2). Cauchy--Schwarz bounds the other coordinates by the square root of their p-mass. The closed-set limit and eta down to zero give

    limsup (sum_v x_v)^2/M <= mu({1}).

Therefore the background contributes at most u mu({1}) to the limiting full Rayleigh quotient.

## 3. Separated components and their one-loop bounds

Only atoms of mu contribute to a line s+t=beta. Write p_s=mu({s}). Its half-product mass is

    Q_beta=sum_{s<t, s+t=beta} p_s p_t + p_(beta/2)^2/2.

As in the earlier hierarchy proof, distribute nonnegative weights over the edges and loop of each label, with squared sum at most that label's energy. The scalar sum sqrt(e_beta Q_beta) then equals the corresponding edge quadratic expression: off-diagonal weights w_st and diagonal loop entry sqrt(2) w_loop. The Rayleigh vector has entries sqrt(p_s); its squared norm is at most one.

Low-label edges have both endpoints in [0,alpha_p], while high-label edges have both endpoints in [1-delta_1,1]. These intervals are disjoint. Other atom locations have no weighted edges. This is why the two hierarchies do not add their operator norms.

For low labels, the off-diagonal graph is a forest. In a hypothetical finite cycle choose its largest label. Its two neighboring labels are smaller and each is less than half of it; their incident nonnegative endpoints cannot sum to the largest label. A component with a loop at alpha_i/2 has no other loop, and every off-diagonal label in it is alpha_h with h>i. Indeed a simple path leaving the loop has strictly increasing labels: after an edge of label alpha_h its next endpoint is strictly between alpha_h/2 and alpha_h, so a smaller label is impossible and a repeated one returns along the same edge. Such a path cannot meet another half-label. Consequently this component has loop at most sqrt(2f_i) and squared off-diagonal budget at most F_{>i}. Bipartition and the Hilbert--Schmidt bound give top norm at most low_i.

Reflect high coordinates by t=1-s. Their labels become delta_j, so the earlier high-hierarchy forest proof applies: a component with loop delta_j/2 has off-diagonal budget E_{<j} and top norm at most high_j.

The complete-graph background adds one further loop of size u at s=1, that is t=0 in the reflected high component. This component cannot contain any half-label loop: the path argument just given, starting from such a loop, cannot terminate at zero. It has off-diagonal squared budget at most E. Its top norm is bounded by the larger eigenvalue of [[u,sqrt(E)],[sqrt(E),0]], namely broad.

Loop-free components have norm at most the square root of their edge-square budget and are already covered: low_1>=sqrt(sum_i f_i) and broad>=sqrt(E). For countably many atoms these conclusions follow by finite truncation, since squared edge weights are summable. Taking the largest component norm proves the upper bound in (G1), uniformly over the original graphs.

## 4. Matching lower graphs with one nested flag

It remains to realize every branch with exactly the prescribed ranks, using one flag rather than incompatible subspaces.

For low_i, take a central clique of size Q~sqrt(2l_i), with binom(Q,2)+l_{i-1}<=l_i, where l_0=0. Fill the preceding flag to l_{i-1} arbitrarily and add the clique at level i. For each h>i add the complete bipartite graph from the central group to a new peripheral group of size floor((l_h-l_{h-1})/Q). Fill unused edge slots arbitrarily, always preserving nesting. The clique exponent is alpha_i/2; peripheral exponents are alpha_h-alpha_i/2. All are positive and below one, so the displayed groups fit in o(M) vertices. The constant-on-groups quotient has central loop sqrt(2f_i) and off-diagonal entries sqrt(f_h), h>i. Its top eigenvalue is low_i. All ignored terms, including background and other graph levels, are nonnegative on the chosen Rayleigh vector. Extend the flag through the high ranks arbitrarily.

For high_j use the analogous high-hierarchy construction from OPTIMAL_HIERARCHY.md: a central clique of size ~sqrt(2r_j), with binom(Q,2)+r_{j-1}<=r_j, and peripheral groups for h<j of sizes floor((r_h-r_{h-1})/Q). Here r_0 is the largest low rank, or zero. It is negligible relative to r_1. Build those bipartite pieces in rank order, include the clique at level j, and fill every level to its exact rank. Exponents are 1-delta_j/2 for the clique and 1-delta_h+delta_j/2 for the peripheral groups, all strictly between zero and one. The quotient attains high_j. Earlier low edges are simply retained; they do not harm the lower bound.

For broad, choose a central group of size Q=M-o(M) and high-level peripheral groups of sizes floor((r_j-r_{j-1})/Q). A non-circular choice is Q=M-ceil(M^(1-delta_q/2)) when q>0: all peripheral groups together are O(M^(1-delta_q)) and fit in the reserved vertices for large M. Build each high graph by adding its own complete bipartite piece and filling to its exact edge count; keep the low flag inside throughout. The background has quotient entry d_M(Q-1)->u on the central group. The own-level bipartite entries tend to sqrt(e_j). Its other contributions are nonnegative. The resulting star quotient has eigenvalue broad. For q=0 use the all-ones vector to attain u.

Ranks are o(M^2), so filling to exact ranks is always possible eventually. Only a lower Rayleigh bound is needed; no claim is made that the finite graph optimizer has this form. These constructions and the uniform upper bound prove (G1), including nestedness.

## 5. Exact limiting feasibility for quantum spectra

Let 2<=m<=n, m->infinity. On C^m tensor C^n take nested coordinate projections

    L_1<=...<=L_p<=H_1<=...<=H_q<=P,

of low/high ranks as above (M=m), and k=rank(P)=ceil((m-1)n/2). For all sufficiently large m the last high rank is less than R=binom(m,2), and R<=k<=mn-binom(m+1,2). Empty hierarchies cause no difficulty. Set

    X_m=sum_i a_i L_i+sum_j c_j H_j+d_m P,
    B_m=I+X_m, rho_m=B_m/Tr B_m.                              (G4)

For an arbitrary unit Schmidt witness, the negative expectation of each positive projection is at most the sum of the appropriate number of largest products x_vx_w. The broad projection is bounded by the sum of ALL such products. Thus Lambda(f,e,u)<2, together with (G1), proves that B_m has positive semidefinite partial transpose after EVERY global unitary for every sufficiently large m. The threshold is independent of n>=m.

Conversely, use the nested graphs of Section 4 as nested spans of antisymmetric Schmidt-witness vectors. Extend the final span to P by taking all R negative vectors and k-R zero eigenvectors of the witness. The rank interval above provides enough zero slots. All flags of the same ranks are unitarily equivalent. Their partial-transpose expectation is exactly one minus half of the graph Rayleigh quotient in (G1). If Lambda>2, APPT therefore fails eventually. This necessity does not use nonnested graphs.

It follows that the closure of possible limiting nonnegative energy/background data is precisely

    sum_{h>i} f_h + 2sqrt(2f_i) <=4     for each low i,
    sum_{h<j} e_h + 2sqrt(2e_j) <=4     for each high j,
    E+2u<=4,    u>=0.                                        (G5)

For sufficiency on the boundary first multiply ALL coefficients by a common fixed factor 1-epsilon. The graph norm is then strictly below two. Let m grow before removing epsilon, or use a justified diagonal sequence. Merely having a limiting norm equal to two does not certify a given finite-dimensional state.

## 6. Purity and the complete finite-depth optimization

Suppose n/m->gamma in [1,infinity). Coefficient sums tend to zero. With T=Tr X_m and S=Tr X_m^2,

    D^2[Tr(rho_m^2)-1/D]=(S-T^2/D)/(1+T/D)^2,
    D=mn.

Between different subquadratic ranks the cross term is O(sqrt(r_small/r_large))->0. Between those ranks and the broad projection it is O(sqrt(r)/m)->0. Since k/D->1/2, direct expansion gives

    D^2[Tr(rho_m^2)-1/D] -> sum_i f_i+sum_j e_j+gamma*u^2/4.    (G6)

Define d_0=4 and d_j=d_{j-1}-d_{j-1}^2/8. For p low levels the maximum total low energy is 4-d_p, with the optimal allocation in REVERSE rank order: f_i=d_(p-i)^2/8. The proof is the same increasing-map recursion as in OPTIMAL_HIERARCHY.md, now applied from the largest low rank backwards. For q high levels the maximum total high energy is 4-d_q, with e_j=d_(j-1)^2/8.

For a prescribed u, (G5) makes the maximum high energy min(4-d_q,4-2u). Every smaller total is feasible by scaling an optimal high energy vector; its graph norms decrease by the square root of that scaling. Thus the complete fixed-depth optimum is

    K_{p,q}(gamma)=4-d_p+max{gamma,4-d_q+gamma*d_q^2/16}.        (G7)

For q=0 this reads 4-d_p+gamma. To verify (G7) for q>0, optimize min(4-d_q,4-2u)+gamma*u^2/4 on 0<=u<=2. On [0,d_q/2] it increases, and on [d_q/2,2] it is convex. Hence its maximizers are u=d_q/2 and u=2. The branch transition is

    gamma_q=16/(4+d_q),                                      (G8)

below which u=d_q/2 and all high energy constraints are saturated, and above which u=2 and all high energies vanish. At equality both choices maximize and no intervening u does. These statements concern limiting spectra in this stated hierarchy model, not all finite-dimensional APPT maximizers.

If the broad coefficient is fixed to zero, the sharp value is 8-d_p-d_q. With p+q=N levels this is maximized by splitting the depths as evenly as possible, since d_j-d_(j+1)=d_j^2/8 strictly decreases. Its deficit is asymptotic to 32/N. Allowing the broad coefficient does not change that 32/N asymptotic in the balanced case gamma=1; the exact finite objective is (G7). This contrasts with the 8/N deficit when an order-one isolated spike is permitted.

All these sharp values refer to the closure of attainable limiting data. Fixed positive margins and integer-root ranks give actual rational, full-rank APPT states at every sufficiently large dimension. No effective threshold, arbitrary growing-depth theorem, global finite-spectrum classification, or absolute-separability conclusion is asserted.
