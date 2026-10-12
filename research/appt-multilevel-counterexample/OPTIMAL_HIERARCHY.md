# Optimal finite hierarchies and the exact multiscale graph test

Research working proof. No preprint, Release, Lean certification or external peer-review claim. The result sharpens the earlier sufficient forest estimate into an exact extremal graph limit and a complete leading-order optimization within a fixed, explicitly specified hierarchy model. It does not classify every possible APPT spectral shape.

## 1. Exact graph limit

Fix a FINITE J and lacunary deficits

    1>delta_1>...>delta_J>0, delta_{i+1}<delta_i/2,
    beta_i=2-delta_i in (1,2).

Let r_i=r_i(M) be integers with r_i/M^beta_i->1, and c_i>=0 with r_i c_i^2->e_i>=0. For simple graphs G_i on M vertices having at most r_i edges, put H_M=sum_i c_i A(G_i). Define

    E_j=sum_{i=1}^j e_i, E_0=0,
    phi_j=(sqrt(2e_j)+sqrt(2e_j+4E_{j-1}))/2,
    Phi(e)=max_{1<=j<=J} phi_j.

Then

    lim_{M->infinity} max_{G_1,...,G_J} lambda_max(H_M)=Phi(e).   (H1)

The same lower limit can be realized by NESTED graph flags with exactly r_i edges. This last point is needed for the quantum necessity argument and is proved below, rather than inferred from arbitrary nonnested graphs.

All J, deficits and limiting energies are fixed before M grows. Equation (H1) is not a statement for an arbitrary choice J=J(M).

## 2. Upper bound: each connected component has at most one loop

We recall the amplitude-measure reduction, deriving the sharper step explicitly. For a nonnegative unit maximizing vector x write p_v=x_v^2 and t_v=1+log_M p_v for p_v>0. At level i, products below M^(-beta_i/2-eta) contribute O(M^-eta) after multiplication by c_i. Products above M^(-beta_i/2+eta) occur in O(M^(beta_i-2eta)) pairs because sum_{v<w}p_v p_w<=1/2; Cauchy--Schwarz gives the same vanishing bound. Coordinates t_v<-eta have total mass O(M^-eta) and their incident-edge contribution also vanishes. Hence only t_v+t_w near delta_i matters.

After replacing negative t_v by zero, the probability measures mu_M=sum_v p_v delta_{max(t_v,0)} on [0,1] have a weakly convergent subsequence. The closed-strip upper bound for product measures, followed by decreasing the strip width to zero, gives for the same limit mu at all levels

    limsup (1/2)x^T H_M x <= sum_i sqrt(e_i Q_i),
    Q_i=(1/2)(mu x mu){t+s=delta_i}.                            (H2)

This uses finitely many levels, a common subsequence, Cauchy--Schwarz on each selected edge set, and continuity from above of a finite measure. No independently optimized measure is substituted for different levels.

Only atoms contribute to these exact-sum lines. On the atom locations, put an off-diagonal edge between distinct t,s when t+s=delta_i, and a loop at delta_i/2 if that point is an atom. The off-diagonal graph is a forest: in a proposed finite cycle take an edge of maximal label. Each neighboring label is smaller (two equal-sum edges at a vertex would have the same other endpoint), hence below half the maximal label. The two endpoints of the maximal edge would sum to less than its label, a contradiction.

There is a stronger fact. A component containing a loop of label j has NO OTHER loop, and all its off-diagonal edges have labels i<j. Start a simple path from delta_j/2. Its first off-diagonal edge must have label delta_i>delta_j, and the next vertex lies strictly between delta_i/2 and delta_i. A new incident edge cannot use a smaller label (all are below delta_i/2) or repeat the label without going back. Thus labels along the path strictly increase, and each new vertex lies strictly between half the current label and that label. This interval contains no half-label of the lacunary list. The path cannot end on a different loop. Every edge in the connected component lies on such a path or is incident along one, proving the assertion.

Write p_t=mu({t}). For each label i, distribute nonnegative weights over its edges and loop, proportional to the terms sqrt(p_t p_s) and p_(delta_i/2)/sqrt(2). Then

    sqrt(e_i Q_i)=sum_{edges label i} w_ts sqrt(p_t p_s)
                    +w_loop p_(delta_i/2)/sqrt(2),
    sum_{edges label i}w_ts^2+w_loop^2 <=e_i.                   (H3)

If Q_i=0 take all these weights zero. The total in (H2) is (1/2)z^T K z, with z_t=sqrt(p_t), off-diagonal entries w_ts and diagonal loop entries sqrt(2)w_loop. The sum of z_t^2 is at most one.

On a loop-free forest component, bipartition and the Hilbert--Schmidt bound give norm at most sqrt(E_J). On a component rooted at loop j the diagonal is at most l=sqrt(2e_j) at that one vertex, and the sum of squared off-diagonal edge weights is at most E_{j-1}. Split its vertices into the two bipartition classes with the root in the first. Its Rayleigh quotient is bounded by

    l||z_1||^2+2 sqrt(E_{j-1})||z_1||||z_2||,

so its norm at the top of the spectrum is at most phi_j. These bounds apply to countable components by finite truncation; the squared edge weights are summable. Since phi_J>=sqrt(E_J), the loop-free bound is already included in Phi(e). Thus (H2)-(H3) prove the uniform upper bound in (H1).

## 3. Matching lower graphs, including nestedness

Fix j. Choose a central clique size q with

    binom(q,2)+r_{j-1}<=r_j,
    q~sqrt(2r_j),

where r_0=0. For each i<j choose a disjoint peripheral group of size

    N_i=floor((r_i-r_{i-1})/q).

These sizes tend to infinity. The central and peripheral groups occupy o(M) vertices: their respective exponents are 1-delta_j/2 and 1-delta_i+delta_j/2, all strictly between zero and one. They therefore fit for all sufficiently large M.

For i<j make G_i contain G_{i-1} and all edges between the central group and peripheral group i, filling with arbitrary further edges until it has exactly r_i edges. This is possible since the increment uses at most r_i-r_{i-1} edges. At level j add the central clique; its union with the earlier graph has at most r_j edges. Fill to exactly r_j, and continue nesting up to every higher rank. Extra edges have nonnegative weights and can only improve the chosen nonnegative Rayleigh tests.

Restrict to vectors constant on each displayed group. The contribution of each own-level bipartite piece has asymptotic off-diagonal quotient entry

    c_i sqrt(q N_i)->sqrt(e_i),

and the central clique has diagonal entry c_j(q-1)->sqrt(2e_j). Ignoring the other nonnegative contributions, the limiting quotient is the star with these off-diagonal weights and this central loop. Its largest eigenvalue is phi_j. Thus the limiting maximum for nested exact-rank graphs is at least every phi_j. The uniform upper bound proves (H1), even with the nested restriction.

There is no assertion that a finite-dimensional graph optimizer is a star with a clique. The statement concerns the exact limit under the specified rank scales.

## 4. Complete asymptotic energy constraints for a quantum hierarchy

Take fixed exponents as above, r_i(m)~m^beta_i, nested projections P_i of rank r_i in C^m tensor C^n, n>=m, and v in the range of P_1. Consider

    B_m=I+a_m|v><v|+sum_i c_{i,m}P_i, rho_m=B_m/Tr B_m.         (H4)

All coefficients are nonnegative. Suppose a_m->a and r_i c_{i,m}^2->e_i. Adding the single-edge spike to the graph test gives the exact limiting largest norm

    max{a,Phi(e)}.                                            (H5)

For the upper bound split its two endpoints from the rest. Their coupling to the rest is bounded by sqrt(2m)sum_i c_i->0, because beta_i>1 and J is fixed; their own block tends to the single-edge value a. The remaining block is covered by (H1). The separate lower tests attain a and Phi(e).

If (H4) is APPT for all sufficiently large m, necessarily

    a<=2, and E_{j-1}+2sqrt(2e_j)<=4 for every j.               (H6)

To justify the second necessity physically, use the nested exact-rank graphs in Section 3 as nested subspaces spanned by antisymmetric Schmidt-witness vectors. Every flag of these ranks, together with a chosen vector in its first member, is obtained from the original flag and v by one global unitary. The unitary-orbit partial-transpose expectation is exactly one minus the weighted edge sum (and minus the nonnegative spike contribution). A graph Rayleigh quotient exceeding two therefore violates APPT. The single-edge/rank-two test similarly gives a<=2. This does not infer quantum necessity from nonnested graphs.

Conversely if max{a,Phi(e)}<2, the projection trace lower bounds against every Schmidt witness and the UNIFORM graph upper bound imply actual APPT for every sufficiently large m, for every n>=m. For a boundary energy vector satisfying (H6), apply a common fixed positive safety margin first, then let the dimension grow; a diagonal selection removes the margin. Thus (H6) describes precisely the closure of the attainable limiting energy vectors. It does NOT say that every finite sequence with limiting norm exactly two is APPT.

These conditions also force E_J<4 for finite J. The total centered-purity coefficient is

    D^2[Tr(rho_m^2)-1/D] -> a^2+E_J.                           (H7)

Indeed all nested cross terms vanish because r_i/r_j->0 for i<j, and the trace correction vanishes because r_J=o(m^2). The formula is uniform in n>=m for every fixed hierarchy.

## 5. Exact optimal coefficient for a fixed number of scales

Define the rational recursion

    d_0=4,
    d_j=d_{j-1}-d_{j-1}^2/8,  j>=1.                          (H8)

Among all APPT spectra of the fixed J-intermediate-scale form (H4), the sharp limiting centered-purity coefficient is

    8-d_J.                                                    (H9)

The uniquely optimal limiting energies and spike are

    a=2, e_j=d_{j-1}^2/8, E_j=4-d_j.                          (H10)

Proof. From (H6), e_j<=(4-E_{j-1})^2/8. The map
`f(x)=x+(4-x)^2/8` is increasing on [0,4], maps [0,4) into [0,4), and has derivative x/4. Induction gives E_j<=4-d_j. Strict monotonicity on the positive range shows that equality at the final step requires every earlier energy bound to be saturated; a^2<=4 is independent. This proves the upper bound and uniqueness at the energy-allocation level.

For (H10), sqrt(2e_j)=d_{j-1}/2 and

    E_{j-1}+2sqrt(2e_j)=4,

so every phi_j equals two. Apply a common factor 1-epsilon to all graph and spike coefficients, with fixed rational epsilon>0. The strict graph margin guarantees APPT eventually. Then let the dimension grow and only afterward let epsilon decrease to zero. This attains (H9) as the sharp maximum limit.

The coefficients can be chosen rational at every finite dimension: use a_m=2(1-epsilon) and

    c_{j,m}=(1-epsilon)/ceil(sqrt(r_j/e_j)).

Here e_j in (H10) is rational, and the ceiling square root is an exact integer operation. For delta_j=3^(-j), r_j is the integer floor of the 3^j-th root of m^(2*3^j-1). No floating-point approximation is a premise. An effective dimension threshold for the compactness margin is not supplied.

Any maximizing sequence in this class has bounded a_m and r_j c_j^2: a single-edge and a clique test bound them. Passing to convergent subsequences therefore justifies the same upper bound even if individual energy limits were not initially assumed. Together with the construction, this is an optimization theorem for the whole specified class, not just a proposed allocation.

The first values are

    J=1: 6,
    J=2: 13/2,
    J=3: 217/32.

Each fixed J has a positive deficit d_J from eight. Since d_j decreases to zero and

    1/d_j-1/d_{j-1}=1/[8(1-d_{j-1}/8)] ->1/8,

we obtain

    d_J~8/J,
    4/(J+1)<=d_J<=8/(J+2).                                   (H11)

Thus in this hierarchy model approaching the coefficient eight within epsilon requires order 1/epsilon intermediate scales, and the optimal allocation achieves that order. This is a sharp refinement of the earlier equal-energy sufficient construction, whose bound lost order 1/sqrt(J). It is NOT a theorem that every APPT near-maximizer, irrespective of spectral scaling model, must have this many levels.

## 6. Consequences and scope

The exact graph limit explains the interactions between scales rather than treating their square masses as independent. A small-scale clique and the earlier levels coupled through a star impose each prefix constraint in (H6). Optimizing all those constraints gives (H8), while single-scale clique bounds alone would miss them.

This gives a complete limiting optimization and energy rigidity for every fixed finite lacunary intermediate-rank hierarchy. It supplies improved certified-in-the-limit families for the gamma<=4 phase and makes precise why this particular bounded-length hierarchy cannot reach eight. It does not classify nonlacunary hierarchies, all possible finite-level spectra, finite-dimensional global optimizers outside EXACT_RECTANGULAR.md, or absolute separability. The analytic upper argument uses the compactness reduction of MULTISCALE.md, restated in Section 2, with a sharper one-loop component analysis; finite ancillary graph checks are not its substitute.
