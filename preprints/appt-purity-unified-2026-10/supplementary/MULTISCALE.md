# Sharp balanced APPT purity: a multiscale construction matches the unrestricted bound

Research working proof, 10 October 2026. No manuscript or Release is being prepared. The result is analytic, not Lean-formalized or externally peer reviewed. Exact finite checks accompany the identities and obstruction examples, not the unbounded compactness argument.

## 1. The result and its precise scope

Let Pmax(m,n) be the maximum of Tr(rho^2) over all APPT density matrices on C^m tensor C^n, where 2<=m<=n. Then

    Pmax(m,m) = 1/m^2 + 8/m^4 + o(m^-4).                         (T1)

More generally, along EVERY sequence m->infinity, n>=m and n/m->1,

    (mn)^2[Pmax(m,n)-1/(mn)] ->8.                                (T2)

For any fixed finite gamma>=1, the new unrestricted lower bound is

    liminf (mn)^2[Pmax(m,n)-1/(mn)] >= max{8,4+gamma},             (T3)

when n/m->gamma. Combining with UNRESTRICTED_BOUND.md gives an upper bound

    limsup (mn)^2[Pmax(m,n)-1/(mn)]
       <=min{4+4gamma,8+max(1,gamma-1)}.                          (T4)

Thus (T1)-(T2) have a SHARP leading excess-purity constant, without assuming a number of spectral levels or a shape for the maximizer. For general gamma>1 the bounds do not yet match. Exact finite-dimensional maxima, all maximizing spectra, and absolute separability remain unproved here.

The upper bound 8 at gamma=1 is already established for arbitrary APPT spectra in UNRESTRICTED_BOUND.md. The new task is a lower bound approaching 8. It requires arbitrarily many separated plateaus; the earlier single intermediate plateau only gives 6, and its combination with a broad plateau gives 25/4 in square systems.

## 2. A uniform matrix bound at separated scales

Fix a FINITE integer J>=1 and numbers

    1>delta_1>delta_2>...>delta_J>0,
    delta_{j+1}<delta_j/2,
    beta_j=2-delta_j in (1,2).

For example delta_j=3^(-j) works. Let r_j=r_j(M) be positive integers with r_j/M^(beta_j)->1. Let c_j>=0 satisfy

    r_j c_j^2 -> e_j>=0.

For each j let G_j be any simple graph on M vertices with at most r_j edges. The graphs need not be independent, nested, random, or disjoint. Put H_M=sum_j c_j A(G_j), E=sum_j e_j and emax=max_j e_j. Then

    limsup max_{G_1,...,G_J} lambda_max(H_M)
       <= sqrt(E)+sqrt(2 emax).                                 (T5)

All parameters J and delta_j are fixed BEFORE M tends to infinity. In particular (T5) does not claim a bound for an arbitrary unverified choice J=J(M).

### 2.1 Only matched amplitude scales can contribute

For an arbitrary sequence of graph choices take nonnegative unit maximizing vectors x=(x_1,...,x_M). A nonnegative maximizing vector exists because the matrices have nonnegative entries. Write p_i=x_i^2 and, for p_i>0,

    t_i=1+log_M(p_i)<=1.

Fix eta>0. For level j, products x_i x_l below M^(-beta_j/2-eta) contribute at most

    c_j r_j M^(-beta_j/2-eta)=O(M^-eta).

Products above M^(-beta_j/2+eta) occur in at most M^(beta_j-2eta)/2 unordered pairs, since sum_{i<l}p_i p_l<=1/2. Cauchy--Schwarz therefore bounds their contribution by O(M^-eta) as well. It follows that, up to an error tending to zero, level j uses only pairs satisfying

    |t_i+t_l-delta_j|<=2eta.                                    (T6)

The total mass of coordinates with t_i<-eta is at most M^-eta. Edges incident to these coordinates contribute at most O(M^(-eta/2)), again by Cauchy--Schwarz and c_j sqrt(r_j)=O(1). For every other coordinate replace t_i by t_i^+=max(0,t_i). This changes a matched sum by at most 2eta.

Let mu_M=sum_{p_i>0}p_i delta_{t_i^+}; it is a probability measure on [0,1]. Take a weakly convergent subsequence, with limit mu. The product measures converge weakly as well. The strip |t+s-delta_j|<=4eta is closed, so the upper bound for measures of closed sets and Cauchy--Schwarz give

    limsup c_j sum_{edges of G_j} x_i x_l
       <=sqrt{(e_j/2)(mu x mu){|t+s-delta_j|<=4eta}}.

Let eta decrease to zero. Continuity from above of a finite measure gives

    limsup (1/2)x^T H_M x
       <=sum_j sqrt(e_j Q_j),
    Q_j=(1/2)(mu x mu){t+s=delta_j}.                             (T7)

The same subsequence and measure are used for every j; J is finite. No optimizing measure is substituted independently at each level.

### 2.2 Lacunarity forces a forest

Only atoms of mu contribute to a line t+s=delta_j. Let p_t=mu({t}) and consider the countable graph on those atoms, putting an off-diagonal edge {t,s} when t!=s and t+s equals one of the delta_j. There is also a loop at t=delta_j/2 when that atom is present. We have

    Q_j=sum_{t<s, t+s=delta_j}p_t p_s
         +(1/2)p_(delta_j/2)^2.                                 (T8)

The graph of OFF-DIAGONAL edges is a forest. To prove this, suppose a simple cycle existed and choose its edge with the largest label delta_j. Neither neighboring edge has that same label: two incident equal-sum edges would have the same other endpoint. Thus both neighboring labels are smaller, each strictly below delta_j/2 by lacunarity. Since all vertices are nonnegative, the two endpoints of the largest edge are individually at most their other neighboring labels. Their sum would be strictly less than delta_j, a contradiction. This excludes every finite cycle and proves the forest assertion, including for a countable atom set.

For each j with Q_j>0, represent the scalar square root as

    sqrt(e_j Q_j)
      =sum_{off edges with label j}w_ts sqrt(p_t p_s)
         +w_loop p_(delta_j/2)/sqrt(2),

where all weights are nonnegative and the sum of their squares for that label is e_j. Choose weights proportional to the coefficients in (T8). If Q_j=0 choose weights zero. Across labels the sum of squares is at most E, and every loop weight is at most sqrt(emax).

Let z_t=sqrt(p_t). The forest is bipartite. Its weighted off-diagonal adjacency operator has norm at most sqrt(sum_off_edges w_ts^2)<=sqrt(E): after a bipartition it has off-diagonal block B, and ||B||_op<=||B||_HS with ||B||_HS^2=sum_edges w_ts^2. This argument also holds for the countable forest by finite truncation, since the squared edge weights are summable. As sum_t z_t^2<=1,

    sum_off_edges w_ts z_t z_s <= sqrt(E)/2.

The loop terms are at most sqrt(emax/2) sum_t p_t <=sqrt(emax/2). Hence

    sum_j sqrt(e_j Q_j)<=sqrt(E)/2+sqrt(emax/2).                  (T9)

Equations (T7)-(T9) prove (T5). The initial graph sequence was arbitrary, so the estimate is uniform over all graph arrangements. This is not a random-matrix limit or a test of a chosen graph family.

## 3. Add an isolated spectral spike

Suppose a_M->a>=0 and E_f is the single-edge adjacency matrix on any selected pair of vertices. Then

    limsup max_{graphs,f} lambda_max(H_M+a_M E_f)
       <=max{a,sqrt(E)+sqrt(2emax)}.                             (T10)

Split the two endpoints of f from the rest. Their block has top eigenvalue a_M+O(sum c_j)->a. The cross block has norm at most sqrt(2M)sum c_j->0, because beta_j>1 and J is fixed. The remaining principal block is covered by (T5), with at most M vertices and the same edge bounds; padding by two zero coordinates does not affect the amplitude argument. The variational bound for a block-diagonal matrix plus the cross block proves (T10).

This separate spike contributes four units of centered squared spectral mass when a approaches 2. The intermediate scales can contribute another four while still satisfying the all-unitary positivity requirement.

## 4. Explicit rational states with an eventual all-unitary certificate

Fix an integer h>=1 and put J=2h^2. Choose delta_j=3^(-j) and beta_j=2-delta_j. For every integer m use

    r_j=floor(m^(beta_j)),
    L_j=ceil(sqrt(2r_j)).

These integers are exactly defined without floating-point arithmetic: r_j is the integer floor of the 3^j-th root of m^(2*3^j-1). For each fixed J, the ranks are strictly increasing and below m(m-1)/2 for all sufficiently large m.

Fix a rational epsilon in (0,1). On C^m tensor C^n, n>=m, choose any nested coordinate projections

    P_1<=...<=P_J, rank(P_j)=r_j,

and a unit coordinate vector v in the range of P_1. Set

    a=2(1-epsilon),
    c_j=2(1-epsilon)/((h+1)L_j),
    B=I+sum_j c_j P_j+a|v><v|,
    rho=B/Tr B.                                                 (T11)

All eigenvalues are rational and B is positive definite. Each level has

    r_j c_j^2 -> e=2(1-epsilon)^2/(h+1)^2,
    E=J e=4h^2(1-epsilon)^2/(h+1)^2.

Therefore

    sqrt(E)+sqrt(2e)=2(1-epsilon).

Equation (T10) bounds the limiting maximum Schmidt-test matrix norm by 2(1-epsilon)<2.

To verify the quantum implication directly, fix any global unitary U and any unit test vector psi with nonnegative Schmidt coefficients x_i. For W=(|psi><psi|)^Gamma, a rank-r_j projection has trace against W at least minus the sum of the r_j largest products x_i x_l. The vector term is at least minus a times the largest product. These elementary projection bounds follow from eigenbasis diagonal weights in [0,1] with prescribed sum. Thus

    <psi,(UBU*)^Gamma psi>
       >=1-sum_j c_j sum_{r_j largest pairs}x_i x_l
             -a max_pair x_i x_l.

The right side is 1-(1/2)x^T(H_m+aE_f)x for some graphs with r_j edges and a distinguished pair f. The uniform estimate (T10), with its strict margin, consequently proves that for EVERY sufficiently large m the normalized state (T11) is APPT for EVERY unitary U. In fact the unnormalized partial transposes have a uniform positive lower bound depending on epsilon once m is large enough.

The threshold in m may depend on the fixed h and epsilon; no quantitative or efficient finite threshold is claimed. A limit equal to 2 is NOT used to infer finite-dimensional positivity. The fixed positive slack is essential.

## 5. Purity and the order of limits

Let D=mn and

    T=a+sum_j c_j r_j,
    S=a^2+sum_j c_j^2 r_j
           +2 sum_{i<j} c_i c_j r_i+2a sum_j c_j.

These are Tr(B-I) and Tr((B-I)^2), respectively; the formula uses nested projections. Exact trace arithmetic gives

    D^2[Tr(rho^2)-1/D]=(S-T^2/D)/(1+T/D)^2.                      (T12)

For i<j, r_i/r_j->0, so c_i c_j r_i->0. Since J is fixed and r_J/m^2->0, one has T^2/D->0, T/D->0, and sum_j c_j->0 whenever n>=m. Hence

    D^2[Tr(rho^2)-1/D]
       ->(1-epsilon)^2[4+4h^2/(h+1)^2].                         (T13)

This gives a lower bound on liminf D^2[Pmax-1/D] for EACH fixed h and epsilon. First take the dimension limit. Only afterward let epsilon decrease to zero and h increase without bound. The resulting lower bound is 8. No interchange with a growing number of levels inside (T5) is made.

The construction is independent of the aspect ratio apart from the available dimension. Combining its lower bound 8 with the earlier lower bound 4+gamma proves (T3). When gamma=1, (T4) is 8. The liminf and limsup therefore agree, proving (T1)-(T2).

## 6. Why the extra levels matter, and what remains

The old inner-polytope conjecture had centered coefficient max(4,gamma), giving 4 in square systems. The earlier one-spike/broad-plateau family gives 4+gamma, hence 5. A single intermediate plateau gives 6, and the precisely solved four-level intermediate-plus-broad sector gives 25/4. The lacunary hierarchy now approaches 8 and matches an upper bound that applies to every APPT spectrum.

This resolves the balanced leading-order maximal-purity problem, not the exact finite-dimensional maximum. It gives no classification of maximizers and no assertion that a bounded number of levels cannot also attain 8 by a different mechanism. It does not prove APPT equals absolute separability or that the constructed states are absolutely separable. For gamma>1 the leading constant remains between the bounds (T3)-(T4).

The forest property cannot be silently dropped. For example labels 3/5,1/2,2/5 admit a triangle on vertices 7/20,1/4,3/20. Its adjacency matrix has top eigenvalue 2, greater than sqrt(3), so the forest Hilbert--Schmidt bound used above is invalid for these nonlacunary labels. The finite checker includes this obstruction. All-unitary validity, the compactness step, and the specified order of limits are proved in the text, not by finite tests or optimizer output.
