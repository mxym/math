# Pentagonal spectral candidate: cut barriers in both direct-sum directions

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.


No new unrestricted C5 rank bound. These statements explain what kinds of genuinely five-party constructions would be needed. Primary conic reference: [Zhou arXiv:2610.34273v3, Thm 5.6 and §6.3](https://arxiv.org/html/2610.34273v3#S6.SS3). All source and target graph tensors here are products of edge identities, not generic tensors.

## Unique conic extremizer and stability

Index mod 5. Set x_i=p_(i,i+1), y_i=p_(i,i+2), t_i=y_(i+1)+y_(i+3)−x_i≥0, τ=Σt_i, ε=25/6−Σx_i. For Q=J−2P copositive, 1^TQ1=6ε−2τ≥0, so τ≤3ε. If ε≤1/6, apply copositivity at 1 ± sqrt(1^TQ1)e_i to obtain |(Q1)_i|≤sqrt(6ε); if Qtotal=0 use an arbitrarily small perturbation instead. The row equations are
 2y_i+y_(i+1)+y_(i+2)+2y_(i+3)=5/2−(Q1)_i/2+t_i+t_(i−1).
The circulant has determinant 6 and inverse first row (−1,−7,−1,5,5)/6. Consequently ||y−5/12||∞≤(19/6)(sqrt(6ε)/2+3ε), and ||x−5/6||∞≤2||y−5/12||∞+3ε. In particular no averaging is needed: the only feasible point attaining 25/6 has p*=5/6 on edges and 5/12 on chords. Its feasibility follows from Zhou’s scaled maximum cuts: p*= (25/24) times the average of the five maximum-cut semimetrics, or (5/24) times their sum.

## One graph source to a direct sum of graph targets

For each of the five cuts C let X_C be the cut rank of the source and x_(C,s) that of target summand s. Any such restriction or degeneration implies Σ_s x_(C,s)≤X_C by flattening. Put θ_C=5/24 and α=Σ θ_C=25/24≥1. Then
 Σ_s ∏_C x_(C,s)^θ_C ≤ ∏_C (Σ_s x_(C,s)^α)^(θ_C/α) ≤ ∏_C X_C^θ_C
by Hölder and monotonicity of the ℓ^α norm relative to ℓ^1. The candidate’s power product equals exactly its implied graph spectral value, so all such forward certificate inequalities are already obeyed at p*. This holds without assumptions on the local maps or tensor support for establishing the conversion.

## Reverse direction: any local linear maps, support-preserving summand images

Suppose a direct sum of graph sources U_s restricts to a graph target T. Let S_s be the image of summand s, so T=Σ_s S_s for arbitrary local component maps. Assume each S_s is supported on the support of T (the values of coefficients need not be positive or even all equal). Write Ω_s for the corresponding subset of edge-label assignments with nonzero coefficients. For a cut C with crossing target edges E_C, rows and columns of its flattening are indexed by partial vertex labels; any nonzero entry of S_s has matching crossing labels on both sides. Distinct crossing labels therefore give disjoint nonzero diagonal matrix blocks, so rank_C(S_s)≥|π_(E_C) Ω_s|. Since S_s is a restriction of U_s, source flattening rank is at least as large.

For the unweighted pentagon with uniform target dimension q, E_C omits exactly one of five edges as C varies, each edge omitted once. Loomis–Whitney (or entropy chain rule and Shearer) gives
 ∏_C |π_(E_C) Ω_s|^(5/24) ≥ |Ω_s|^(5/6).
The Ω_s cover all q^5 target assignments. Thus the implied source costs satisfy
 Σ_s ∏_C rank_C(U_s)^(5/24) ≥ Σ_s |Ω_s|^(5/6) ≥ q^(25/6).
Subadditivity of u^a for a=5/6 proves the last inequality; the bound is strict if at least two Ω_s are nonempty. For example if each Ω_s covers at most fraction f<1 of target assignments, the ratio exceeds the barrier by at least f^(-1/6). This works under arbitrary correlated filters and arbitrary maps if their *individual images* obey the support condition. Merely summing to T does not imply it.

General nonuniform result: let target edge dimensions q_e, any family of vertex cuts C, and θ_C≥0 with p_e=Σ_{C:e∈E_C}θ_C≤1. For uniform X on Ω⊂∏_e[q_e], entropy obeys H(X_(E_C))≤log |π_(E_C)Ω| and H(X_(E_C))≥Σ_{e∈E_C} H(X_e|all earlier edge coordinates), using a common edge order and that conditioning decreases entropy. The conditional deficits d_e=log q_e−H(X_e|all earlier edge coordinates) are nonnegative. Therefore
 Σ_C θ_C(log∏_{e∈E_C}q_e−log|π_(E_C)Ω|) ≤ Σ_e p_e d_e ≤ Σ_e d_e = log∏_e q_e−log|Ω|.
So each normalized source value is at least the volume fraction of target support its image covers. The same cost barrier holds for arbitrary graph and nonuniform dimensions. In particular projecting independently onto edge-label ranges is unnecessary.

## Reverse direction with sparse interference

Without support preservation let Ω_s include only the nonzero entries of S_s that are inside target support. Fix a cut C and let G_(s,C) be the undirected graph on π_(E_C)Ω_s connecting distinct labels h,k whenever the C-flattening of S_s has any nonzero entry with row crossing label h and column crossing label k, or vice versa. (Rows and columns each have every crossing edge label at its own endpoint.) An independent label set gives a diagonal nonsingular minor: pick one supported nonzero entry per label from its matching block. Thus rank_C(S_s)≥α(G_(s,C))≥|π_(E_C)Ω_s|/(Δ_(s,C)+1). The same proof as above then shows Σ_s candidateCost(U_s) ≥ candidateCost(T)/max_s∏_C(Δ_(s,C)+1)^θ_C. Subexponential-in-power maximum interference degrees leave the asymptotic barrier unchanged. Uniform C5 can additionally use the entropy gain from each summand covering at most a fraction f of target support.

A route beating the value via direct sum of graph sources must therefore use extensive off-support cancellation, unless the argument uses a different mechanism than local restriction. In particular the results do not preclude stronger non-graph primitives, additions with broadly cancelling images, or asymptotic spectral constraints independent of cuts. No general rank lower bound follows.
