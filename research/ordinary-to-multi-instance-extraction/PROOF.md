# Multi-instance extraction from arbitrary strong seeded extractors

Throughout log denotes log₂. Write TV(P,Q)=(1/2)Σ_z|P(z)−Q(z)| and H∞(X)=−log max_x Pr[X=x]. Uniforms introduced in a replacement are independent of one another and of the source, seeds and any selection labels. Alphabet sizes and seed spaces are finite. Each seed may have a fixed seed law on its alphabet; in the binary specialization all seeds are uniform. No independence between the input blocks is assumed.

## 1. Precise general statement

For t≥1, coordinate i∈[t] has an input alphabet of size N_i≥2, an output alphabet of size M_i≥1, and a function E_i(x_i,s_i). Put n_i=log N_i. Each E_i is strong (k_i,η_i) for its specified seed law: for every source V with H∞(V)≥k_i, independent of S_i,

    TV((S_i,E_i(V,S_i)), (S_i,U_i)) ≤ η_i,

where U_i is uniform on the M_i outputs. Assume 0≤k_i≤n_i, 0≤η_i≤1; the seeds S_i are mutually independent and independent of all source variables. Choose any 0≤r_i<n_i and 0<γ<1. Define

    K_i = ceil(2^{k_i})−1,
    a_i = min(M_i, 1+M_i η_i),  b_i = M_i−a_i,
    q_i = min(1, K_i 2^{−r_i}),
    D = min(1, (1/2) sqrt( Π_i(a_i+b_i q_i) − 1 )).

Let X have arbitrary joint distribution on the product of the input alphabets and let Δ be an upper bound on its deficiency Σ_i n_i−H∞(X).

**Theorem.** There is a deterministic choice J=J(X)⊆[t] such that the retained positions satisfy the pointwise weighted budget

    Σ_{i∈J}(n_i−r_i) ≤ Δ + log(1/γ).

Define Y_i=E_i(X_i,S_i), and Z_i=Y_i for i∈J, Z_i=U_i otherwise. Then

    TV( (J,X_J,S,Y), (J,X_J,S,Z) ) ≤ γ+(1−γ)D.

Here S and Y,Z denote the full vectors. The symbol (J,X_J) can be encoded as a label with an ordering for the listed coordinates. In particular both J and its complement are chosen based on X alone, and are independent of the seed vector. The theorem includes their public disclosure. An implicit deterministic rule depending on the full law of X is sufficient; no time bound for finding it is asserted.

## 2. One-instance consequence: few high-collision neighbors

Fix coordinate i and a reference input x. Define

    c_i(x,x') = M_i Pr_{S_i}[E_i(x,S_i)=E_i(x',S_i)],
    B_i(x) = {x' : c_i(x,x') > a_i}.

If a_i=M_i then B_i(x) is empty. Otherwise a_i=1+M_iη_i. If |B_i(x)|≥2^{k_i}, the uniform source on this set has entropy at least k_i. On its strong-extractor experiment, consider the event that the output equals E_i(x,S_i), where x is fixed and the seed is visible. The ideal probability of the event is 1/M_i. By the strict defining inequality the real probability, averaged over x' uniform on B_i(x), is strictly more than 1/M_i+η_i, contradicting the ordinary extractor guarantee. Thus |B_i(x)|<2^{k_i}, so it is at most K_i. In all cases the collision kernel satisfies the nonnegative pointwise estimate

    c_i(x,x') ≤ a_i + b_i·1[x'∈B_i(x)].

This is the specialization to a reference codeword of the standard extractor-to-list-decoding implication (also noted in Guan–Wichs–Zhandry §3.2); its use in Section 3 is the new step. The argument is about a known finite table E_i and a statistical event on its public-seed output, not about inverting any function. The strict boundary can matter for integer parameters: the permitted size is ceil(2^{k_i})−1, not implicitly floor(2^{k_i}) with equality assumed impossible.

## 3. All blocks extract from a dense source

For a set I of positions, call a source V=(V_i)_{i∈I} r-dense if for every A⊆I,

    max_v Pr[V_A=v] ≤ 2^{−Σ_{i∈A} r_i}.

The empty restriction is allowed with value 1. Denote by P the joint law of (S_I,(E_i(V_i,S_i))_{i∈I}), and by Q the law of (S_I,U_I). The reference therefore includes exactly the same seed vector and its law, not just the output marginals. Let V' be an independent copy of the **whole** V. Relative chi-square divergence satisfies

    1+χ²(P || Q) = E_{V,V'} Π_{i∈I} c_i(V_i,V'_i).             (1)

To verify (1), conditional on each seed vector s of positive probability let p_s(y) be the conditional output law. Then P(s,y)=Pr[S_I=s]p_s(y) and Q(s,y)=Pr[S_I=s]/Π_i M_i. Consequently 1+χ²=Σ P²/Q = (Π_i M_i) E_s Σ_y p_s(y)². That inner sum is the collision probability of two independent source samples given the **same** seed vector. Applying the independent seed laws to the two fixed source samples multiplies the individual collision probabilities, giving (1). All outcomes with zero seed mass are omitted from both laws.

For a fixed first sample v and subset A⊆I, the expression from multiplying the indicator terms is bounded by

    Pr[ for all i∈A, V'_i∈B_i(v_i) | V=v ]
      = Pr[V'_A∈Π_{i∈A} B_i(v_i)]
      ≤ (Π_{i∈A}|B_i(v_i)|) 2^{−Σ_{i∈A} r_i}
      ≤ Π_{i∈A}K_i 2^{−r_i}.                                  (2)

The equality uses independence of V and V', not independence of blocks of V'. The middle inequality uses the pointwise min-entropy cap on the entire joint restriction V'_A and the elementary cardinality of a product set; it is valid regardless of any internal dependencies. For the sharper q_i cap, omit indices with K_i 2^{−r_i}>1 before using (2), which can only increase the probability, yielding the bound Π_{i∈A}q_i. No factor for a seed value is paid. Expanding the product in (1) with the nonnegative pointwise kernel bound and using (2) therefore gives

    1+χ²(P || Q) ≤ Π_{i∈I}(a_i+b_i q_i).

Cauchy–Schwarz in the reference law yields TV(P,Q)≤(1/2)√χ²(P||Q); it is also at most 1. This is a TV assertion on the joint law with public seed vector, equivalently an average of the seed-conditioned distances, not a pointwise guarantee for each seed. For I empty there is no output and the bound is zero. Every factor a_i+b_i q_i is at least 1, so the single number D defined above bounds every such coordinate restriction. Universal hashing is recovered directly by taking a_i=1 and B_i(x)⊆{x}; using the extractor-based neighborhood cap in this product bound is the new step.

## 4. Exact source partition into fixed and dense coordinates

This is the density-restoration construction used in the literature, written here for arbitrary finite alphabet sizes and weights. It explicitly partitions the **original source support**, rather than replacing X by a nearby source in the definition.

Keep a residual subset R of the support of X, initially the entire support. While its original probability w=Pr[X∈R] is at least γ, use the residual law X conditioned on R:

1. If the law on all coordinates is r-dense, take J=∅ and remove the entire residual set as one good component.
2. Otherwise choose a violating assignment X_J=z_J on a nonempty set J of maximal cardinality among all violations; its residual conditional probability is strictly more than 2^{−Σ_{j∈J}r_j}. Remove all points of R with that assignment as one good component.

Choose a deterministic tie-breaking rule. Given a removed nonempty-J component, the coordinates in J are constant. Its complement is r-dense: if A disjoint from J violated density under the conditioned component, multiply its conditional probability by the residual probability of X_J=z_J. The resulting residual probability of the assignment on J∪A would strictly exceed 2^{−Σ_{i∈J∪A}r_i}, a violation on an even larger coordinate set. No conditional min-entropy of a particular block given all other free blocks is assumed.

Each positive-probability step makes progress in a finite support. On a nonempty selected J, the cap on the original joint probability of each x is 2^{Δ−Σ_i n_i}. At most Π_{i∉J}N_i inputs extend its prescribed value. Thus

    2^{−Σ_{j∈J}r_j}
      < Pr[X_J=z_J | X∈R]
      ≤ 2^{Δ−Σ_{j∈J}n_j}/w
      ≤ 2^{Δ−Σ_{j∈J}n_j}/γ.

This implies the asserted weighted budget (strict for these components). For the J=∅ steps the budget is immediate. End with residual mass e<γ, possibly zero. On this exceptional component set J=∅ (so the pointwise budget still holds), even if it is not dense.

Let L label the removed components and, if it is present, the one exceptional residual component. Since these partition the old support, L=L(X) and J=J(L) are deterministic, and the seeds retain their independent laws even conditional on L. In a good component the outputs on I=[t] minus J have distance ≤D to uniform jointly with S_I by Section 3. The withheld seed tuple S_J is independent within the component, because it is independent of X,L,S_I. Adjoining S_J and the retained outputs, computed deterministically from S_J and the fixed raw values X_J, preserves this distance (adjoin the same independent randomness and apply a map). This also proves that every retained output in the ideal experiment is computed from the **original** X and its seed, as in the definition. Average TV with the common label L is exactly the weighted average of the conditional distances, so it is ≤(1−e)D+e≤γ+(1−γ)D. Because (J,X_J) is a deterministic function of L on every component (it is empty for the residual case), project out L and keep (J,X_J). This proves the theorem on the unreplaced original source.

## 5. Binary specialization and original open question

Set each alphabet size to N_i=2^n, M_i=2^m, all extractors equal, and their seed laws uniform as in Guan–Wichs–Zhandry Definition 3.1. In particular k and η are the ordinary single-instance min-entropy and TV-error parameters; they are not names for the joint t-instance threshold and error. Take t≥1, 0≤α≤1, and target 0<ε≤1. A sufficient real parameter choice is

    η ≤ ε²/(4 t 2^m),
    r = k+m+log(4t/ε²) < n,
    γ = ε/2.

Indeed a_i+b_i q_i≤1+2^mη+2^{m+k−r}≤1+ε²/(2t). Because (1+x/t)^t≤exp(x), and exp(x)−1≤2x on 0≤x≤1/2, the product minus one is at most ε². Thus D≤ε/2 and the full distance is at most ε. Here Δ≤(1−α)tn, so with I=[t] minus J the budget proves

    |I(X)| ≥ max{0, t − floor(((1−α)tn + log(2/ε))/(n−r))}.

Consequently a continuous permissible fraction is

    β = max{0, 1 − ((1−α)n + log(2/ε)/t)/(n−r)}.

In the nontrivial regime this also reads β=α−((1−α)r+log(2/ε)/t)/(n−r). There is no silent switch from rate α to entropy k. With r≤n/2 this yields the near-rate guarantee β≥α−2(r+log(2/ε)/t)/n. In particular, if the ordinary extractor supports k=O(m+log t+log(1/ε)) under the required single-instance error, it has β≥α−O((m+log t+log(1/ε))/n); its seed length is unchanged. The proof is uniform in the extractor function and does not rely on a family-specific structural condition. It gives a quantitative affirmative answer to the original general strong-extractor question, with no additional structural property of the extractor. The pointwise lower bound guarantees at least one replacement when (αn−r)t>log(2/ε). It does not say that every choice of single-instance parameters yields a nontrivial multi-instance claim. For a sequence of extractors, the weaker β≥α−o(1) reading follows whenever r=o(n) and log(2/ε)=o(tn).

For Definition 3.1, use I_X=I(X), drop the raw values outside I(X) and the chosen set from the compared joint laws, and retain all seeds and all output positions. This gives exactly its almost-uniform replacement property, with a deterministic source-dependent choice that is seed-independent. In the stronger displayed theorem the label can be disclosed too. Seeds freshly drawn independently across blocks are needed for (1). No conclusion is made about correlated seeds, seeded choices of I, quantum or computational indistinguishability, or application to a specific implementation.

## 6. Why qualify both single-instance parameters

These are examples about abstract extraction definitions. They neither construct attacks on a protocol nor claim any concrete scheme unsafe.

**Entropy threshold cannot simply be omitted.** Given an ordinary strong (k₀,η) extractor on a bits, extend its input to a+b bits by ignoring the last b bits. An input with min-entropy at least k₀+b has a first-a-bit marginal of min-entropy at least k₀, since each fiber has size 2^b. Therefore the extended function is genuinely ordinary strong (k₀+b,η). Now fix its active prefix at every position and make the ignored bits independent uniform. The joint rate is α=b/(a+b). In the real experiment every output is determined by the public seed alone. If an ideal experiment replaces at least B positive-output-length positions with uniform symbols, the probability that every output still agrees with its predetermined value is at most M^(−B), where M is the output alphabet size. The distance is at least 1−M^(−B). Thus an extractor-independent rate-minus-loss formula that ignores the single-instance threshold cannot hold literally across all parameters. For example take b=a, fix m=1 and any t, and fix a target ε<1/2. The base extractor can be the binary inner product E(x,s) with uniform s∈{0,1}^a at threshold k₀=a/2: distinct inputs collide with probability 1/2, so (1) for one block gives error at most 2^(−a/4)/2. The extended extractor is an ordinary strong extractor with error tending to zero at threshold k=3a/2. Its joint source above has α=1/2 for all a but no positive β is possible at target ε<1/2, because a positive β forces at least one replacement. Thus this also excludes unconditional near-rate and positive-β readings at every source rate. The source rate is below the single-instance threshold per block; this does not contradict Section 5.

**The single-instance error cannot be kept independent of the number of replacements.** Starting with any ordinary strong extractor on n bits with error η₀ at k₀, add independent public tag bits. On a tag set of probability μ, output a fixed constant instead of running the old extractor. At k₀ this is still strong with error at most (1−μ)η₀+μ(1−1/M), by conditioning on the tag. Even at full input entropy, let an ideal experiment replace at least B positions using any selection independent of the fresh seeds (it may depend on the source). In the real experiment every tagged output equals the fixed constant; in the ideal experiment that same event has probability at most (1−μ(1−1/M))^B, by conditioning on the selected positions and using the independent tags and fresh uniforms. Thus the distance is at least 1−(1−μ(1−1/M))^B. This explains why a universal guarantee must account for error accumulation. It does not assert that the sufficient ε²/(t 2^m) scale of this proof is necessary or optimal.
