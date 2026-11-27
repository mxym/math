# Matching word-locality bounds without an explicitness requirement

## 1. Model and statement

A deterministic evaluator takes an n-bit input x and reads a key S of ell independent uniform w-bit words through a word-probe interface. It returns an n-bit value. The choice of locations may depend on x and on previously read word values. Its locality t is the maximum number of probes per evaluation; repeated probes can be cached without increasing this number. The evaluator is stateless across evaluations and its description is public. There is no time or description-size restriction in our upper bound. A selective guarantee means that for any fixed list of at most k distinct inputs, their output vector has total variation (TV) distance at most epsilon from an independent uniform vector. The adaptive guarantee allows each next input to depend on preceding outputs. These are the selective and adaptive versions of [DLW] Definition 3.1; the underlying probe model is their Definition 3.2.

Set epsilon=2^(-n), 2≤n≤k≤2^n, w≥1, A=kn/w, and let

    T_*(n,k,w) = max{1, n/w, n / sqrt(w log₂(2+A))}.

**Theorem 1 (nonexplicit upper; unrestricted probe lower).** There is an epsilon-almost k-wise independent family for the adaptive guarantee with ell≤C_up ceil(A) and t≤C_up T_*, for an absolute constant C_up. Conversely, for every fixed C≥1, every such family with ell≤C ceil(A) has t≥c_C T_* for a positive constant c_C, even with only the selective guarantee. Every selective family also requires ell≥ceil(A).

In the upper bound, cell probe complexity does not include access to the public evaluator description. We use an exponentially large fixed catalog of address-and-matrix maps, and make no claim that an efficient evaluator can replace it. Key word locality can be adaptive to the key, separately from the adaptivity of input selection in the statistical guarantee.

## 2. Upper bound

If w≥kn, put k independent F_(2^n) coefficients in one key word and read it to evaluate the polynomial of degree less than k at x (identify n-bit strings with field elements). For any k distinct inputs the Vandermonde evaluation matrix is invertible; exact uniform outputs for any adaptive sequence follow by applying this to each fixed transcript, as below. The key is one word and t=1.

Otherwise A≥1. Write L=ceil(log₂(2+A)), alpha=w/n, and choose

    d = ceil(64 max{1, n/w, n/sqrt(wL)}),   B = ceil(512 A/d).
    ell_data = d B,   h = n+ceil(log₂ k)+4.

Use h independent header bits, padded to whole words, followed by ell_data independent data words partitioned into d chunks of B words each. Header and data are independent. A catalog entry, indexed by the header, specifies for every possible x both one address within each chunk and an n × (dw) binary matrix. To evaluate at x, read the header and the d specified words and apply that matrix to their concatenated dw bits. Each candidate entry is sampled by choosing all addresses and all matrix entries independently and uniformly in their respective alphabets.

We first analyze one random entry and an arbitrary fixed list X of k distinct inputs. For a subset of q of those inputs let U be their total number of distinct addressed data words. Put u=floor(8q/alpha). If u<d, U≤u is impossible since every input uses one word in each chunk. Otherwise, for any fixed set of u data words with u_v in chunk v, all the specified qd addresses fall into it with probability

    ∏_v (u_v/B)^q ≤ (u/ell_data)^(dq)

by arithmetic/geometric mean; zero u_v causes no problem. Union over the containing sets gives

    Pr[U≤u] ≤ binom(ell_data,u) (u/ell_data)^(dq).

Here u≤dq/8 from d alpha≥64, and ell_data≥512 k/alpha implies ell_data/u≥64 k/q≥64. In particular, each positive u is in range. Using binom(ell_data,u)≤(e ell_data/u)^u, the base-two log of the last upper bound is at most
u log₂ e − (dq−u) log₂(ell_data/u) ≤ −(dq/2) log₂(64k/q). The inequality uses log₂ e<2 and log₂(ell_data/u)≥6. There are at most binom(k,q)≤(64k/q)^q subsets of size q. Since d≥64, their total failure probability is at most

    2^(−(dq/4) log₂(64k/q)).                              (1)

Only q≥q_0=d alpha/8 can contribute. If q_0>k, no failure is possible. Else q log₂(64k/q) is increasing on (0,k], by differentiation, and the exponent magnitude in (1) is at least

    (d² alpha/32) log₂(512 A/d) ≥ (d² alpha/64) L ≥ 64 n.

For the first inequality, k≥n and w≥1 imply 1, n/w and n/sqrt(wL) are each at most sqrt(A), hence d≤65 sqrt(A). Also 2^L≤2(2+A)≤6A, while (512A/d)²≥(512/65)² A>6A. The last inequality is the defining choice of d. Summing over q≤k≤2^n, the probability that any nonempty subset fails the address condition is at most 2^(-63n). On the complementary event, w U≥8nq for every subset of size q.

Condition on any address pattern with that property. Stack the n output rows for all k inputs as a binary matrix on the full data key (fill all unread columns by zeros). For a specified nonzero linear combination of the stacked rows, let q be the number of input blocks with some nonzero coefficient. For each physical data bit in the union of the q tapped word sets, some selected input block contributes at least one independent fair matrix coefficient. The parity on that bit is fair, and different physical bits use disjoint independently sampled matrix entries. Thus the probability that this combination vanishes is exactly 2^(-wU)≤2^(-8nq). There are binom(k,q)(2^n−1)^q such combinations, bounded by 2^(2nq) because k≤2^n. Summing over q≥1 bounds rank deficiency by Σ_{q≥1}2^(-6nq)≤2^(-5n). Including address failure, a random entry has full nk-row rank on the fixed list except with probability at most 2^(-4n). This test concerns the full rank of the stacked map, not fresh bits in each successive probe.

Now draw K=2^h candidate entries independently. For the fixed X, the event that at least b=K 2^(-n) entries are rank deficient has probability at most

    binom(K,b) (2^(-4n))^b ≤ (e 2^(-3n))^b ≤ 2^(-nb).

Here b is an integer at least 16k. There are at most 2^(nk) lists X of length k with distinct inputs. A union bound of at most 2^(nk−nb)<1 shows that some fixed public catalog has a fraction less than 2^(-n) of deficient entries for each X. We use that catalog thereafter; it is not fresh randomness. Duplicate entries are allowed and the header samples a uniform index, not a uniform distinct map.

Fix any deterministic adaptive input-selection procedure. Repeated queries may be answered by caching its earlier answer, and shorter procedures may be padded to exactly k distinct queries while discarding the padding in their output; k≤2^n makes this possible. Consider the augmented ideal transcript in which the header index is uniform and independent of the uniform oracle responses. Given any fixed resulting input list X, the fraction of bad headers is less than epsilon. This proves that the ideal augmented transcript is good except with probability epsilon, even though X itself depends on ideal responses. For any fixed good augmented transcript, its stacked data map has full nk-row rank for that fixed header and list. Its prescribed outputs therefore have probability 2^(-nk) under uniform data. The fixed output vector dictates that same input list under the deterministic query rule, so the real and ideal atom probabilities agree at every good augmented transcript (including the factor 1/K for its header). TV distance is at most the ideal bad mass: the sum of the overlapping masses on good transcripts is at least 1−epsilon. Forgetting the header cannot increase TV. Conditioning on any randomized query procedure's own independent coins and averaging proves the adaptive guarantee. The one-word field construction is the same argument with every list good.

For resources, ell_data=d ceil(512 A/d)≤512 A+d and d≤65 sqrt(A)≤65A. Since h≤2n+4≤6n, the header cost is at most 6n/w+1 words. Thus ell=ell_data+ceil(h/w)=O(A) and t=d+ceil(h/w)=O(T_*); ceilings and padding are included. The description records all addresses and all matrices; it is not charged to random key words and is not claimed polynomial-sized.

## 3. Lower bound

The first two support bounds are direct. For any one fixed input, a deterministic w-bit word-probe decision tree of depth at most t has at most 2^(wt) leaves and hence at most that many possible outputs. If wt<n then its support under the ideal law has mass at most 1/2, so selective TV is at least 1/2. The integer conclusion wt≥n holds because epsilon<1/2. Likewise for fixed k distinct inputs the support has size at most 2^(w ell), so selective TV below 1/2 requires ell≥ceil(A).

The case A≤1 already has T_*=1. For A>1 set L₀=log₂(2+A), T_0=n/sqrt(w L₀). Fix C and choose C_0≥1 so that log₂(e ell)≤C_0 L₀, using ell≤C ceil(A). We may take t≤ell since no repeated cells need be probed. If n<16, the lower bound t≥1 already gives t≥T_0/16. If t≥T_0/4, we are done. If w≤16 C_0² L₀, then t≥n/w≥T_0/(4C_0). We may therefore suppose n≥16, t<T_0/4 and w>16 C_0² L₀.

We use the common-union counting idea of [DLW] Theorem 5.1, with a ceiling for the number of queries and an explicit large-part condition. Let q=ceil(wt/n+1). Since wt≥n, q≤3wt/n. Also q≤(1/4) sqrt(w/L₀)+2≤k/4+2≤k because w≤kn≤k². Since k≤2^n, we have q≤(1/4) sqrt(n 2^n)+2≤2^(3n/4−1) for n≥16. Let P=binom(ell,t). Then log₂ P≤t log₂(e ell)<n/4.

For any fixed key, partition all 2^n inputs by their set of tapped locations padded to t using any deterministic rule. There are at most P parts. A largest part has size J≥2^n/P≥2^(3n/4)≥2q. For an ordered uniform list of q distinct inputs, the probability that all are in that part is (J)_q/(2^n)_q≥(1/(2P))^q, where (z)_q=z(z−1)…(z−q+1). Every such list uses at most t distinct words in total. The same probability lower bound holds after averaging over the key.

For each fixed input list X of length q, consider the set R_X of evaluation tuples realizable on some key whose evaluations on X as a whole use at most t distinct key words. This is just a support set for a mathematical probability comparison. It has size at most 2^(wt): simulate those evaluations sequentially with a read cache, branching into 2^w possibilities only when a new word is read. Prune any path that would read a (t+1)-st distinct word. The surviving completed paths are leaves of a rooted tree of depth at most t and branching factor 2^w; pad each shorter leaf if necessary to see the leaf bound. No factor counting unread addresses or decision trees is needed.

The ideal uniform evaluation vector on X lands in R_X with probability at most 2^(wt−nq)≤epsilon by the ceiling choice. Selective TV then bounds its real probability by 2epsilon, even when this inequality is averaged over the random input list. The previous large-part argument yields (2P)^(-q)≤2epsilon, and hence

    n−1 ≤ q (1+log₂ P) ≤ 3(w/n)t (C_0+1)t L₀.

This gives t≥T_0/sqrt(6(C_0+1)) because n−1≥n/2. Combined with the one-query support bound it proves the claimed lower order over n≥2.

**Endpoint n=1 (excluded above).** Here epsilon=1/2. For k=1 a constant family uses zero probes and zero random words. For k=2, a constant pair has ideal distance 3/4, so one word and one probe are necessary. They suffice for any w≥1: output the first fair bit at input 0 and zero at input 1. The entire output pair has distance exactly 1/2, which also bounds any adaptive view by data processing.

## 4. Separate structural bound on address-pattern entropy

Assume n≥2 and keep the selective guarantee with the same epsilon. For a key S, its whole address pattern is the map I_S assigning to every x the set of key word locations tapped in that evaluation. Consider a fixed pattern I with probability pi>epsilon; the conditional key law can be arbitrary. For a list X of q≤k distinct inputs set u=|∪_(x in X) I(x)|. Two keys with pattern I and the same values at these u positions produce identical output vectors: for each x, deterministic probing follows the same path when every response to a tapped position agrees. Thus the conditional output support on I has size at most 2^(wu). Under the unconditioned real law this support has mass at least pi, under uniform at most 2^(wu−nq). The selective guarantee forces

    wu ≥ nq + log₂(pi−epsilon).                         (2)

In particular, if pi≥2epsilon then every list of k distinct inputs uses at least n(k−1)/w distinct positions for this pattern. No assertion is made that every key or pattern must expand without a mass premise.

For ell≤C ceil(A), k≥2, this premise requires
t=Omega_C(min{n−log₂ k,A}). Here is a direct combinatorial proof. Put a=n(k−1)/w, so A/2≤a≤A. If a<4 then t≥1 already gives the order. Otherwise take an integer v=floor(a/2), with a/4≤v<a≤ell. For a uniformly chosen v-set of key locations, fewer than k inputs can have I(x) contained in it, by the union condition. If t>v/2 then t≥a/8≥A/16. If t≤v/2 then each x has probability at least (v/(2ell))^t of being contained: expose its at most t required indices without replacement, and each numerator is at least v−t+1≥v/2. Averaging the count of such x gives 2^n(v/(2ell))^t<k, so t>(n−log₂ k)/log₂(2ell/v). The latter denominator is bounded by a constant depending only on C. This proves the stated order.

In particular, for n≤k≤poly(n) and w≤k, any family of locality o(n) and near-optimal key size must have all whole-pattern atoms of probability less than 2^(1−n), hence pattern min-entropy greater than n−1 for large n. Static access has just one atom. If all addresses are controlled by an h-bit header, their min-entropy cannot exceed h; our catalog uses h=n+O(log k) bits in this regime. This does not imply an unrestricted stronger lower bound on t, and the ordinary locality result does not impose such a header on general evaluators.
