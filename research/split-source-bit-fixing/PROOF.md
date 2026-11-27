# A fixed family for fully adaptive split-source observations

## 1. Model and statements

All logs are base two unless written ln. Fix N,M≥1, P≥1 integer, and let U=[N]². A random oracle H assigns independent uniform values in [M] to every member of U. Source i has the whole table H and independent private coins (also independent of H). It returns (X_i,Z_i) with coordinate X_i∈[N] and a binary string of length at most σ_i. Write X=(X_1,X_2), Z=(Z_1,Z_2), σ=σ₁+σ₂, σ'=σ+2 log N. Observers output one bit from a challenge value y∈[M], the pair Z, and up to q classical oracle queries to the relevant table. Queries may adapt to y, Z, and earlier answers. The observer never receives X. Source, predictor and observer computation are unbounded subject only to the stated query condition. A predictor may read all of H and both leakages.

We say the pair is δ-unpredictable if the best predictor succeeds in guessing X_i with probability at most δ, for i=1,2 separately. For positive-probability (H,Z), let m_i(H,Z) be the maximum posterior mass of X_i given (H,Z), and let

    δ_* = max_i E[m_i(H,Z)] ≤ δ.

The equality of optimal guessing probability and E[m_i] holds by choosing a maximizer on each of the finitely many inputs (H,Z). In particular δ_*≥1/N; the family may use δ_*, a number determined by the source laws themselves, without taking a supplied upper bound δ as input. Conditional on each such (H,Z), the coordinates X_1 and X_2 are independent: the joint law of the source pairs factors given H, and conditioning each pair on its own Z_i preserves that factorization. The m_i need not be independent, and we never bound E[m_1 m_2] by δ².

A bit-fixing family assigns to each (f,z) a finite distribution over fixed subsets I⊆U with |I|≤P. The oracle sampled from that component equals f on I and is a uniformly fresh table on U minus I, independent across those cells conditional on the component and (f,z). This is a consistent P-mixture. In Real, the observer gets oracle H, leakage Z, and y=H(X). In Dec, draw H,X,Z exactly as in Real; draw the component and H* from the family at (H,Z) using fresh randomness, and give the observer oracle H*, leakage Z, and y=H*(X). Also define Real0 and Dec0 by the same experiments with independent uniform y in place of the challenge lookup. Let κ(q) be the supremum of |Pr[Real=1]−Pr[Real0=1]| over the observers just described.

**Theorem 1 (extraction).** If N≥2, for every q≥0,

    κ(q) ≤ min{1, 10 sqrt(σ'(q+1)δ)}.

**Theorem 2 (consistent decomposition).** There is one family depending only on the two source laws and P (hence allowed for every prescribed slack γ∈(0,1)), such that simultaneously for every q≥0 and every q-query observer,

    |Pr[Real=1]−Pr[Dec=1]| ≤ min{1, 3σ' q/P + 18 sqrt(σ'(q+1)δ)}.

If N=1, the family that fixes the sole cell gives distance zero for every P≥1. If M=1, all experiments agree. For other parameters, Theorem 2 is stronger than the stated c/0010 form with c=3 and C=18: increasing σ' q to (σ'+log(1/γ))(q+1), and including the extra γ, can only enlarge the upper bound. The family is not selected separately for each observer or each query budget. The theorem does not produce an oracle-specific decomposition for each source separately.

## 2. An adaptive rectangular concentration lemma

Fix a deterministic observer D and a possible leakage z. For a fixed cell u, arbitrary table H, y∈[M], and b∈{0,1}, set F_u^b(H,y) to the result of D on (y,z) with oracle H, except that if it tries to query u, stop immediately *before* returning that cell's answer and output b instead. This truncated procedure depends on the table away from u only. For a nonempty rectangle R=A×B⊆U with L=|R| set

    S_{R,z}^b(H) = Σ_{u∈R} [ F_u^b(H,H(u)) − E_{y uniform} F_u^b(H,y) ].

**Lemma.** For each fixed R,z,b and 0≤s≤1, a uniformly drawn H satisfies

    Pr[ S_{R,z}^b(H)/L ≥ s ] ≤ exp(−L s²/[8(q+1)]),

and the same inequality holds for the lower tail with −S_{R,z}^b(H)/L. No union over the range [M] is used.

*Proof.* Set p=1/[2(q+1)]. Independently mark each cell in R with probability p, and denote the marked set by T. Given T and the outside table H|_{U minus T}, for each u∈T define a function G_{T,u}^b(y) by running D until it finishes or asks for its first answer in T.

- If it finishes and outputs d, return d(1−p)^{−w}, where w is the number of distinct queried cells in R before it finishes.
- If the first query in T is at u, return b(1−p)^{−w}, where w counts distinct earlier queried cells in R before that query.
- If the first query in T is at another cell, return zero.

In particular no query in T is answered. Distinct cells rather than repeated probes enter w. For a fixed H,u,y, run the full u-truncated procedure and record the set W of distinct queried cells in R before it stops. When it stops at u, this excludes u itself, and otherwise the record also does not contain u. This run and W are deterministic when H,u,y are fixed. On masks that contain u, the masked run realizes the first or second case exactly when T∩W=∅, in which case it uses the recorded |W|. Indeed the two executions agree until the first masked query, if any. Every other mask containing u realizes the third case, including when the truncated procedure would stop later. Since u∉W, independence gives probability p(1−p)^{|W|} of u∈T and T∩W=∅. Thus, with the convention that the contribution is zero if u∉T,

    E_T [ 1[u∈T] G_{T,u}^b(y) ] = p F_u^b(H,y).                (1)

This identity holds with y=H(u) also, since H is fixed when averaging T. It permits exact reweighting without losing a factor depending on the size of the deviation or query range.

Now fix T and the outside table. For u∈T the functions G_{T,u}^b(·) are fixed. The cells H(u) are independently uniform, so the variables

    W_u = G_{T,u}^b(H(u)) − E_{y uniform} G_{T,u}^b(y)

are independent and centered. Each has range length at most (1−p)^{−q}≤2: use −ln(1−p)≤p/(1−p) and qp/(1−p)=q/(2q+1)<1/2. By (1),

    S_{R,z}^b(H) = E_T [ p^{−1} Σ_{u∈T} W_u ].

Apply convexity of exp for each H. For a centered variable V of range length at most 2, the log of E exp(tV) and its derivative vanish at t=0; its second derivative is the variance under exponential tilting, at most 1 because the law stays in an interval of length 2. Integrating gives log E exp(tV)≤t²/2. Using this bound conditional on T and the outside table and then independence, for |λ|≤p,

    E_H exp(λ S_{R,z}^b(H))
       ≤ E_T exp( λ² |T|/(2p²))
       = (1−p+p exp(λ²/(2p²)))^L
       ≤ exp(λ² L/p).

The last inequality uses 1+a≤exp(a) and exp(a)−1≤2a for a∈[0,1/2], whose range follows from |λ|≤p. Choose λ=ps/2 and apply Markov's inequality to get exp(−pLs²/4). Choosing negative λ gives the other tail. This proves the lemma.

## 3. From fixed rectangles to the actual split sources

Fix deterministic D and let ξ=N^{−2}. For each possible pair of rectangle side lengths k,l∈{1,…,N} set

    e_{k,l} = sqrt( 8(q+1) [(k+l+4) ln N + (σ+4) ln 2] /(kl) ).

There are at most N^{k+l} rectangles of those sizes and fewer than 2^(σ+2) leakage pairs, because variable-length strings are allowed. Taking both b and both signs gives at most four choices. For e_{k,l}≤1 the lemma gives total exception probability at most N^{−4} for each size pair, by substituting the threshold in its exponential. For e_{k,l}>1 the event |S_{R,z}^b(H)|/L>e_{k,l} is empty. Summing over N² size pairs, with probability at least 1−ξ over the original uniform H it therefore holds simultaneously for every such R, z and b that |S_{R,z}^b(H)|/L≤e_{k,l}. This good event is stated **before** conditioning on Z. Any dependence of leakages or rectangular supports on H is already covered by the simultaneous bound.

Fix (H,Z) on this good event and take k=⌊1/m₁⌋, l=⌊1/m₂⌋. Because the posterior point probabilities are at most 1/k and 1/l, each posterior coordinate law is a convex combination of uniform laws on supports of exactly k or l, respectively. For completeness, intersect the simplex with the constraint p_i≤1/k. Any vertex with two entries strictly between 0 and 1/k could be perturbed in opposite directions, so there is at most one such entry; the normalization 1 forces zero such entries. The vertices are precisely the uniform laws on k points. The conditional product law is thus a convex combination of uniform laws on k-by-l rectangles, with no requirement to select a rectangle independently of H.

Let B_b(H,Z) be the conditional difference

    E_X F_X^b(H,H(X)) − E_{X,y uniform} F_X^b(H,y),

where the expectations are conditional on (H,Z) and the independent y in the second is uniform. The rectangle bounds show |B_b|≤e_{k,l} on the good event. Also 1/k≤2m₁, 1/l≤2m₂, and 1/(kl)≤(1/k+1/l)/2. Since N≥2,

    [(k+l+4) ln N + (σ+4) ln 2]/(kl)
      ≤ [3 ln N + (σ+4) ln 2/2] (1/k+1/l)
      ≤ (10 ln N + σ ln 2)(m₁+m₂)
      ≤ 5 ln 2 · σ'(m₁+m₂).

On the exception event |B_b|≤1 even when Z is correlated with H. Therefore Jensen's inequality, E(m₁+m₂)≤2δ_*, and the event probability give

    E|B_b| ≤ ξ + sqrt(80 ln 2 · σ'(q+1)δ_*).                  (2)

We compare the original (not truncated) experiment with the independent challenge experiment. At every H,X,y the output of D is between F_X^0(H,y) and F_X^1(H,y). The difference of these truncations in a run is exactly the indicator that the original run makes a query to X at some point (up to that query the executions agree). Let h_ind be the probability of this event in Real0. The original difference Real−Real0 is at most E B_1 + h_ind and the reversed difference is at most −E B_0 + h_ind. Both bounds use the independent-challenge experiment for the truncation discrepancy. In particular we do not assert that the query positions in the real experiment are independent of X.

Here and below, given (H,Z), any random query set or fixed set of size at most s that is drawn conditionally independently of X obeys the **mean hit bound**

    Pr[X lies in the set]
       ≤ E min(1,s m₁m₂)
       ≤ sqrt(s) E sqrt(m₁m₂)
       ≤ sqrt(s) sqrt(E m₁ · E m₂)
       ≤ sqrt(s) δ_*.                                      (3)

The first inequality is the posterior product structure; the second uses min(1,a)≤sqrt(a), not an assertion of independent posterior maxima. In Real0 the queried set is such a set with s=q, since y is fresh uniform and observer coins are independent; hence h_ind≤sqrt(q)δ_*. Define B=sqrt(σ'(q+1)δ_*). The two terms ξ and sqrt(q)δ_* are at most B separately, since N≥2, δ_*≥1/N, σ'≥2 and δ_*≤1. The coefficient sqrt(80 ln 2) is less than 8. Thus (2) and the truncated-run comparison give the bound 10B, proving Theorem 1 for deterministic D. For randomized D condition on its independent coins and average the resulting two-sided bound; no simultaneous union over D is needed. The family to be built below is independent of D regardless.

## 4. The consistent family, fixed before the query budget

Define P₀=min(P,⌈σ'/δ_*⌉), ℓ=3σ'/P₀, and ξ=N^{−2}. We construct the family using only the source laws and P; in particular the same choices work even when γ is arbitrarily small. We first compare Real0 and Dec0, which share an independent public y.

Let the possible leakage alphabet have size L_Z≤2^(σ+2). Leakages with probability less than ξ/L_Z have total mass at most ξ. For these leakages, or impossible (H,Z) pairs, define the family with empty fixed set. For each other leakage z, conditional on z the table law has probability at most M^{−|U|}/Pr[Z=z] at each table, just because the unconditional H is uniform. Thus its deficiency ∆_z from a uniform table is at most log(L_Z/ξ). In particular

    ∆_z + log(1/ξ) ≤ σ + 2 + 4 log N ≤ 3σ'.

If ℓ≥log M, we may use the empty fixed set for this z as well: for any given y,z, the chance of a particular feasible query transcript using a≤q different addresses is at most 1 in the conditioned table and is M^{−a} under the fully uniform table. The pointwise ratio is at most M^q≤2^{ℓq}, enough for the comparison below.

For ℓ<log M, let r=log M−ℓ. For a conditional table law call the unfixed cell law r-dense if every deterministic assignment on s distinct free cells has probability at most 2^{−rs}. Perform the following disjoint partition of the positive support of H given z. While the remaining mass within this conditional law is at least ξ, work within the normalized remainder. If that distribution is r-dense choose no fixed cells and take the entire remainder. Otherwise choose an assignment on a set I of maximum cardinality among those violating the density inequality, with a deterministic tie-breaker. Remove its full fiber in the current remainder as one component. The component's free cells are r-dense: a violation on a nonempty disjoint set of free cells multiplies with the strict violation on I, giving a violation on a larger set in the remainder. If the remaining mass drops below ξ, take it as one exceptional component with no fixed cells. The process terminates because a step removes a nonempty part of finite support.

For the nonempty fixed sets chosen in this procedure, the normalized remainder has conditional mass w≥ξ and its probability of the chosen assignment is strictly more than 2^{−r|I|}. The original conditional law is pointwise at most 2^{∆_z} M^{−|U|}, and at most M^{|U|−|I|} full tables extend the assignment, so that probability is at most 2^{∆_z}M^{−|I|}/w. Consequently |I|ℓ<∆_z+log(1/ξ)≤3σ' and |I|≤P₀. This remains true in all cases with I empty.

For each (f,z) choose the component of its conditional partition containing f, and resample uniformly on the unfixed entries while preserving its assigned fixed values. That component is determined by (f,z) alone, not the selected points X. For an exceptional component or low-mass z, simply draw a fresh uniform oracle. The family is therefore consistent with f and uses ≤P₀≤P fixed cells. This is the conventional density-restoration method with the selection recorded as a deterministic function of the old table and leakage.

Fix good z and a nonexceptional partition label, and condition on the common independent challenge y and observer coins. For each feasible adaptive query transcript, the fixed cell answers are prescribed and repeated cells must give the same answers. The full path is then exactly the event of its answer assignments on the distinct free queried cells, since the observer chooses each next cell deterministically from the prefix. If there are s≤q such cells, its probability under the original conditional component is ≤2^{−rs}; in the resampled oracle it is exactly M^{−s}, because free values are independent. Hence the transcript probability ratio is ≤2^{ℓ q}. The same ratio was shown for ℓ≥log M; infeasible paths for the resampled oracle are infeasible for the original. If two probability distributions satisfy P_path≤a Q_path pointwise for a≥1, their overlap Σ min(P_path,Q_path) is ≥1/a, so TV is at most 1−1/a. This also bounds the difference after any decision computed from the transcript. Averaging over labels, y,z and observer coins gives

    |Pr[Real0=1]−Pr[Dec0=1]| ≤ 1−2^{−ℓ q}+2ξ
                              ≤ 3σ' q/P₀+2ξ.               (4)

The two exceptional contributions are the discarded leakage mass and, conditional on each other leakage, the exceptional remainder. Source points need not be included in this comparison because the independent challenge does not use them.

## 5. Returning to the genuine challenge, for all q at once

Condition on H,Z and any selected component with fixed set I (it is deterministic here, though random selection independent of X would also suffice). Draw its oracle H° and a fresh uniform challenge y, independent given this conditioning. For Dec use oracle H* equal to H° except for overwriting H°(X) by y when X∉I, and challenge H*(X). For Dec0 use oracle H°, challenge y. For each fixed (H,Z,I,X), H* still has the component's law: at the free cell X the replacement is independent uniform, and on fixed cells there is no alteration. Each experiment therefore has the correct marginal. If X∉I, both runs start with the same y, and, using common observer coins, their transcripts coincide unless Dec0 queries X. Thus

    |Pr[Dec=1]−Pr[Dec0=1]| ≤ δ_* sqrt(P₀) + δ_* sqrt(q),      (5)

by (3). In Dec0 both its fresh oracle and y are conditionally independent of X given (H,Z), so its queried set is covered by (3). There is no similar assumption on adaptive query positions in Dec after a differing answer; the coupling requires only the Dec0 path.

Combining Theorem 1 in the form 10B, (4), and (5), the desired distance is at most

    10B + 3σ' q/P₀ + 2ξ + δ_* sqrt(P₀) + δ_* sqrt(q).

Because P₀≤⌈σ'/δ_*⌉, the fixed-set term is ≤sqrt(σ'δ_*+δ_*²)≤2B. Also 2ξ≤2B and δ_* sqrt(q)≤B. The minimum in P₀ gives 3σ' q/P₀≤3σ' q/P+3qδ_*; if P exceeds the cap, this uses ⌈σ'/δ_*⌉≥σ'/δ_*, and otherwise the extra term is unnecessary. If qδ_*≤1, then qδ_*≤B, so the distance is bounded by 3σ'q/P+18B. If qδ_*>1, the proposed right side already exceeds 1. Since δ_*≤δ, this proves Theorem 2 with the explicit stated cap.

Notice why P₀ can be fixed before q: the improved set-hit estimate in (3) allows saturation around σ'/δ_* (not around sqrt(σ'/δ_*)), where the budget-dependent query term becomes qδ_*, absorbed by the square-root term in the nonvacuous regime. The estimates do not require any upper bound on M, any promise that query positions ignore y, or any per-q choice of the family.
