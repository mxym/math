# Noiseless simulation and exact endpoint

Use the notation in PROOF.md. For every noise level and expected budget t, a comparison with singleton equality queries gives
    
    I(J;H_τ) ≤ min{log n, (t/c)log n},    c=(n−1)(n+2)/(2n).           (E1)

At Δ=1 this bound is attained at every real t≥0. The exact endpoint is a separate elementary decision-tree calculation, not an exact constant claim at positive noise. In particular I≤2(1+log n)t/n also follows from the proof below without optimizing.

First fix the bounded truncation T=τ∧m. A noiseless oracle for i returns 1_{J=i}. To generate a reward with the prescribed law, flip each response independently with probability (1−Δ)/2, using private independent randomness. The original policy sees only the simulated noisy rewards and the original policy seed. Consequently its joint law with J and its distribution of numbers of probes are the prescribed ones, including repeats and the stopping decision. Give the analyst both all independent seeds and the genuine noiseless responses. This can only increase information. The following argument is performed conditionally on those seeds, so that the noiseless decision tree, including the stopping rule at m, is deterministic; the marginal distribution of J remains uniform.

Consider its all-zero-answer branch, defined as a formal branch even if impossible under the planted prior after n distinct probes. Let d be the number of distinct labels along that branch, in their order of first occurrence. If J is the jth such label, its path coincides with the all-null branch up to the jth distinct probe and receives a first positive response there. The transcript then determines J. If J is outside the list the entire transcript has the same all-zero value. Thus the conditional mutual information is
    
    H_d=(d/n)log n−(1−d/n)log(1−d/n),

with 0 log 0=0, also valid at d=0. Because each first occurrence takes at least j actual probes, and the formal all-null branch has length at least d, the conditional mean cost C satisfies
    
    C ≥ c_d := (1/n)∑_{j=1}^d j + (1−d/n)d = d−d(d−1)/(2n).

This lower bound is exact for visiting d distinct labels without repeats, stopping on the first hit or after d failures. Since −(1−x)log(1−x)≤x and c_d≥d/2, this already gives I≤2(1+log n) E[T]/n.

For the sharper statement, H_0=c_0=0. When augmenting the no-repeat search from d−1 labels to d, the query takes place only on the still-unresolved branch, of mass (n−d+1)/n. On that branch it splits off one of n−d+1 equiprobable labels. Hence
    
    (H_d−H_{d−1})/(c_d−c_{d−1}) = h(1/(n−d+1)),

where h(x)=−x log x−(1−x)log(1−x). For d≤n−1 these successive slopes are nondecreasing since 1/(n−d+1)≤1/2. Their positive-weight prefix averages H_d/c_d therefore have maximum at d=n−1. At d=n the gain in H is zero and the cost rises (from d=n−1 the one remaining label was already known); thus H_d≤c_d(log n)/c_{n−1} for all d. As c_{n−1}=c, fixing seeds, then averaging (seeds independent of J), yields I(J;H_T)≤(log n)E[T]/c as well as I≤log n. The limit argument in PROOF.md gives (E1) under arbitrary stopping.

At Δ=1, querying n−1 distinct labels until a first hit or exhaustion determines the secret and costs c in expectation. With independent probability min(1,t/c) run this strategy, otherwise make no queries. The choice is visible, since the strategy for n≥2 always makes at least one query. Therefore this algorithm attains the right hand side of (E1), including nonintegral t, t=0 and the plateau. No sharpness at Δ<1 is inferred. Full noiseless sequential search and its cost are classical; this calculation identifies the expected-budget information envelope within this restricted query model.
