# An input-probe lower bound for verifying a claimed factor

A short factor certificate need not allow a verifier to read only a short part of the actual integer. This note gives unconditional probe bounds even when the actual integer is promised to be a product of two distinct equal-bit-length primes, the prover may be interactive and computationally unbounded, and reading messages or doing local computation is free.

## Model

Fix n≥3, P=2^(n−1), let S be the primes in [P,2P), and let X be the set of distinct products pq with p,q in S distinct. Write M=|S| and C=|X|=binomial(M,2), by unique factorization. The authentic input is the padded 2n-bit expansion of x∈X. The verifier can access this authentic value **only by individually addressed bit probes**, although the prover may supply an alleged full value, factors and arbitrary further messages. There is no separate trusted hash, commitment, residue, oracle for word arithmetic on x, or other side channel. Computational work, prover message lengths, and rounds are not limited by this model.

A verifier may check an externally declared prime factor or may accept and supply a claimed prime factor at the end of the interaction. Completeness γ means that for each true input the appropriate honest verifier–prover run accepts a genuine prime factor with probability at least γ. The bounds below hold for any such fixed honest strategy per input. Soundness β means that for every true input and any prover strategy the probability of accepting a nonfactor is at most β. One can instead ask to verify a complete pair: the alternatives used below share **no prime factor** with the honest input and therefore invalidate either interpretation. All probabilities over protocol coins are classical; cost is the number of distinct authentic input bits probed.

For C=Θ(2^(2n)/n²) we use only the ordinary prime number theorem. Quantities such as total message length and time to actually find a factor are not inferred from our probe count.

## Bounded-error lower bound from disjoint local alternatives

Choose an integer 1≤ell≤n−1, and partition the 2n-bit word into r=floor(2n/ell) disjoint consecutive ell-bit blocks, ignoring a short remainder. Fix one block. There are at most 2^(2n−ell) outside-block patterns, so among x∈X at most that many have no distinct y∈X identical outside that block. If x and y differ only inside the block starting at bit j, their difference is 2^j d for a nonzero integer d of absolute value less than 2^ell≤P. Any alleged common prime factor p∈S is odd and would have to divide d. Since p≥P, this is impossible.

For a true x and any block admitting such an alternative y, run the honest prover for x on the actual input y, simulating its behavior with the alleged input x and the same randomness. On all honest accepting runs at x that never query this block, the two executions have identical transcripts under the coupled coins. Thus on y a wrong factor would be accepted. This event has probability at most β by soundness. If R_x denotes the event of accepting a true factor in the honest run at x, then
```
Pr[R_x and at least one probe of this block] ≥ Pr[R_x]−β ≥ γ−β.
```
This transcript replay remains valid when probes are adaptive and messages depend on earlier replies. The cheating prover can adopt the honest x strategy independent of the unchanged parts of y. There is no need to assume one can compute the alternative efficiently.

If b_x is the number of blocks with a distinct alternative, let Q be the distinct-probe count. Summing disjoint blocks gives
```
E[Q·1_(R_x)] ≥ (γ−β) b_x.
```
On average the number of blocks without an alternative is at most r 2^(2n−ell)/C. Take ell=ceil(2 log_2 n+4 log_2 log_2 n) for large n. Markov's inequality then shows that outside a fraction O(1/(log n)²) of X, b_x≥(1−o(1))r; in particular
```
E[Q] ≥ E[Q·1_(R_x)] ≥ (γ−β)(1−o(1)) n/log_2 n.
```
The exceptional set depends only on X and the partition, not on the verifier, its proof length, or its witness-selection rule. The same calculation also bounds the conditional expected cost on acceptance. For a fixed positive completeness–soundness gap this is Ω(n/log n). It does not establish an Ω(n) bounded-error lower bound for this promise. In the stronger model where the actual value can be *any* padded 2n-bit integer, every single-bit flip invalidates the proposed odd prime factor, and the same replay argument gives (γ−β)2n probes in expectation. Those flips are not asserted to preserve the balanced-semiprime promise.

## Finite small-list bound on the number of easily verified words

For a set U⊆{0,1}^m and integers t,K with 0≤t≤m, K≥1, let B(U,t,K) contain those x∈U having a subset of at most t positions on which fixing bits to x leaves at most K possibilities in U, including x. Put V(m,t)=Σ_(i=0..t) binomial(m,i). Then
```
|B(U,t,K)| ≤ K·V(m,t).
```
To prove this, choose one such position set Q_x for each x in the bad set, and evaluate its cylinder indicator f_x(z)=Π_(j in Q_x)(z_j if x_j=1, otherwise 1−z_j) on all z in that same set. The resulting real matrix A has diagonal one and at most K nonzero entries per row. Its rank is at most V(m,t), the dimension of multilinear polynomials of degree at most t. Conversely, if d is the number of rows, tr(A)=d and its squared Frobenius norm is at most dK. Orthogonally projecting onto its column space gives |tr(A)|≤√rank(A)·||A||_F, so its rank is at least d/K. This proves the claimed bound, also when the chosen coordinate sets depend arbitrarily on x. In the singleton case K=1 it is the linear-independence bound for isolating pattern indicators.

## Applying the lemma to the semiprime promise

Split the natural bit word as x=PH+L with 0≤L<P: the low part has m_L=n−1 bits and the high part m_H=n+1. In any fiber with one part fixed, no two distinct words share a factor in S:

* With L fixed, for a candidate p, its mate is prescribed modulo P by p's invertibility modulo P, and [P,2P) contains only one integer of that residue.
* With H fixed, for a candidate p its mate lies in [PH/p,P(H+1)/p), an interval of length ≤1, so at most one integer is possible.

The candidates within any one fiber thus use pairwise disjoint unordered factor pairs, so the fiber size is ≤M/2. There are at most 2^m_H high values and at most 2^m_L low values; the counts can be reduced if some padded words do not occur.

Choose one side as the varying half of m bits and write V_fix for the number of values of the other half. For fixed t,K, at most V_fix K V(m,t) inputs across all fibers have a short pattern leaving a list of size ≤K. This is independent of which protocol is chosen. On a remaining input x, consider an accepting transcript with at most t probes in the varying half. Whatever was probed in the other half, at least K other valid inputs in x's own fiber agree with all these probes, and each invalidates both factor labels of x. For each such possible y, replay as before implies that the probability of the honest true-accept event while querying no position differing from y is at most β. Taking expectations, then summing over alternatives in the fiber F_x, proves the useful finite inequality
```
Pr_x[R_x and at most t probes in the varying half]
    ≤ (|F_x|−1) β / K ≤ (M/2) β / K.
```
This uses the same honest strategy for x throughout, and neither a single deterministic transcript nor a fixed alternative common to all coins is required. With random or adaptive proofs, each replay for an alternative y is a legitimate spoofed strategy. Applying the result to both halves permits addition of probe counts.

## Zero and exponentially small soundness

At β=0, set K=1. Choose t in each half to be floor(m/2−sqrt(3(n+1) ln n)) for sufficiently large n. The [binomial tail bound](https://doi.org/10.1080/01621459.1963.10500830) gives V(m,t)≤2^m n^(−6). Thus the overall fraction of excluded inputs across both halves is O(n^(−4)). For all other x, with probability one every honest accepting run has more than t probes in each half, giving at least
```
n − O(sqrt(n ln n))
```
distinct probes on any such accepting run. A randomized verifier can still reject early; the statement is about acceptance, or expected cost after multiplication by completeness. It holds for each protocol, including deterministic or randomized zero-soundness verifiers.

For a quantitative nonzero error bound, suppose β≤2^(−θ n) for a fixed θ>0, and put c=min(θ,1). Let h_2 be binary entropy and take its inverse on [0,1/2]. With η=n^(−1/3), for large n take K=ceil(2^((1−c+η)n)) and t=floor(m h_2^(-1)(c−2η)) in the varying half. The elementary entropy bound V(m,t)≤2^(m h_2(t/m)) shows that the excluded fraction is O(n²·2^(−η n)) across both halves (since V_fix≤2^(2n−m) and m=n±1). For every remaining input, the probability of accepting while making at most t probes in either half is at most 2·2^(−η n), by the finite inequality and M/2≤2^n. Consequently, except on that small probability of accepting too soon, an accepting run reads at least
```
[2 h_2^(-1)(min(θ,1)) − o(1)] n
```
distinct bits. In the range θ≥1 the threshold is n−o(n). This gives an explicit soundness-dependent conclusion without passing to all padded integers.

## Related work and scope

[Aaronson's randomized certificate complexity](https://arxiv.org/abs/quant-ph/0210020) and the [standard decision-tree framework](https://homepages.cwi.nl/~rdewolf/publ/other/tcs.pdf) give context for the replay and polynomial arguments. The new specialization is the arithmetic no-common-factor property in each natural block fiber, coupled with disjoint-block alternatives and a list-capacity bound that continues to work under a semiprime promise and interactive untrusted proof. The promise density uses the ordinary prime number theorem; see [Rosser–Schoenfeld](https://projecteuclid.org/download/pdf_1/euclid.ijm/1255631807) for classical prime count estimates. Proofs of proximity deliberately relax soundness on nearby words (see [sample-based proofs of proximity](https://weizmann.elsevierpure.com/files/157853487/gr_ITCS2022_SampleBasedProofsofProximity_PV2022.pdf)); the theorem instead requires rejecting wrong factors even on close valid inputs.

Reading all authentic bits trivially permits exact comparison to a supplied expansion, so the point is a locality barrier, not an impossibility of verification or a solver for the factorization search problem. No size lower bound for proof strings or bound on general factoring time is claimed. Compare the [linear-bit Lucas–Pratt certificates](FactorLinearPratt.md) and the [tagged residue-state model](FactorTaggedResidue.md), for two different resource measures.

[The finite checker](verify-factor-input-probes.js) enumerates only predetermined toy prime pools, verifies the local alternatives, checks small-list counts on both actual product fibers and abstract cubes, and checks the finite replay inequality using exact integer-weight query sets. The replay covers 1,105 local-alternative pairs, 1,007 natural fibers, 273 abstract cubes, 40,048 exact capacity checks, and 6,483 weighted replay bounds. It does not factor a supplied integer.
