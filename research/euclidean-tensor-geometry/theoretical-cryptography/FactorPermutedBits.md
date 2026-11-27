# Factor-output lower bounds for permuted bit orders

The [consecutive-block factor-output theorem](FactorStreamingBlocks.md) uses that for a fixed high or low input block, each candidate factor labels at most one adjacent semiprime. This identity fails for arbitrary digit sets. Nonetheless, there is a linear workspace lower bound for **every** balanced fixed split with deferred output, and a new linear bound with write-only online output for a uniformly random fixed bit permutation. No ordinary random-access factoring lower bound is claimed.

## Model and conclusions

Let n≥3, P=2^(n−1), and S be a pool of M≥2 n-bit primes. An input is the padded 2n-bit representation of N=pq for a uniform unordered pair of distinct primes in S. A balanced split divides the 2n input positions into two views A,B of n positions each. In each pass the machine visits one full view and then the other, in a prescribed order; a fixed permutation of all 2n bits gives this setup by making the cut after n positions. In multiple passes the same two views are used, with predetermined visit orders. Allow unlimited computation on the current view and at most 2^s states at every handoff. The output is append-only and uncharged, but its length or timing is not available as additional persistent memory. Success means outputting the n bits of either p or q, in a predetermined output bit order. Randomness is permitted.

For the full pool of n-bit primes, the following hold for any fixed target success at least δ>0 over the input and the machine's coins.

* For **every** balanced split, producing the full factor at the receiving view in a one-way conversation requires s≥n/2−O_δ(log n), even if the receiver can freely access all n retained bits. For online one-pass output, a more precise deterministic bound depends on the split imbalance, as described below.
* Draw a uniform permutation independently of the input and then fix it. With probability 1−o(1) over that drawing, **every** one-pass machine of constant success, even one specialized to that permutation and writing output online, needs s≥n/2−o(n). If output is wholly deferred to the receiving view the stronger lower bound is 3n/4−o(n).
* For that same high-probability set of permutations, if r=o(n) passes use those two fixed views, arbitrary interleaved write-only factor output needs (2r−1)s≥n/4−o(n). In particular rs=Ω(n). These results do not apply to input-dependent permutation choices or to a model with free random access.

## Deterministic graph bounds

Valid products are the edges of a simple bipartite graph of views; each edge has the two prime factors as labels. The degree of a label at a view is the number of incident edges carrying that label. Split the original padded word into the natural low block L of n−1 bits and the natural high block H of n+1 bits, regardless of the order in which positions are supplied. For any fixed prime p, the map q ↦ pq, for q∈S excluding p, is injective on either natural block separately. The low-block injectivity follows because p is invertible modulo P and the candidate q lie in an interval of length P. The high-block intervals for the candidate q have length P/p≤1.

In view A, let u and v be the numbers of *unobserved* positions from the natural low block and natural high block. Then u+v=n and its local label degrees are at most D_A=2^min(u,v), since the observed natural low coordinates alone leave at most 2^u candidate q and the natural high ones alone leave at most 2^v. Similarly D_B=2^min(n−1−u,n+1−v) works for B. In particular both are ≤2^floor(n/2). There are at most V_A=2^n possibilities for A and V_B=2^n for B.

Here are finite counting formulas that also hold when a fraction ε of the input edges is discarded and D_A,D_B are any degree bounds on the remaining edges at their respective views. Set C=binomial(M,2). Let W_k be the largest number of n-bit candidate factors agreeing on the first k positions of the prescribed output order; always W_k≤2^(n−k). A one-pass machine visiting A and then B has
```
Pr(success with deferred output) ≤ ε + V_B·2^s D_B/C;
Pr(success with online output) ≤ ε + [V_A D_A W_k +
                                      V_B D_B·2^s(2^k−1)]/C.
```
For deferred output, each chosen state and view B determines a single output label. For online output, if at least k bits are written in the first visit, each first view admits at most W_k candidate labels. Otherwise there are fewer than 2^k possible earlier strings and at most 2^s states per second view. Each allowed factor label at a view costs at most its degree in good edges. The proof fixes the random tapes before counting and then averages, as in the preceding note.

For r passes, fix the state transcript and the vector of lengths of the 2r written pieces. If side A writes a bits in total, the count is at most
```
min(V_A D_A·2^(n−a), V_B D_B·2^a).
```
Indeed, a fixed view and its pieces constrain that many candidate labels, each of degree at most the corresponding D. With 2^((2r−1)s) transcript choices, and binomial(n+2r−1,2r−1) schedules, we obtain
```
Pr(success) ≤ ε + 2^((2r−1)s) binomial(n+2r−1,2r−1)
                  max(V_A D_A,V_B D_B) 2^floor(n/2)/C.
```
A weighted sum over possible a gives a sharper finite bound, if needed.

The prime number theorem gives C=Θ(2^(2n)/n²). With ε=0 and D_B≤2^floor(n/2), the deferred one-way result holds for every balanced split. More specifically, for the deterministic D_A,D_B above, taking k≈log_2 D_A+2 log_2 n plus a δ-dependent constant in the online bound yields
```
s ≥ n − log_2 D_A − log_2 D_B − 4 log_2 n − O_δ(1).
```
This remains linear for splits with a linear imbalance in how many high and low positions fall in A. It does not force a linear online bound at the most evenly interleaved deterministic splits. Indeed, the consecutive-view **capacity-one premise** is false for some interleaved views: on 10 padded bits, 323=17·19 and 391=17·23 differ only at bit positions 2,6,7 (index 0 is least significant). Any five-bit view avoiding those positions has two edges with label 17. This is not a counterexample to a memory lower bound.

## Entropy-sampling lemma, including a pointwise tail

Let X be uniform on a nonempty set U⊆{0,1}^w, and independently let J be a uniform k-subset of its coordinates. Write all logarithms in base two except inside ordinary exponentials. For any T≥1 and t>0,
```
Pr[−log_2 Pr(X_J=x_J | J) at x=X < (k/w) log_2|U| − 2t]
 ≤ w·2^(1−T) + exp(−2t²/(w T²)) + 2^(−t).
```
This finite statement is uniform in U and k. A sample of size zero satisfies the inequality trivially.

For x in the support put q_i(x)=−log_2 Pr(X_i=x_i | X_<i=x_<i). Their sum is exactly log_2|U| for every such x. Conditional on each past, at most two one-bit outcomes have probabilities below 2^(−T); consequently Pr(max_i q_i(X)>T)≤w·2^(1−T). For each remaining x, [Hoeffding's sampling-without-replacement bound](https://doi.org/10.1080/01621459.1963.10500830) applied to the population of its w values q_i(x) gives
```
Σ_(i∈J) q_i(x) ≥ (k/w) log_2|U| − t
```
except with probability at most exp(−2t²/(k T²)) over J, which is no larger than the displayed bound with w.

To compare sampled full-prefix surprises to true projected probabilities, fix J. Define a hybrid distribution Q on the whole word by drawing each coordinate in order. At i∈J use the conditional law from the original source given only the earlier coordinates in J; at i∉J use its conditional law given the whole previously drawn prefix. Arbitrary rules at zero-probability histories make Q a probability distribution. On the support of the original law P,
```
Q(x)/P(x) = Pr(X_J=x_J)·2^(Σ_(i∈J) q_i(x)).
```
The expectation under P of this ratio is at most one, because its support sum is no greater than the total mass of Q. Markov therefore bounds by 2^(−t) the probability that the sample's actual surprise falls more than t below the sampled prefix surprise. Combining these three exceptional events proves the pointwise tail. The idea is classical min-entropy sampling; see [Vadhan's original work](https://iacr.org/archive/crypto2003/27290061/27290061.pdf). This proof is included to track fibers under the original, unsmoothed uniform distribution.

## Typical degree bound for a random fixed split

Let A be a uniform set of n observed positions, and choose the ordered prime pair uniformly so the first label p is distinguished. Condition on p, the set of observed natural low positions, their values, and the number of observed natural high positions. The surviving mates form a set R and the original mate q is uniform on R. If u low positions are unobserved, the low injectivity gives |R|≤2^u. The natural high words of mates in R are distinct, so they form a uniform set U⊆{0,1}^(n+1) of the same size. Conditional on the above data, the observed high positions are a uniform set J of k=(n+1)−v positions, independent of q, where v=n−u is the unobserved high count.

The full local degree d_A(p,N) of this label and view is the number of mates in R having the observed high projection. Therefore
```
d_A(p,N) / |R| = Pr(X_J=x_J | J) at the actual high word.
```
By the sampling lemma, except on its stated exceptional event,
```
log_2 d_A(p,N) ≤ (v/(n+1)) log_2|R| + 2t
               ≤ uv/(n+1) + 2t ≤ n/4 + 2t.
```
The product bound uses u+v=n; there is no need to treat the split counts as concentrated. Take w=n+1, T=6 log_2 w and t=w^(2/3). The exceptional probability is O(n^(−5)). By symmetry there is the same bound for the other factor and for the complementary view. Averaging over A, the expected fraction of edges on which any of the four degree bounds fails is O(n^(−5)). Markov shows that all but O(n^(−3)) of masks have failure fraction at most n^(−2). Delete those exceptional edges. Remaining label degrees at both sides are bounded by D=2^(n/4+2(n+1)^(2/3)): if one of its surviving incident edges has that label, the original local degree at that edge was already ≤D.

The finite counting bounds can now be applied simultaneously to every protocol for that mask, since no bad-edge selection depends on the protocol. Taking k≈log_2 D+2 log_2 n plus a δ-dependent constant gives the asserted n/2−o(n) for online one-pass. Deferred output removes the early-string cost, giving 3n/4−o(n). For r=o(n), log_2 binomial(n+2r−1,2r−1)=o(n), which gives the multipass result. Typical here is high probability over a uniformly drawn permutation fixed once, not high probability over the algorithm's runtime.

## A limit of the structural argument

The exponent n/4 cannot in general be improved from injectivity of the two natural projections alone. For the abstract code {(x,x): x∈{0,1}^n}, both projections are injective. Given n random observed positions, the unobserved free coordinates are exactly those whose two copies are both hidden. Their number Z has E[Z]=n(n−1)/(2(2n−1))=n/4+O(1) and Var(Z)=O(n), since distinct indicators have nonpositive covariance under sampling without replacement. For every codeword the fiber size is exactly 2^Z. Thus it is 2^(n/4+o(n)) with probability 1−o(1). One can duplicate only n−1 free positions and pad the high word by two constants for an example of the actual widths. This explains a limitation of the proof, not of semiprimes specifically.

## Prior art and exact checks

[Ablayev–Karpinski](https://eccc.weizmann.ac.il/eccc-reports/1998/TR98-011/) give arbitrary-order read-once branching-program results for integer **multiplication**, which is a different direction and output. [Bourgain's work on prescribed binary digits of primes](https://arxiv.org/abs/1307.0398) addresses prime counts with a small prescribed fraction of digits, not these conditional product fibers. The results here instead use two deterministic injective projections and an entropy-sampling argument. There is no claim to have obtained a maximal degree bound uniformly over all interleaved masks, a lower bound for general classical factoring, or a computational factoring method.

[Exact toy checks](verify-factor-permuted-bits.js) verify the two-view counterexample, deterministic degree bounds on small generated semiprimes, the prefix-surprise likelihood identity on finite uniform supports, and the duplicated-code occupancy calculations. The replay covers 4,678 balanced cuts, 579,380 degree increments, 2,400 hybrid-distribution checks, and 17,574 duplication masks. The asymptotic conclusions follow from the proof above, not the checks.
