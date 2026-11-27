# Exact worst-case bound

## 1. Definitions and statement

Fix a finite public-coin interactive proof and a statement x. Round i consists of a prover message followed by a fresh uniform verifier challenge. The full transcript after the r-th challenge determines acceptance. When a convention permits a final prover-only message with no fresh coins, assume the usual terminal consistency clause that a doomed post-challenge prefix rejects for *every* final message. Equivalently use the terminal predicate that accepts that prefix if any final message would be accepted. The counterexample below has no extra prover-only message. We count random verifier challenges, as in the sum-check source. All prover messages of a repeated round are fixed before that round's verifier challenges are sampled. The challenges in distinct copies are independent given their respective histories and current messages.

A round-by-round (RBR) certificate consists of doomed transcript prefixes, taken at challenge boundaries, such that on every NO input the root is doomed; all doomed terminal prefixes reject; and from any doomed prefix, for each choice of next prover message, the conditional probability of a non-doomed successor in round i is at most p_i. This is Definition 3 in [BDGIKT], allowing a possibly heterogeneous profile. It requires a guarantee on every fixed prefix and message, not just the actual prover strategy. The error of a certificate is its worst single transition probability, and the optimal error is its minimum over legitimate certificates. For an m-fold repetition, use independent challenges and accept if every constituent verifier accepts. There is no restriction to independent prover strategies.

Let B_i(a,b) be the probability that at least a−b+1 out of a independent Bernoulli(p_i) trials succeed, for integers 1 ≤ b ≤ a ≤ m. Set
```
   M(m; p_1,…,p_r)
      = min_{m=a_0 ≥ a_1 ≥ … ≥ a_r=1} max_{i=1,…,r} B_i(a_(i−1),a_i).   (1)
```
Then every base proof with the stated profile admits a repeated certificate of error at most M. For dyadic p_i, there is a perfectly complete public-coin verifier (possibly with high ordinary soundness for profiles close to 1) whose exact repeated RBR error is M and whose exact base RBR error is max_i p_i. Thus (1) is the exact universal envelope. For real p_i interpreted only as upper bounds on finite uniform-bit protocols, the supremum is also M, by approximating p_i from below by dyadic rationals: finite minima and maxima of polynomial tails are continuous.

All integers in (1) are positive, m,r ≥ 1. The formula includes p_i=0 or 1. For exact rational inputs an O(r m²)-entry dynamic program uses terminal values U_r(a)=0 for a ≥ 1 and the recurrence
```
   U_(i−1)(a) = min_{1 ≤ b ≤ a} max{B_i(a,b), U_i(b)},   M=U_0(m).  (2)
```
The tails themselves can be computed by elementary binomial recurrences; the count O(r m²) refers to table transitions after tails are tabulated, not bit complexity with arbitrary real inputs.

## 2. Universal certificate

For a NO input, call a coordinate surviving at boundary i if its projected base transcript has been doomed at each boundary 0,…,i. Stop counting a coordinate forever at its first non-doomed boundary, even if its base label later changes back. Let K_i be the number of surviving coordinates. Choose a profile in (1); declare a repeated prefix doomed at boundary i exactly when K_i ≥ a_i. On YES inputs set all labels non-doomed. This is allowed by Definition 3; no efficient recognition of the language or the certificate is required.

The root on a NO input has K_0=m. At termination a repeated doomed prefix has K_r ≥ 1, so at least one terminal constituent is doomed and rejects; thus all-accept fails. It remains to bound each transition. Fix the input, a repeated doomed prefix and the arbitrary vector of current prover messages. A surviving coordinate j has probability q_j≤p_i of leaving the base doomed set. After conditioning on the vector of messages, the indicator depends only on j's fresh challenge. The indicator family is independent conditional on precisely these data, even when a joint strategy chose the messages from all previous transcripts. Couple all indicators to independent uniform variables: one with threshold q_j for the actual exit indicator and one with threshold p_i for a dominating exit indicator. If K_(i−1)=a≥a_(i−1), the resulting survivor count stochastically dominates Bin(a,1−p_i), hence also Bin(a_(i−1),1−p_i) by keeping only the first a_(i−1) independent trials. The event of leaving the repeated doomed set is K_i<a_i, of probability at most B_i(a_(i−1),a_i). This proves (1). An independent private choice of prover messages can be averaged after this pointwise bound; there is no look-ahead within a vector round. Coordinating verifier challenges or changing the terminal aggregation rule are different models.

## 3. Attainment and optimality without any restriction on certificates

For dyadic p_i=d_i/2^b_i, take the language of bitstrings beginning with 1. In each of the r rounds the prover has a dummy message (or ignore arbitrary fixed-length content); the verifier publishes an independent uniformly random b_i-bit word. Call it an event if the integer word is below d_i. Ignore messages. On YES inputs accept always. On NO inputs accept at termination precisely if at least one event occurred. The base certificate “no event yet” on NO inputs gives profile p_i exactly whenever the prefix is reachable and still has no event. If some p_i=1 no finite nontrivial RBR bound is possible: the accepting transcript can become certain, and reasoning below or the first such transition gives value 1. Otherwise every no-event history still has positive probability. The exact one-copy value follows from the argument below, or from (1) with m=1. Ordinary soundness is 1−∏_i(1−p_i). For the counterexamples in Section 4 it is at most 1/3, so this is also a conventional bounded-error proof system. If an arbitrary profile gives ordinary error arbitrarily near 1, the universal envelope is stated over verifiers in Definition 3 without also prescribing a separate ordinary error cap. There is no claim of attaining every high-error profile within a class with a given smaller ordinary error. In particular, profiles with ∏_i(1−p_i)≥2/3 satisfy that cap.

At a repeated prefix in this model let a be the number of coordinates with no event yet. Their successor count is exactly Bin(a,1−p_i) given the entire prefix, not just in an unconditional average. At a terminal prefix rejection is equivalent to a≥1.

For a proposed error e<1, determine the **maximal admissible doomed set** backwards on the complete finite transcript tree. At the end include every rejecting terminal. At each earlier layer include a prefix exactly when for **each** permitted prover message the total probability of excluded successor prefixes is ≤e. This gives a legitimate local labeling whether or not the root belongs. It contains every possible certificate by backwards induction: all admissible doomed terminals reject, and being contained in the next maximal doomed set can only increase a candidate child's escape probability. If the root is absent, no valid certificate of error e exists. This argument is about arbitrary prefix labels, not a symmetry assumption.

In our experiment the maximal set can be computed solely from the count. Starting from threshold t_r=1, if the next maximal set is a≥t_i, the required escape probability at count a is Pr[Bin(a,1−p_i)<t_i]. This is nonincreasing in a by coupling, so the preceding maximal set is again a threshold (empty if none qualify). It depends on no other component of the history. One can define these thresholds on the virtual state space {0,…,m} at every layer, even for counts not realized by an actual transcript; then restrict to each reachable history. The recursion agrees because all positive-probability children of a reachable history are reachable. For e<1, a<t_i always leaves that next threshold, since counts cannot increase. Thus finite thresholds are nonincreasing in time, and t_0≤m is necessary and sufficient for existence. If it holds, use a_0=m and a_i=t_i for i>0. These satisfy (1) with all costs ≤e, since the first count m is at least t_0. Conversely a profile with all costs ≤e is a certificate by Section 2. Hence the exact optimum equals (1). At e=1 use any root-and-terminal consistent labeling, including the root and all rejecting terminals; acceptance histories can never become doomed at termination. Formula (1) is always at most 1, so this closes the endpoint.

## 4. Relation to Remark 3

[BDGIKT], Remark 3, proposes that m=kr copies suffice for repeated RBR error at most p^k whenever a base r-round proof has RBR error p. The following examples have r=2 independent challenge rounds and perfect completeness, so the usual all-accept convention applies. If a fixed terminal aggregation rule also accepts on the vector of all-accept outputs, its terminal rejecting set is only smaller, and cannot yield a smaller optimal RBR error in these examples. We do not claim anything about arbitrary redesigned verifiers.

For r=2 with p_1=p_2=p, the exact value is
```
   M(m;p,p) = min_{1≤a≤m} max{p^a, Pr[Bin(m,1−p)<a]}.                (3)
```
For p=1/8 and m=6, a=3 gives the maximum 778/8^6 = 389/131072, as the first-round contribution is (15·49+6·7+1)/8^6 and the second is 512/8^6. For a≤2 the second-round quantity is at least 1/64, larger than this value. For a≥3 the first-round quantity is at least its value at a=3. This proves optimality and 389/131072 > (1/8)^3. The base ordinary soundness is 1−(7/8)^2=15/64.

The uniform inequality also fails when p vanishes. Suppose p=2^(−L), k=2L and L≥3. To have repeated error ≤p^k, (3) requires a≥k from the second term. The first term is then at least
```
   Pr[Bin(2k,p)=k+1] = C(2k,k+1) · p^(k+1) · (1−p)^(k−1).
```
The middle binomial coefficient is at least 4^k/(2k+1) by averaging, and C(2k,k+1) ≥ C(2k,k)/2. Thus the ratio of this lower bound to p^k is at least p · (4(1−p))^k/[2(2k+1)], which is at least (9/2)^L/[2(4L+1)] > 1 for L≥3. The last inequality holds at L=3 and its left side increases with L. The base ordinary error is ≤2p≤1/4. Challenge lengths L and repetition k=2L both grow linearly.

There is no contradiction with a fixed-parameter small-p interpretation. Indeed every profile of cutoffs in (1) has at least one budget d_i=a_(i−1)−a_i+1≤ceil(m/r), since the sum of budgets is m−1+r. For constant p on all rounds, the binomial tail in that round is at least p^d_i, by specifying any d_i fixed successes. Conversely choose integers d_i differing by at most one with the same sum; each is at least ceil(m/r) and the corresponding threshold sequence ends at 1. A union bound over d_i-subsets then gives
```
   p^ceil(m/r) ≤ M(m;p,…,p) ≤ min(1, 2^m · p^ceil(m/r)).              (4)
```
If m=kr and r≥2, take a_i=(r−i)k for i<r and a_r=1. The first r−1 rounds need at least k+1 losses to leave the certificate; the last needs k. Those tails are at most C(kr,k+1)p^(k+1) and exactly p^k, respectively. In particular M=p^k whenever p≤1/C(kr,k+1). For r=1 equality holds always. The conjectured power as p→0 with fixed r,k is therefore not refuted. What fails is the uniform exact bound for all parameters, as written.

## 5. Exact limiting rate for two rounds

Use natural logarithms, put q=1−p with 0<p<1, and write I(x||q)=x ln(x/q)+(1−x)ln((1−x)/(1−q)) with continuous endpoint conventions. Define I_-(x)=I(x||q) for x≤q and 0 for x≥q. Then
```
   lim_{m→∞} [−ln M(m;p,p)]/m
      = max_{0≤x≤1} min{x ln(1/p), I_-(x)}.                          (5)
```
To derive (5), take a_m/m→x along any sequence of allowed thresholds. For fixed q the logarithmic rate of Pr[Bin(m,q)≤a_m−1] is I_-(x). One elementary proof bounds each binomial point mass at j both above by exp(−m I(j/m||q)) and below by (m+1)^−1 times that quantity. The bounds follow by expressing the point mass as exp(−m I) times its probability in Bin(m,j/m), where j is a mode and its mass lies between 1/(m+1) and 1. The largest-mass exponent over the tail is the minimum of I on its allowable grid; replacing a sum of ≤m+1 terms by its largest term incurs at most ln(m+1)/m. This minimum converges to I_-(x), including x=0 and x=q. In (3), the negative logarithm of the maximum becomes the minimum of rates. Any target x is approximable by allowed thresholds; conversely any sequence of optimal thresholds admits a subsequence with convergent a_m/m. These facts prove the limit.

The increasing line x ln(1/p) and strictly decreasing I(x||q) have a unique intersection x_* in (0,q). This intersection maximizes (5). Moreover x_*<1/2: if q≤1/2 it is immediate; if q>1/2, I(1/2||q)=−(1/2)ln(4p(1−p))<(1/2)ln(1/p). Therefore (5) is strictly smaller than (1/2)ln(1/p) for every fixed p∈(0,1). Along m=2k the ratio M(2k;p,p)/p^k grows exponentially in k. For instance one can choose p=1/8, which is compatible with ordinary soundness at most 1/3. Thus not even a uniform multiplicative constant independent of k repairs the proposed inequality at fixed p. This limit is for the worst-case envelope, not for every base protocol.

## References

The source-to-theorem mapping, round-count convention, and distinction from published count-based bounds are in SOURCES.md.
