# Coordinatewise increasing objectives and fixed real marginals

For fixed real-valued marginal laws on a finite product, let the benchmark be the supremum of E f(X) across all couplings, for any nonnegative Borel coordinatewise nondecreasing f. If couplings are restricted to be positively upper orthant dependent (PUOD), the supremum is at least three quarters of this benchmark. This is sharp, already for two Bernoulli coordinates and the union indicator. Equivalently one can take two uniform [0,1] marginals and the indicator that one is larger than 1/2: countermonotone uniforms have union probability one, while independent uniforms attain the maximum 3/4 under the constraint. No attainment assumption on the unrestricted supremum is needed.

**Proof.** Start with any given coupling X. Write X_i=Q_i(1−R_i) almost surely with uniform (not necessarily independent) upper-tail ranks R_i and marginal quantile functions Q_i. This representation allows atoms: for marginal CDF H_i and an independent uniform W_i, take 1−R_i=H_i(X_i−)+W_i[H_i(X_i)−H_i(X_i−)]. This is uniform by the randomized distributional transform (within the quantile interval belonging to an atom it is uniform, elsewhere there is no interval); the left-continuous generalized inverse Q_i recovers X_i almost surely. Let a=3/4, draw U uniform independently of X and the rank randomizers, and simultaneously set
```
       R'_i = min(R_i, U/(1−a+U))  if U≤a;      R'_i=U  otherwise.
```
For a threshold 0≤q<a, the event R'_i≤q occurs if either R_i≤q and U≤a, or R_i>q and U≤(1−a)q/(1−q). For a threshold q≥a, R'_i≤q is just U≤q (up to null endpoint conventions). These are exactly the high/low threshold rules of the finite theorem applied to the indicators of R_i≤q, of marginal q. In particular the new ranks are individually uniform. At an arbitrary vector of thresholds q_i, apply the finite rule to the input events R_i≤q_i, using the same U for all of them. For every J,
```
 P(R'_i≤q_i for every i∈J) ≥ ∏_{i∈J} q_i .
```
Now Y_i=Q_i(1−R'_i) has the original marginal; Y_i>t_i is equivalent up to null differences to R'_i≤1−H_i(t_i). This proves the required upper-orthant inequalities for all real thresholds. On U≤a, all R'_i≤R_i, so all Y_i≥X_i. The event is independent of the original X, giving E f(Y)≥a E f(X), including extended expectations by monotone truncation. Taking suprema completes the proof.

This is only upper-orthant dependence: simultaneous lower-orthant conditions cannot be added with this constant. As in the finite theorem, for n equally likely singleton marginals of size 1/n, the simultaneous lower-orthant bound alone forces P(Y nonempty)≤1−(1−1/n)^n. The fixed-marginal literature already studies optimization with these dependence restrictions; the assertion above is the sharp uniform multiplicative comparison, not an algorithm for computing a particular optimum.
