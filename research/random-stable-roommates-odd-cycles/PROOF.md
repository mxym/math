# Odd-cycle participants in random stable roommates

Take even n participants, independent uniform strict complete rankings of the other n−1 people, and rank oneself last (a possible unmatched singleton). In Tan's stable permutations the collection of directed odd cycles is the same for the entire instance, up to the uniform choice of orientation convention. Let X be the number of vertices in these cycles, including the possible singleton, and let U mean that no stable perfect matching exists. Mertens, *Random stable matchings* (2005), §3.1, Conjecture 2, predicts E[X | U] of order √(n/log n).

**Theorem.** With R standard Rayleigh (density x exp(−x²/2) on x>0) and B independent Beta(1/2,1/2), X/√n converges in distribution and in each positive integer moment to RB. This remains true conditionally on U. In particular E[X | U] ~ √(π/8) √n, so the order in Conjecture 2 fails. The solvability estimate itself is not new and no speed of convergence is asserted.

## 1. An instance identity, not size-biasing by stable partitions

Use the predecessor-better orientation of Mertens and Young–Studebaker (YS, arXiv:2610.07741v1): the successor is the worse neighbor, and no two people prefer each other to their respective successors. Let L(π) count even cycles of length ≥4. For a fixed instance without invariant singletons, and any function f of the odd cycles,
  sum_{stable π} (−1)^L(π) f(odd(π)) = f(odd(I)).                   (1)
This is the odd-pattern form of Mertens's cancellation (2015, Prop. 3.2 and Cor. 3.3); we justify the application separately. Tan gives existence and invariance of the odd cycles O, and each even cycle of length ≥4 can be split in either alternating way into transpositions, preserving stability. Fix O and let V be the remaining vertices. For i in V mark each w in O that prefers i to its successor. For i call a partner j in V eligible from i if i ranks j above **every** such w; call a pair acceptable if eligible from both sides. In a stable extension of O the worse partner of each i, hence also its better partner, must clear that cutoff. Resolving its even cycles gives a perfect acceptable matching M₀ on V. Put all acceptable partners first (in their original relative order), and append the other partners in any strict order. This defines a complete residual roommates instance. M₀ is stable in it: every pair that was acceptable has the old comparisons, and no unacceptable partner can improve upon M₀ in the new lists. This is the odd-core restriction of Glitzner–Manlove, with an explicit completion to use the complete-list signed identity.

Every stable perfect matching N of the completed instance uses only acceptable pairs. On any nontrivial alternating cycle of M₀ and N, every M₀ edge has an endpoint preferring N (else it blocks N), and every N edge has an endpoint preferring M₀. Since every vertex has exactly one of these preferences, counting endpoints on this cycle forces equality on every edge. If both endpoints of an N edge deem it unacceptable in the completed lists (by symmetric deletion), both prefer M₀, a contradiction. Common edges are already acceptable. Every stable all-even permutation of the completed instance likewise uses only acceptable cycle edges: each edge is used in some stable perfect matching obtained by splitting the even cycles. Conversely, the all-even permutations stable in the completed lists are precisely the restrictions of original stable permutations with O. Indeed all their cyclic partners clear the original cutoffs, O has no internal blocking pair, and no mixed pair can block. An unacceptable residual pair cannot block in the original: at least one side fails its original cutoff and so ranks its own acceptable successor above that partner. All other needed comparisons are unchanged. The converse follows from the same tests for an original stable extension after tail completion. For V empty use the unique empty residual permutation. The instancewise all-even signed identity of YS Appendix A (the all-even sum is 1 on a solvable instance) now gives (1); f can be factored out because O is invariant. This step precludes inadvertently weighting an instance by its number of reduced partitions.

If a singleton is present, invariance implies there is no fixed-point-free stable permutation. Thus summing over only fixed-point-free permutations in (1) gives f(O) times the indicator of no singleton, for every instance. We bound the exceptional contribution separately.

## 2. Marked permutations and a common integral

Use independent uniform [0,1] scores for each ordered pair, smaller is better. On a fixed-point-free permutation let A be the vertices on cycles ≥3, m=|A|, B₀ the matching on the complement, H the simple graph of the long-cycle edges and D=B₀∪H. The stability probability is
  p_H=∫_[0,1]^n (∏_{i∈A}x_i) ∏_{{i,j}∉D}(1−x_ix_j) dx.
Indeed condition on all successor scores x_i: a distinct predecessor must have score below x_i; on every pair outside D one must exclude simultaneous improvement. All relevant ordered-pair scores are disjoint. In even n, m is even. Write J=J_{n,m}=1/(n+m−1)!!.

Here are the uniform kernel estimates used below, with their dependence on the YS results explicit: p_H≤CJ for all m. For even m≤√n log n there is a number b_{n,m} the same for all these labeled types, such that
  |p_H−b_{n,m}|/J ≤ C(m² log⁸ n/n² + exp(−c log² n)),
  b_{n,m}/J=e^{1/2}+o(1) uniformly.                                 (2)
The first global bound is YS Lemma 3.1 (any excluded graph of maximum degree two). YS Prop. 4.1 is *stated* for unions of even long cycles. To extend it to odd long cycles, use exactly the same matching-only kernel W=(∏_A x_i)∏_{{i,j}∉B₀}(1−x_ix_j), and the same symmetric good region G in their (3.1). On G each x_i≤2 log² n/√n and one restores H by the factor 1+∑_{ij∈H}x_ix_j+O(m² log⁸ n/n²), via the logarithmic product expansion since m max x_i²=o(1). The integrated linear term equals m times the contribution of any two distinct vertices in A by permutation symmetry, as H has m edges. Outside G, YS Lemmas 3.1–3.2 apply directly to D of maximum degree two. Thus it is literally their matching-only b of (4.3), whose uniform estimate follows from their Prop. 4.2 and does not mention H at all. Empty or unrealizable m cause no difficulty (m=2 has zero coefficient). These estimates are a prior analytic ingredient, not a new calculation of solvability.

Fix integer r≥1. On m labeled long vertices write c_m for 1/m! times the signed number of permutations into cycles ≥3, each weighted by the r-th power of the total odd-cycle length. The corresponding sum with all signs made positive is at most m^r: there are at most m! permutations. Choosing A and the matching elsewhere gives a multiplier with Gaussian cutoff:
  A_{n,k}=(n)_{2k}(n−2k−1)!! J_{n,2k}=∏_{j<k}(n−2j)/(n+2j+1),  m=2k,
where (n)_m denotes a falling factorial. As in YS Lemma 5.1, A≤exp(−k²/(4n)); also A_{n,k}→exp(−x²/2) if 2k/√n→x≥0, by summing the logarithms (uniform on compact x-ranges). Convention (−1)!!=1.

## 3. Why the signed coefficients have the needed scale

Use an exponential generating series in z and mark each vertex of an odd cycle by exp(s). Before marking, the signed series of long-cycle permutations is
  H₀(z)=exp(∑_{l odd≥3}z^l/l−∑_{l even≥4}z^l/l)=(1+z)exp(−z+z²/2).
Ordinary directed cycles are used: both orientations of each length ≥3 are counted. After marking, c_m is the coefficient of z^m in
  ∂_s^r [ H₀(z) exp(∑_{l odd≥3}(exp(sl)−1)z^l/l) ] at s=0.         (3)
This is H₀ times a polynomial in L_j(z)=∑_{l odd≥3}l^{j−1} z^l (1≤j≤r), obtained as r! times the coefficient of s^r in exp(∑_{j=1}^r L_j(z)s^j/j!). Each L_j=(z d/dz)^{j−1}[z³/(1−z²)] is rational with poles only at ±1 of order j. Its leading coefficient at +1 is (j−1)!/2, in powers of (1−z)^{-1}. Therefore the coefficient of the pole of order r at +1 in (3) is
  H₀(1) r! [w^r] exp(∑_{j≥1} w^j/(2j)) = 2e^{−1/2} (1/2)^{overline r},
with rising factorial. At −1 the pole has order at most r−1 because H₀(−1)=0. Subtracting the principal parts leaves an entire function. By the binomial series and Cauchy's estimate on any fixed circle of radius >1 for that remainder, we obtain
  c_m ~ 2e^{−1/2}(1/2)^{overline r} m^{r−1}/(r−1)!,     |c_m|≤C_r(m+1)^{r−1}. (4)
This applies to even m without discarding the −1 singularity. For r=1 it says c_m→e^{−1/2}, including on the required even subsequence.

## 4. Summing without losing cancellations

From (1), the fixed-point-free weighted sum is E[X^r; no singleton]. In the range m>√n log n, the unsigned contribution is bounded by C∑ A_{n,m/2}m^r, superpolynomially small. In the remaining range, replacing each p_H by b_{n,m} costs at most
  C_r∑_{m even} A_{n,m/2} m^r(m² log⁸ n/n²+exp(−c log² n))
  = O_r(n^{(r−1)/2} log⁸ n)+o(1) = o(n^{r/2}).
Here ∑_{m≥0}e^{-m²/(16n)}(m+1)^s=O_s(n^{(s+1)/2}), s≥0. Now group *signed* types before replacing b/J by e^{1/2}: (4) bounds the corresponding total absolute coefficient weight by O_r(n^{r/2}), so (2) makes this second error o(n^{r/2}). Extending the sum back to all even m costs only a superpolynomial tail. Hence
  E[X^r; no singleton]=e^{1/2}∑_{k≤n/2} c_{2k}A_{n,k}+o(n^{r/2}).
The mesh of m/√n is 2/√n. Dividing by n^{r/2}, (4), the compact Gaussian limit and the Gaussian majorant give the Riemann integral
  (1/2)^{overline r}/(r−1)! ∫_0^∞ x^{r−1}e^{−x²/2}dx
  = [(1/2)^{overline r}/r!] 2^{r/2} Γ(1+r/2).                       (5)

## 5. The exceptional singleton and the conditional law

At most one singleton can occur since two unmatched people block each other. Fix that person f, and put N=n−1. With a fixed-point-free permutation on the remainder, its joint stability with f is given by the n−1 variable stability integral with extra factor ∏_{i≤N}(1−x_i)≤e^{−S}, S=∑ x_i: all people prefer one another to being unmatched, so every other person must prefer their successor to f. YS Lemma 3.1 bounds this by C J_{N,m} E[e^{-S}] with S² distributed as chi-square_{N+m}. Uniformly this expectation is ≤exp(−√N/2)+P(S²<N/4)≤C exp(−c√N), by the chi-square lower-tail Chernoff bound (or use E e^{−S²/2}=2^{−(N+m)/2}). The unsigned permutation multiplier times J is at most
  (N)_m (N−m−1)!!/(N+m−1)!! ≤ 1
for odd m: it is 1 at m=1 and its ratio at m+2 to that at m is (N−m)/(N+m+1). The long-vertex cycle count is at most m!, already included in this multiplier. Summing over f, m and permutations bounds the probability of any singleton by Cn² exp(−c√n). With X≤n it contributes o(1) to every fixed moment. This also avoids treating singleton scores as independent continuous self-scores.

Equation (5) is precisely E[B^r]E[R^r]. Since 0≤RB≤R has all positive exponential moments, these moments determine the law; the method of moments gives the stated convergence. By Tan, X=0 on U^c. Chin–Michelen's theorem implies P(U)→1 (the sharp solvability rate of YS is not needed). The conditional r-th moments are exactly the unconditional ones divided by P(U), and conditioning on an event of probability tending to one does not change the weak limit. At r=1 the constant is √(π/8). This argument measures the instance invariant, not a uniformly sampled or size-biased stable permutation.
