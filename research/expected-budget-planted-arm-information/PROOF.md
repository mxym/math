# The stopped mutual-information converse

Let J be uniform on n≥2 arms. Given J, each pull of J produces an independent Bernoulli reward with probability p₊=(1+Δ)/2; every other pull has success probability p₋=(1−Δ)/2. An adaptive policy can choose successive arms and whether to stop from its past actions, observed rewards and independent randomization. Let τ count its pulls, H_τ be the transcript including its length, and t≥0 bound E[τ] under the uniform planted prior. No such budget is imposed under any auxiliary model. All logarithms are natural.

**Theorem.** For all 0<Δ≤1,
    
    I(J;H_τ) ≤ min{log n, 16(2+log n) t Δ²/n}.

In particular, this gives the conjectured converse in Gu–Han–Qian, NeurIPS 2025, §4.3 and Appendix C.5. Together with their Proposition 4.4 it proves that the optimal information has order min{1,tΔ²/n} log n in their noise regime (use monotonicity beyond n/Δ²). Our upper bound separately holds up to the noiseless endpoint; the constant displayed here need not be optimal. The success-probability results and stopped achievability are theirs.

**Proof.** Reveal to the analyst the entire independent random seed R of the policy, so all decisions are deterministic given R and preceding observations. First truncate after T=τ∧m pulls, with m a fixed positive integer. Write P_i for the law of this seeded transcript when the only high arm is i, and M for the uniform mixture of the P_i. Let N_j denote the number of pulls of arm j by T. The key auxiliary law P_{ij}, for distinct i,j, makes **both** i and j high and leaves every other arm low. Use the same policy, seeds and truncation in all these experiments. The auxiliary costs need not obey the budget, since we will charge only the costs under the true single-plant laws.

Use H²(A,B)=∫(√dA−√dB)². We first show
    
    H²(P_i,P_{ij}) ≤ 4Δ² E_i N_j.                                     (1)

If Δ≤1/2, the conditional KL chain rule gives
    
    D(P_i || P_{ij}) = D(Ber(p₋)||Ber(p₊)) E_i N_j
                     = Δ log((1+Δ)/(1−Δ)) E_i N_j.

Indeed, condition on R and pad the bounded transcript with a cemetery symbol after stopping. At each stage a reward contributes only when the next pull is made and the chosen arm is j; both events are determined by the previous seeded history. In all other cases the conditional divergence is zero. Integrating 2/(1−x²) on [0,Δ] bounds the logarithm by (8/3)Δ. Now use H²(A,B)≤D(A||B), which follows by integrating −log x≥2(1−√x).

For Δ≥1/2, couple the two experiments with the same seed and fresh shared uniform draws, a reward being obtained by thresholding the draw at its success probability. Until the first disagreement all decisions match. A first disagreement is possible only at a pull of j; at such a pull its conditional probability is Δ. Consequently the total probability of ever disagreeing is at most Δ E_i N_j, by summing over times when the first path is still active, chooses j and has not yet disagreed. Total variation is no larger than this coupling probability; H²≤2TV pointwise upon integration. As 2Δ≤4Δ² here, (1) follows, including at Δ=1.

For distinct i,j, the triangle inequality for H followed by (1) gives
    
    H²(P_i,P_j) ≤ 2H²(P_i,P_{ij}) + 2H²(P_j,P_{ij})
               ≤ 8Δ²(E_i N_j + E_j N_i).

Each term on the right averages over the *other* label. Because ∑_j N_j=T, averaging over the n² ordered pairs (diagonals on the left are zero) gives
    
    (1/n²)∑_{i,j} H²(P_i,P_j) ≤ (16Δ²/n)(1/n)∑_i E_i T ≤ 16Δ² t/n.   (2)

To pass to information use the bounded-density comparison in the proof of Gu–Han–Qian Theorem 3.1(a), credited there to Yang–Barron, Lemma 4. In detail, since P_i≤nM, set u=√(dP_i/dM)≤√n. For f(u)=2u²log u−u²+1 (continuous at 0), f(1)=f′(1)=0 and f″(u)=4+4log u≤4+2log n. Hence f(u)≤(2+log n)(u−1)². Integrate, then use convexity of H² in its second argument, to obtain
    
    I(J;R,H_T) = (1/n)∑_i D(P_i||M)
       ≤ (2+log n)(1/n)∑_i H²(P_i,M)
       ≤ (2+log n)(1/n²)∑_{i,j} H²(P_i,P_j).

Equation (2) proves the upper bound at m. The seeded truncation histories generate increasing sigma-algebras: every shorter truncated transcript is recovered by truncating the longer one, with length visible. Since Eτ≤t<∞ under the planted mixture, τ is finite there almost surely, and their union generates the full seeded history up to null sets. The n posterior probabilities of J converge by bounded martingale convergence; continuity and boundedness of entropy then give convergence of the mutual informations. Removing R by data processing and applying I≤log n finishes. At t=0 no samples are taken almost surely. At Δ=0, if admitted, the observations and actions are independent of J. ∎

The point of (1)–(2) is not a new KL or Hellinger inequality. It is the choice of a common two-high experiment for each pair and the averaging of *off-diagonal* true-law pull counts. The all-low reference in the original fixed-horizon proof would instead charge the stopping cost under a law that need not even have finite expected duration.
