# A logarithmic converse loss for unassisted quantum and private erasure coding

**Theorem.** Fix an integer d ≥ 2, an erasure probability p ∈ (0,1/2), and an infidelity ε ∈ (0,1). Let C=(1−2p)log₂d and V=4p(1−p)(log₂d)². Use the unassisted parallel model of Wilde [W], §§2.3–2.4, with squared state fidelity, arbitrary mixed encoders or prepared states, and arbitrary collective decoders. Let Q_et and Q_eg be the optimal logarithmic entanglement transmission and generation dimensions and P_opt, P_max, P_marg the optimal logarithmic private message sizes in the three joint criteria of [W]. All are in bits and at blocklength n and error ε. Then each of Q_et, Q_eg, P_opt, P_max equals

    nC + √(nV) Φ⁻¹(ε) + O_{p,d,ε}(log n),

and P_marg equals the same formula with ε replaced inside Φ⁻¹ by 1−√(1−ε). Here Φ is the standard normal CDF. In particular this proves the O(log n) converse improvement requested in [W], Appendix D.5. The lower bounds are exactly the previously known lower bounds.

## 1. Quantum reduction used from [W]

For the private case a flag-diagonal measurement can only increase both optimized and marginal joint fidelities; use the flag-reduced code for the upper bound. Write f_E for its conditional optimized squared fidelity, and g_E for its conditional squared fidelity against the actual conditional environment marginal. Thus 0 ≤ g_E ≤ f_E ≤ 1. Write F_E for quantum conditional Bell fidelity, for either transmission or generation. The receiver has the flag and the erasure pattern probabilities are input-independent, so conditional decode maps can be taken on each flag subsystem. There is no symmetry assumption on the code.

Let K be binomial(n,p); a bar denotes the uniform mean on the size-k layer. Then the original f_opt and either quantum fidelity are bounded above by E[bar f_K] and E[bar F_K], respectively (the relevant flag-conditioned identities are equalities after the flag reduction). For the actual-marginal criterion its square root fidelity is bounded by E[r_K], with r_k the average of √g_E over |E|=k, and

    r_k ≤ √(bar f_k).                                           (1)

These are Lemma 4.1, Eq. (3.12), and Eqs. (6.12)–(6.14) of [W]. The marginal root is essential; averaging g_E instead would give the wrong quantile. For maximal-message private error, Eq. (2.24) lower bounds the error by the optimized average error, so the optimized converse suffices.

Lemmas 4.2–4.3 of [W] supply, separately for either quantum task or the optimized private task, orthogonal projectors P_E on one common finite-dimensional space, with the relevant mean fidelity bounded by the norm of their mean. For distinct E,F of equal size k,

    ‖P_E P_F‖ ≤ min(1, d^(n−2k+|E∩F|)/M),                      (2)

where M is the integer code size or quantum reference dimension. This uses the common surviving physical subsystem of dimension d^(n−2k+|E∩F|), and includes all receiver and sender auxiliary spaces exactly as in [W]. These quantum overlap and flag facts are the input to the proof; we do not modify them.

Here is the scalar-to-operator step (Lemma 4.4 of [W]). If a real symmetric matrix W supported where ‖P_E P_F‖ ≤ η has maximum absolute row sum ≤ ℓ and ‖W−U‖ ≤ ζ, where U is uniform averaging on the index set of size m, then ‖(1/m)Σ_E P_E‖ ≤ ζ+ℓη. In fact, for a unit top eigenvector ψ of the mean, with eigenvalue a>0, set v_E=P_Eψ. Then Σ‖v_E‖²=ma, and the quadratic form of U⊗I on v equals ma². The difference on replacing U by W has absolute value at most ζma. Also |⟨v_E,v_F⟩|≤‖P_EP_F‖‖v_E‖‖v_F‖. The supported term is bounded by (η/2)Σ_E,F |W_EF|(‖v_E‖²+‖v_F‖²) ≤ ηℓma by symmetry. Divide by ma; a=0 is trivial. No positivity, entrywise sign, or interpretation as an operational probability distribution is required of W.

## 2. Signed matrices directly on the layer

Fix p₀ with p < p₀ < 1/2, and consider integers 1 ≤ k ≤ p₀ n. On Ω={E⊂[n]: |E|=k}, use two real symmetric stochastic matrices. A is normalized Kneser adjacency: A_EF=1/binom(n−k,k) for E∩F empty and 0 otherwise. J is normalized Johnson adjacency: J_EF=1/[k(n−k)] for |E∩F|=k−1 and 0 otherwise. Put

    H=[k(n−k)/n](I−J),   u=k/(n−k),   u₀=p₀/(1−p₀),
    c₀=−ln u₀ > 0.

All matrix operator norms below are Euclidean on the layer, and ‖·‖_row is maximum absolute row sum. The spectral statements that follow also hold with the uniform probability inner product, which differs only by a constant factor.

For R⊂[n] of size j write f_R(E)=1{R⊂E}. Let V_j span these indicators, with V₋₁={0}. The spaces are nested because Σ_{x∉R} f_(R∪{x})=(k−|R|) f_R, and V_k is the whole space. The following computations show scalar action on V_j modulo V_(j−1); the matrices being symmetric, this gives simultaneous orthogonal eigenspaces V_j∩V_(j−1)^⊥. The constant level is j=0. For A, with falling factorials (b)_j,

    A f_R = [(k)_j/(n−k)_j] 1{E∩R=∅}
          = [(k)_j/(n−k)_j] Σ_{S⊆R} (−1)^|S| f_S .

The first identity counts a uniform k-subset disjoint from E and containing R. Its quotient scalar is ν_j=(−1)^j(k)_j/(n−k)_j. For J, the value is 1−j/k when E contains R, is (k−j+1)/[k(n−k)] when |R∩E|=j−1, and is zero otherwise. Subtracting (k−j+1)/[k(n−k)] times Σ_{r∈R}f_(R∖{r}) leaves exactly [1−j(n−j+1)/(k(n−k))]f_R. For the constant level J1=1. Thus the H eigenvalue is x_j=j(n−j+1)/n. For 1≤j≤k, x_j ≥ 1 (x_1=1 and the sequence is increasing up to k<n/2) and x_j≤j. Also |ν_j|≤u^j≤u₀^j≤exp(−c₀x_j), since each of the j falling-factorial ratios is at most k/(n−k).

Take a real constant Λ ≥ max(3,(ln 6+2)/c₀), fixed in n,k. For an integer t≥1 set L=Λt and define a polynomial using the degree-t Chebyshev polynomial of the first kind:

    P_t(x) = T_t((L+1−2x)/(L−1)) / T_t((L+1)/(L−1)).
    W_t = A P_t(H),    B_n=2n+7,    γ=min(1,2/√Λ).

Then W_t is real symmetric, and W_t1=1. If 1≤t<k,

    (W_t)_EF ≠ 0  ⇒  |E∩F|≤t<k,
    ‖W_t‖_row ≤ B_n^t,
    ‖W_t−U‖ ≤ 2 exp(−γ√t).                                     (3)

For support, each monomial in H of degree s uses at most s Johnson swaps, interspersed with possible stays. Multiplication by A first goes to a set disjoint from E; each swap can increase intersection with E by at most one. Cancellation cannot enlarge this support.

For row sums, ‖H‖_row ≤ 2k(n−k)/n ≤ n/2. Hence Z=((L+1)I−2H)/(L−1) has ‖Z‖_row ≤ (L+1+n)/(L−1) ≤ n+3. By submultiplicativity and T_(j+1)(Z)=2ZT_j(Z)−T_(j−1)(Z), induction gives ‖T_j(Z)‖_row ≤ B_n^j. Indeed 2(n+3)/B_n + 1/B_n² ≤ 1, and the base cases j=0,1 hold. A has row norm 1 and the scalar denominator is at least 1.

For the spectral norm, the eigenvalues of W_t−U off the constants are ν_jP_t(x_j). For 1≤x≤L, the Chebyshev numerator is at most 1 in absolute value, and the scalar denominator satisfies

    T_t((L+1)/(L−1)) ≥ ½ exp(2√(t/Λ)),

since arcosh((L+1)/(L−1))=2 artanh(1/√L) ≥ 2/√L and T_t(cosh z)=cosh(tz). For x>L, |(L+1−2x)/(L−1)|≤3x/L and its value is less than −1; |T_t(y)|≤(2|y|)^t for |y|≥1. Thus on x>L the spectral product is at most exp(−c₀x)(6x/L)^t. Its logarithm decreases on x≥L because t/x≤1/Λ<c₀. Its boundary bound exp[t(ln 6−c₀Λ)] is at most exp(−2t). The two ranges give (3).

By (2) and the scalar-to-operator step, for every 1≤t<k≤p₀n, each of bar f_k, bar F_k is bounded by

    min(1, 2 exp(−γ√t) + d^(−s+b_n t)),
    s = log_d M−(n−2k),      b_n=1+log_d B_n.                  (4)

Indeed the support excludes E=F, and its overlap factor times the row bound is at most B_n^t d^(n−2k+t)/M. Notice that b_n is O_d(log n); we will never pay a uniform t·b_n shift.

## 3. Averaging with degree chosen separately for each count

Put a=(n−log_d M)/2 and let I_n be the integer counts pn/2 ≤ k ≤ p₀n. For sufficiently large n all k in I_n are at least 2. Write z=k−a; above a, s=2z. If k∈I_n and z≥b_n, take

    j = floor(z/b_n),    t = min(j,k−1).

This is a positive degree covered by (4), and b_n t≤z. For any of the contributions c_k equal to bar f_k, bar F_k or r_k, (1) and (4) give the common bound

    c_k ≤ min(1, √2 exp(−γ√t/2) + d^(−z/2)).                 (5)

For bar f_k and bar F_k this uses x≤√x for x∈[0,1]; for r_k use (1) directly. The remaining square-root estimate uses √(x+y)≤√x+√y. For 0<z<b_n use just c_k≤1 (bin j=0).

Let A_p>0 give the maximum binomial atom bound A_p/√n, and let τ_n=P(K∉I_n), exponentially small in n (both are [W], Lemma E.1). The integer counts in each half-open interval j b_n≤k−a<(j+1)b_n number at most b_n+1, for any real a. Put c=γ/2. The saturation t=k−1 is handled by

    exp(−c√min(j,k−1)) ≤ exp(−c√j)+exp(−c√(pn/2−1)).

Indeed the left side is the larger of two nonnegative terms, and k−1≥pn/2−1. With the bin j=0 included harmlessly, the total above-threshold contribution from the typical counts is at most

    √2 A_p(b_n+1)/√n · Σ_{j≥0} exp(−c√j)
        + √2 exp(−c√(pn/2−1))
        + A_p/[√n(1−d^(−1/2))].                              (6)

For the first term the series is finite, for example by integrating exp(−c√x) on [0,∞). For the last term, the positive values k−a lie at unit spacing with first at most 1 if k ranges over integers above a; one can extend the sum to all such integers, then use the geometric series. The saturation term uses the total probability ≤1, not a count of layers.

Counts at most a contribute at most P(K≤a), and exceptional counts above a contribute at most τ_n. Together (5)–(6) bound each of the quantum and optimized private fidelities and the square root of the actual-marginal fidelity by

    P(K≤a) + O_{p,d}(log n/√n),                                (7)

uniformly in M and the code. Here one may fix p₀=(p+1/2)/2. The proof permits a outside [0,n] and includes equality k=a in the lower-threshold part. This is a bound on the average over the physical flag distribution; it is not asserting uniformly vanishing fidelity at every k a fixed logarithmic distance above a.

## 4. Gaussian inversion and coding statements

Write α=1−ε for optimized private and either quantum task, and α=√(1−ε) for marginal private; for maximal-message private use optimized private as in §1. A code passing the required error threshold has P(K≤a) ≥ α−O(log n/√n) by (7). Let σ=√(np(1−p)). The uniform Berry–Esseen bound for the binomial, applicable also at a real threshold, gives

    Φ((a−np)/σ) ≥ α−O_{p,d}(log n/√n).

Since α is fixed strictly between zero and one, Φ⁻¹ is Lipschitz locally at α. Thus a≥np+σΦ⁻¹(α)−O_{p,d,ε}(log n). Substitute a=(n−log_d M)/2, multiply by 2log₂d, and use −Φ⁻¹(α)=Φ⁻¹(1−α). This gives exactly the asserted upper bounds in bits, with 1−α the appropriate quantile input. No asymptotic upper limit on the initial code size was used.

For the lower side, [W] Theorem 3.1 and Appendix C give O(1) lower remainders for Q_et, Q_eg and P_opt. Theorem 3.2 gives O(1) for P_marg at its changed quantile and −½ log₂n−O(1) for P_max at its original quantile. These imply the claimed two-sided O(log n) statements. Nothing in this argument shows a sharp third-order coefficient or whether the maximal-message expurgation penalty is needed.

[W] Mark M. Wilde, [Second-order asymptotics for the quantum and private capacities of the erasure channel](https://arxiv.org/html/2611.32395v1), arXiv:2611.32395v1.
