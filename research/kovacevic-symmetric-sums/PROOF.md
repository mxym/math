# The finite-alphabet maximum-entropy sum when all but one marginal are symmetric

**Scope.** Ordinary Shannon entropy, arbitrary independent marginals on the integer interval: the general Kovačević conjecture is **not** proved here. The maximizing construction and its value are Kovačević's; the signed-sum concentration input is classical. No uniqueness or publication-priority claim. Logs below are natural.

## Statement and attainment

Let integers n,r≥1, and let independent X_i have values in {0,…,r}. Assume at least n−1 marginal laws are invariant under x↦r−x. They need not be identical, and need not use the entire alphabet. Write b_m(k)=2^(−m) binom(m,k), H_m=H(Bin(m,1/2)), H_0=0,
and Z=exp(H_n)+(r−1)exp(H_{n−1}). Then

    H(S) ≤ log Z,   S = X_1+⋯+X_n.

The maximum in this class is attained. For n=1 it is log(r+1), the usual bound for one variable. In general the first n−1 input laws may be fair on {0,r}, with the last putting w/2 at each endpoint and exp(H_{n−1})/Z at each of the r−1 interior letters, where w=exp(H_n)/Z. These probabilities sum to one, including when r=1. The output Q is strictly positive on every site 0,…,nr, and satisfies

    Q(kr)            = exp(H_n) b_n(k)/Z                (0≤k≤n),
    Q(kr+j)          = exp(H_{n−1}) b_{n−1}(k)/Z        (0≤k<n, 1≤j<r).

The residue-zero slice is a multiple of Bin(n,1/2); each other slice is a multiple of Bin(n−1,1/2). Therefore E_Q log(Z Q)=0 and H(Q)=log Z. The claim is an upper bound; no hypotheses on prime factors or alphabet parity are imposed.

## A supporting score

For m≥0 define μ_m=E log binom(m,B_m) for B_m∼Bin(m,1/2), and L_m(k)=log binom(m,k)−μ_m. At normalized positions u=s/r, define a score G on [0,n] by

    G(k)=L_n(k) at integers k,
    G(u)=L_{n−1}(floor(u)) on the open unit intervals.

Then G(s/r)=log(Z Q(s)). For any output P, zeros allowed, elementary relative entropy gives exactly

    H(P)=log Z − E_P G(S/r) − D(P||Q).

Thus it suffices to bound the *linear* functional E_P G from below by zero, not the average conditional entropies. The off-lattice extension of G is only a proof device.

If all marginals are symmetric, we may generate X_i=(r/2)(1+A_i ε_i), where A_i=|2X_i/r−1| in distribution, A_i are independent, and independent uniform signs ε_i are independent of all amplitudes. This representation also holds at A_i=0 by adjoining an unused fair sign. It therefore suffices by linearity to show

    E G(U)≥0,     U=(n+Σ_i a_i ε_i)/2,     |a_i|≤1,                       (1)

for every deterministic amplitude vector (the permission of negative amplitudes just flips signs).

## The off-grid comparison

Suppose U never hits an integer. Put K=floor(U), m=n−1, so 0≤K≤m. The needed fact is that K is at least as concentrated in all middle blocks as B_m. For each integer 1≤j≤floor(m/2), use the upper-tail sign configurations F_j={ε:Σ a_i ε_i> n−2j}. If ε,η∈F_j, then their weighted sums add to more than 2(n−2j). Each differing coordinate cancels and each matching coordinate contributes at most 2, hence d_H(ε,η)≤2j−1. The odd-diameter binary-cube theorem (Kleitman) gives

    |F_j|≤2 Σ_{i=0}^{j−1} binom(n−1,i).

Here 2j−1<n, as required. Upon division by 2^n this is Pr(U>n−j)≤Pr(B_m<j); the lower tails Pr(U<j) coincide with the left by sign symmetry. Taking the complement and using no ties gives

    Pr(j≤K≤m−j) ≥ Pr(j≤B_m≤m−j).                                         (2)

This concentration inequality is the signed-sum lemma of Ordentlich, later reproved by Yu. The cube diameter argument just supplies a short derivation. Since log binom(m,k) is symmetric and nondecreasing up to the middle, it is a constant plus a nonnegative combination of indicators of the blocks [j,m−j] (coefficients are successive differences of log binomial coefficients). Hence (2) gives E L_m(K)≥0, which is (1) in this case. For m=0,1 there are no nonconstant blocks and the conclusion is immediate.

## Resolving integer ties

For 1≤k≤n−1 set t=k/n and h(t)=−t log t−(1−t)log(1−t) with 0log0=0. The identities binom(n−1,k−1)=t binom(n,k) and binom(n−1,k)=(1−t) binom(n,k) give

    L_n(k) − [L_{n−1}(k−1)+L_{n−1}(k)]/2
       = −(1/2)log(t(1−t)) − (μ_n−μ_{n−1}) ≥ 0.                          (3)

Indeed delete the last bit from n independent fair bits. Conditional on their sum k that bit is one with probability k/n; the shortened sum has unconditional law B_{n−1}. Taking conditional averages of the two binomial identities (using the sole possible branch at k=0,n) gives μ_n−μ_{n−1}=E h(B_n/n)≤log 2. Also t(1−t)≤1/4, proving (3).

If all |a_i|=1, then U∼B_n and E G=0 exactly. Otherwise choose i with |a_i|<1: then 0<U<n for every sign vector, so only interior integers could be hit. Select δ>0 so small that |a_i|+δ<1, δ/2<1/2 and δ/2 is smaller than the distance to the nearest integer for every *nonintegral* value of U. The last condition is vacuous if there are none; only finitely many values occur. In two separate deterministic amplitude vectors replace a_i by a_i±δ, forming U_±=U±δε_i/2. For both perturbations no integer is hit, and they remain within [0,n]. Negative amplitudes, including the case a_i=0 on the minus side, are allowed in (1).

For noninteger U, both perturbed scores equal the original. If U=k, the two scores are L_{n−1}(k−1), L_{n−1}(k) in some order, whose mean is at most G(k) by (3). Thus G(U)≥(G(U_+)+G(U_−))/2 pointwise. Each perturbed expectation is already nonnegative by the off-grid comparison. This proves (1). The perturbations need not preserve the original integer support: no entropy comparison or invocation of the desired theorem is made for them, only the previously established real-amplitude score lemma.

Taking expectations over the original amplitudes proves the score bound, and then the entropy bound for symmetric marginals.

## One arbitrary marginal

Relabel the possible exception as X_n; T=Σ_{i<n}X_i has the same law as (n−1)r−T. Therefore T+r−X_n has the same entropy as S (its law is that of nr−S). Independently of T, replace the law of X_n by the equally weighted mixture of the original and reflected laws. The new input is symmetric, and the resulting convolution is the equally weighted mixture of the two output laws above. Concavity of Shannon entropy shows its entropy is at least H(S); the fully symmetric case bounds it from above by log Z. This argument cannot in general be iterated across two asymmetric inputs, because the remaining sum need not be symmetric. 

In particular we have not obtained the unrestricted maximum for general n,r≥3. For r=1 or r=2, or for n≤2, the corresponding unrestricted cases were already known.
