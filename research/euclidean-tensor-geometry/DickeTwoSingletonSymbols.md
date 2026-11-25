# The Dicke entropy formula for two singleton symbols

**Yongxian Zhang.** Research note (AI-assisted proof development and verification).

For k≥4 let S consist of the permutations of (0^{k−2},1,2). Write L=k(k−1), and let h=H((k−2)/k,1/k,1/k), with log base 2. Then the asymptotic induced matching number of S, and the asymptotic subrank of any tensor over any field with exactly this support, are both 2^h.

The upper bound is the usual information-to-slice-rank argument (Dicke case of the support functional): every term in S^{⊠n} has total information knh across all k words, measured under the product of the symbol marginal. Every term therefore has a party word of information at most nh. At each party at most 2^{nh} words have this information bound. Assigning terms to such a party and word proves slice rank ≤k2^{nh}. Tensor subrank is at most slice rank; an induced matching gives a monomial restriction to a diagonal by projection and rescaling on any field.

For the lower bound use higher-order Coppersmith–Winograd (Christandl–Vrana–Zuiddam, as stated in Arunachalam–Vrana–Zuiddam, https://arxiv.org/html/1905.03148, Theorem 1.3). The uniform distribution P on S has entropy log L and each coordinate marginal ((k−2)/k,1/k,1/k). Encode the symbols 0,1,2 by 0,q,p for distinct primes p,q (for example p=2,q=3). The coordinate sum on S is p+q; subtracting this from the last coordinate encoding makes the total zero and leaves every difference unchanged. Encode each word uniquely as q e_I+p e_J, I≠J.

Let R be a collision set in the theorem, whose pairs share some fixed coordinate, and contain an off-diagonal pair. Let r be the rational rank of all integer difference vectors x−y for (x,y) in R. They have zero sum and zero fixed coordinate, hence 1≤r≤k−2. For every law Q on R with the prescribed 2k marginals it suffices to show
  H(Q) ≤ log L + r(log L−h)/(k−2).
For r=k−2, take the common symbol Z at the fixed coordinate. It is a function of each word X,Y, and H(X,Y)≤H(X)+H(Y)−H(Z)≤2log L−h, as required.

For 1≤r≤k−3, let W_p and W_q be the spans of the reductions of all the difference vectors modulo p and q, respectively. They each have dimension ≤r since every integer minor of size r+1 vanishes. On [k] define the equivalence relation i∼_p i' iff e_i−e_i'∈W_p and similarly ∼_q for W_q. The vectors e_i−e_{i_0} over the nonrepresentatives i in each equivalence class are linearly independent across all the classes, since each contains a private nonrepresentative coordinate. Thus Σ_C(|C|−1)≤r for each partition. For every pair (X,Y)∈R, the p-class of its singleton-1 position agrees between X and Y; reducing modulo p erases singleton 2 and q is invertible. Likewise their q-classes of their singleton-2 positions agree. Let U(X) be this ordered pair of equivalence classes, so U(X)=U(Y).

Each individual singleton position under Q's Y marginal is uniform on [k], by its k coordinate marginals. Conditional on its equivalence class C, its entropy is log |C|. Thus, by conditional subadditivity and dropping irrelevant conditioning,
  H(Y|X) ≤ H(Y|U(Y))
         ≤ (1/k) Σ_{C in partition p} |C| log |C|
            + (1/k) Σ_{C in partition q} |C| log |C|
         ≤ [2(r+1)/k] log(r+1).
In the last step, a class of size r+1 and singleton classes maximize the sum under Σ(|C|−1)≤r: the function g(t)=(t+1)log(t+1) on t≥0 is increasing, convex and vanishes at zero, so merging any two deficits is at least as good. Using H(X)≤log L proves H(Q)≤log L + [2(r+1)/k]log(r+1).

It remains to verify [2(r+1)/k]log(r+1) ≤ r(log L−h)/(k−2). The function [(r+1)/r] ln(r+1) increases for r>0, since its derivative is [r−ln(1+r)]/r²>0. Therefore it suffices to check r=k−3. Using log L−h=log(k−1)+[(k−2)/k]log(k−2), and writing natural logarithms for the check, the desired comparison rearranges to
  k(k−3) ln(1+1/(k−2)) ≥ 2 ln(k−2).
For k=4, (3/2)^4>4 verifies it. For k≥5 use ln(1+1/(k−2))≥1/(k−1), and abbreviate t=k−2≥3. The remaining inequality t−2/(t+1)≥2 ln(t) follows at t=3 and thereafter by differentiation (1+2/(t+1)^2−2/t>0).

This verifies every collision-set bound in higher-order CW, yielding matching asymptotic induced matching lower bound 2^h. No dependence on the coefficient field arises: the primes are used only to analyze integer difference vectors in the combinatorial bound. This proves a family of the general Dicke entropy conjecture, not the unrestricted conjecture. 

## Literature update: a general proof

Wenqi Zhu, Chunlin Liu, Kai Zou, and Ping Nie, [*The Entropy Law for the Asymptotic Subrank of Dicke Tensors*](https://github.com/erenup/dicke-tensor-subrank) (November 2026), give a written proof for all multiplicity tuples over the complex numbers, with an induced-matching lower bound. Their method uses the entropy of quotient fibers under permutation symmetry and isolates candidates against the entire tensor-power support. The argument was checked here at the written-proof level; the asymptotic theorem is not a Lean-certified result. The induced-matching construction only uses the support, and the slice-rank upper bound also depends only on the support. For finite coefficient fields one can prove the upper bound after scalar extension to an infinite field. Hence their proof also yields the all-field, arbitrary-nonzero-weight variant of this note. This note is retained as an alternative proof or certificate for its narrower scope, not as a novelty or priority claim.
