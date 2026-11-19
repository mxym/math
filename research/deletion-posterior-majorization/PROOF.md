# Constant observations majorize all fixed-length deletion posteriors

## Scope and statement

Fix an alphabet A of size q≥2, input length n≥0 and surviving length 0≤m≤n. The input X is uniform on A^n. An independent uniformly random m-subset I of [n] is retained, in its original order; Y=X_I. This is the fixed-deletion channel, or the independent identically distributed deletion channel conditioned on output length m (whenever this event has positive probability). For y∈A^m let p_y=(Pr(X=x | Y=y):x∈A^n). All vectors include their zero entries and are compared after decreasing rearrangement. For every a∈A,
    
    p_y ≺ p_{a^m}.

Here u≺v means every prefix sum of the decreasing rearrangement of u is ≤ the corresponding sum for v, with equal overall sums. If 1≤m<n then equality up to permutation holds exactly for constant y. All strictly Schur-concave entropies, in particular Shannon and every finite Rényi order 0<α<∞, thus have just the constant outputs as minimizers. The same is true of min-entropy (α=∞), by a separate argument below. Order zero does not distinguish outputs. When m=n all posteriors are point masses. When m=0 there is a single output, and the posterior is uniform. For m=1 all outputs are constant, consistently with the assertion.

This is the minimization side of the binary Atashpendar–Roscoe–Ryan question, now simultaneously for every finite alphabet, both lengths, and every Schur-concave functional (strict uniqueness for the strictly Schur-concave ones). It is a pointwise posterior statement, not about capacity, entropy given a fixed *transmitted* word, or an optimized input prior. There is no alternation-maximization claim here.

## Proof by coordinatewise alignment of cylinder sets

Write B=binom(n,m) and D=B q^(n-m). The number K_y(x) of retained masks I satisfying x_I=y is the number of embeddings with multiplicity. Double-counting (x,I) gives Σ_x K_y(x)=D, so Bayes' rule gives p_y(x)=K_y(x)/D, with the same denominator for every y.

Consider a family of cylinder indicators, one per mask, each specifying one letter at each coordinate of that mask. Initially the letters spell y, but intermediate families need not come from any word. Let F(x) be their sum. Choose an input coordinate j and change *all* requirements at j to a; masks not containing j are unchanged. Holding the other coordinates fixed, let C count satisfied masks avoiding j; D_b counts masks containing j originally requiring b there whose other requirements are satisfied. Before and after, the two q-tuples of F in this fiber are
     
    (C+D_b : b∈A)    and    (C+Σ_b D_b, C,…,C)   (up to order).

The second majorizes the first: both sums are qC+ΣD_b, and for any 1≤r≤q the old r-largest total is at most rC+ΣD_b, the new r-largest total. This fiber statement implies the full majorization. Indeed any set of r old entries chooses some number in each fiber; the r-largest old sum is at most the total obtained by choosing the same counts, but the largest entries, in the new fibers. That is at most the r-largest new sum. Global totals are identical. Apply this alignment for all n coordinates; the final F counts embeddings of a^m. Transitivity and division by D prove the result.

**Strictness.** If y is nonconstant choose k with y_k≠y_(k+1). Do j=k+1 first. Use two masks inside the first m+1 positions. Both retain input position r for pattern positions r<k, and r+1 for pattern positions r>k+1. Pattern positions k,k+1 are placed at (k,k+1) in the first mask and at (k+1,k+2) in the second. Their common retained positions other than j have the same letters, while j has different required letters. One can therefore satisfy both sets of requirements *outside* j in a single assignment. In this fiber at least two D_b are positive. The local majorization is not a permutation, so the sum of squares increases strictly; explicitly the increase is 2Σ_{b<c}D_b D_c>0. It is nonnegative on all other fibers and at all remaining steps. Consequently p_y and p_{a^m} cannot be permutations. Constant outputs produce permutations of each other by relabeling the alphabet. The asserted strict entropy consequences follow from strict convexity of u log u (0 log 0=0), of u^α for α>1, and strict concavity for 0<α<1 (with the usual sign of the Rényi prefactor).

**Endpoints.** The maximum entry of p_{a^m} is B/D=q^{-(n-m)}, attained at x=a^n. For nonconstant y, the two explicit conflicting masks cannot both match any x, so max_x K_y(x)≤B−1. This gives strictness at α=∞. For order zero, compare support sizes: in a uniform host the greedy search for successive required letters has a success probability 1/q at each trial conditionally on the entire past. Continue targeting a fixed letter after the last match; this gives n independent Bernoulli(1/q) trials by the product rule. The output word is a subsequence iff at least m successes occur. Thus the support size q^n Pr(Bin(n,1/q)≥m) is independent of y. These endpoint observations are not needed for the Shannon claim.

For reference, under uniform enumeration the constant vector has entry binom(t,m)/D with multiplicity binom(n,t)(q−1)^(n−t) for each t=0,…,n (binom(t,m)=0 for t<m). The formula is elementary and was already reported in the original binary work.
