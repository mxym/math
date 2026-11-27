# When the scalar \((0,\delta)\)-DP monotone optimum remains optimal

Geng, Ding, Guo and Kumar (AISTATS 2019) optimized scalar additive noise within the symmetric decreasing class. Their §1.1 footnote suggests that the monotonicity assumption might be dispensable. For the power costs \(\mathbb E|X|^p\), this note determines exactly when their optimum has the **same value without that assumption**:

- For every \(p\ne1\) and every \(0<\delta<1\), a compactly supported periodic perturbation of the continuous component has the same privacy budget and a strictly smaller cost.
- For \(p=1\), their value is globally optimal exactly when \(\delta\ge1/2\) or \(\delta=1/(2k)\) for a positive integer \(k\). A direct inequality for arbitrary probability measures proves the positive cases; a strictly improving mechanism treats every other value.

The original theorem within its stated class is unchanged. The model requires the total-variation bound for **every real shift** of magnitude at most the sensitivity, not just the largest shift. This is not a formula for the unrestricted optimum when the published optimizer is suboptimal. Proofs are analytic; exact rational and independent checks are provided.

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~
