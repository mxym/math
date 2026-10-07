# Independent review of 005 v4 symmetric equality

7 October 2026. Audited snapshot: `dd969ea280508a15995fbe83a80cac0f6d227f73`.

**Scoped pass:** no substantive correction was required in the written equality classification or qualitative stability theorem. The source remains unchanged. This is an independent model review, not external peer review, formal verification or novelty certification.

The theorem classifies centrally symmetric bodies satisfying a(K)=1/2 as affine Cartesian products of centrally symmetric one- and two-dimensional factors. The audit reconstructed the balanced Rademacher equality cases, exclusion of long exposed circuits, support extension, rank-two circuit decomposition and the passage back to Cartesian products. It checked both polytopal and general convex-body arguments and the fixed-dimension compactness statement.

The commit-pinned manifest matches all 11 listed source/evidence hashes. The supplied 7,749-case exact Rademacher regression passes in ordinary and optimized Python. An additional independent checker exhausts 6,144 spanning circuit configurations in dimensions three through five and agrees with the rank-two matching criterion. These finite tests do not replace the general written proof.

One optional wording improvement is to use positive probability of an independent sampled basis in Lemma 5.1 rather than an expectation when discussing an arbitrary law without a moment assumption. Its existing extended-real positive-expectation reasoning is sufficient, so this is not a mathematical gap.

The new quantitative simplex-rigidity supplement concerns the different lower endpoint a(K)=1/(d+1). It does not turn v4’s qualitative symmetric upper-end stability into an explicit modulus. The optimal asymptotic projection-volume constant also remains undetermined in these results.

[Original v4 proof](https://github.com/mxym/math/blob/dd969ea280508a15995fbe83a80cac0f6d227f73/preprints/005-simplex-product-optimum/v4/paper.md) and [pinned manifest](https://github.com/mxym/math/blob/dd969ea280508a15995fbe83a80cac0f6d227f73/preprints/005-simplex-product-optimum/v4/MANIFEST.json).
