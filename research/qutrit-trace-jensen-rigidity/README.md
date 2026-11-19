# Which quantum trace Jensen gaps are squared Hilbert distances?

Yongxian Zhang (张永贤). AI-assisted research draft, November 19, 2026. Internally checked, not externally peer reviewed. Historical priority is not claimed.

For a continuous real function $f$ on $[0,1]$ and density matrices $A,B$, consider
$$
J_f(A,B)=\tfrac12\operatorname{Tr}f(A)+\tfrac12\operatorname{Tr}f(B)-\operatorname{Tr}f((A+B)/2).
$$

**Classification.** In each fixed dimension $d\ge3$, $J_f$ is conditionally negative definite on the density matrices if and only if $f(t)=at^2+bt+c$, $a\ge0$. In that case $J_f(A,B)=a\operatorname{Tr}(A-B)^2/4$; affine generators give zero. It is enough to test the necessity on strictly positive *real* qutrits with a two-by-two block and scalar complement. [Proof](PROOF.md). The Shannon case was already settled negatively by **Teng Zhang** (Theorem 1.6, Example 9.6), and the [earlier five-state note](../five-qutrit-jensen-entropies/) covers the Jensen–Tsallis range through order two. This classification concerns trace generators, not every spectral entropy; in particular it does not assert a classification for the functional $\log\operatorname{Tr}A^q$.

**A separate triangle counterexample.** Failure of negative type need not imply failure of the triangle inequality. For the specific non-affine operator-convex generator $f(t)=(1+79t)^{-1}$, three full-rank rational qutrits *do* violate the triangle inequality for $\sqrt{J_f}$. The two equal short squared distances are $4241/480480$; the long squared distance is $17/480$, strictly greater than four times either short squared distance. This checks the scope of [Teng Zhang, arXiv:2602.08164v1](https://arxiv.org/abs/2602.08164v1), Theorem 1.9 and Corollaries 1.10 and 10.3, **as stated in v1**. It does not negate the Shannon metric theorem or the positive qubit embedding result. [Exact three-state calculation](TRIANGLE.md). Qualitative existence also follows by transferring older results of **Keiji Matsumoto**; the [prior-art derivation](PRIOR-IMPLICATION.md) spells out the reverse-test bound, regularization and trace-one completion. The contribution of this part is the explicit exact certificate, not a claim of first discovering nonmetricity.

See [sources and repository comparisons](SOURCES.md) and [independent internal review](REVIEW.md). The review labels refer to the frozen proofs: the public classification text is identical, and only mathematical delimiters, status wording and source attribution were edited in the three-state note. The reviewer did not serve as an external referee.

## Reproduce the arithmetic checks

From this directory, with Python 3 (standard library only):

```sh
python3 -B -O verify_rigidity.py
python3 -B -O verify_triangle.py
python3 -B -O independent.py
sha256sum -c SHA256SUMS
```

The checks confirm finite algebraic identities; they do not replace the analytic arguments for continuous generators. Original outputs: [classification](RIGIDITY-CHECKS.txt), [triangle](TRIANGLE-CHECKS.txt), [independent calculation](INDEPENDENT-CHECKS.txt).
