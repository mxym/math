# Shannon entropy of Bernoulli bits under at most two-to-one observations

Take $n$ independent Bernoulli bits, all with success probability $p$, and observe only a deterministic function of them. If no output has more than two possible inputs and the all-zero and all-one words have singleton fibers, the output’s Shannon entropy is **strictly concave in $p$** on $[0,1]$. This works for arbitrary dimension, without an additive or symmetry hypothesis on the observation.

- **Weighted Bernoulli sums.** In [Neunhäuserer’s recursive-overlap conjecture, §3](https://arxiv.org/pdf/2609.05546v2), this proves strict concavity and a unique maximum at $p=1/2$ whenever each attained subset sum has at most two representations. It does not prove the unrestricted conjecture.
- **Sharpness for arbitrary deterministic observations.** A 24-bit map with singleton extremes and fibers of size at most three has *positive* entropy curvature at $p=1/2$. It identifies comparable inputs and therefore **is not a positive weighted sum**. The example establishes no obstruction to extending the weighted-sum result to three or more representations.

Read the [proof](PROOF.md), [three-point construction](SHARPNESS.md), [prior-work comparisons](SOURCES.md), and [independent mathematical review](REVIEW.md). The [author’s standard-library checker](verify.py) uses certified rational logarithm intervals and exact orbit histograms. Its finite tests are supporting checks rather than the all-dimensional proof:

```sh
python3 -B -O verify.py
sha256sum -c SHA256SUMS
```

See [the recorded run](CHECKS.txt). AI-assisted research with independent internal AI proof review, not externally peer-reviewed. No priority or minimum-dimension claim.
