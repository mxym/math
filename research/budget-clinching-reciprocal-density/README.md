# When middle-ironed clinching fails, and a class where it is optimal

**Yongxian Zhang.** Two bidders have independent values with the same continuous distribution, one divisible item (equivalently, lottery allocation probabilities), and the same known hard budget. The objective is expected allocated value, subject to dominant-strategy truthfulness, individual rationality and no positive transfers in the Feng–Hartline model. For uniform values, Feng and Hartline proved that an auction in their middle-ironed clinching family is optimal. They conjectured an extension to regular value distributions; for welfare their regularity condition is a concave CDF.

* **Counterexample with a common budget of one.** On $[0,28/5]$, take the density proportional to $1+(3/5-x)_+/6$. Its hazard is strictly increasing. An explicit four-band auction strictly outperforms every middle-ironed clinching auction in expected welfare. The comparison is against the *best* member of their family and its sign is certified exactly. It does not assert that the four-band auction is itself optimal. See [the construction and proof](PROOF.md).
* **Failure arbitrarily close to uniform.** If the positive continuously differentiable density on $[0,h]$ has strictly concave, nondecreasing reciprocal, then the family fails for **some** common budget. This includes analytic, strictly increasing-hazard examples arbitrarily close to uniform.
* **An optimal nonuniform class.** If the reciprocal density is affine and nondecreasing, then for **every** positive common budget some member of the family is optimal, even against truthful mechanisms that sometimes withhold the item. The constant-reciprocal case is precisely the earlier uniform theorem. See [the two structural proofs](STRUCTURE.md).

These conditions do not classify general densities. The results do not address optimal revenue, liquid welfare, the best prior-independent ratio, or all clinching formats with arbitrary price jumps.

[Original sources, theorem-by-theorem comparison, and limits of the search](SOURCES.md) · [Internal review of the example](REVIEW.md) · [Internal review of the two classes](STRUCTURE-REVIEW.md). AI-assisted mathematical research with independent internal AI review; not externally peer reviewed. No assertion of global priority.

From this directory, run:

```sh
sha256sum -c SHA256SUMS
python -O check.py | diff - CHECKS.txt
```

The standard-library verifier uses rational arithmetic for sample profile checks, a rigorous interval for the explicit welfare gain, and finite checks of the affine-reciprocal identity. The proofs, not those finite samples, cover the continuous model.
