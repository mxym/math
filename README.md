# Infinite chromatic log-concavity for all \(K_{2,n}\)

For every \(n\ge1\), take the absolute coefficients of the chromatic polynomial of the complete bipartite graph \(K_{2,n}\). The first log-concavity transform, after deleting its initial zero, has \(n+1\) distinct negative real roots. By Brändén's preservation theorem, the absolute coefficients are therefore infinitely log-concave.

The [proof](FactorK2nInfiniteLogConcavity.md) treats all \(n\) using a separate analytic argument and two exact finite verifications. In the analytic range the three-term Jacobi expansion and an ODE energy comparison give \(n+2\) alternating signs. The smaller range uses exact integer evaluation at rational points, with the two verifiers proposing their points differently. [The source-slice notes](RELEASE_NOTES.md) distinguish this family from the conjecture for all graphs, and from the earlier result on wheels.

## Reproduce

Use ordinary Python 3.10 or later; both scripts are standalone.

```sh
sha256sum -c MANIFEST.sha256
python3 verify_factor_k2n_infinite_logconcavity.py
python3 -I -B verify_k2n_independent.py
```

No Lean formalization is claimed. This slice is solely about \(K_{2,n}\), not complete bipartite graphs with both parts of size at least three.
