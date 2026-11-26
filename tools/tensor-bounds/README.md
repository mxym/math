# Tensor bounds workbench

Research tooling only. This is neither a paper release nor a universal solver. It searches and replays exact lower-bound certificates for log-weighted graph tensors. It is deliberately small (2–10 vertices, Python standard library).

## Use

```sh
python3 tensor_bounds.py search c5.json --depth 2 --states 512 > report.json
python3 tensor_bounds.py verify c5.json report.json
python3 -m unittest -v
```

The JSON input has `vertices` and `edges`; an edge is `[u,v,weight]` with zero-based endpoints and positive integral or quoted rational log-weight. Repeated edges add. Arithmetic uses rational fractions. A weight with denominator `s` means work on the common scaled powers-of-two tensor and divide the base-two logarithmic exponent by that scale.

1. **Cut:** exhaust all two-part cuts and certify each by flattening rank.
2. **Quotient:** exhaust all three-part partitions. Contract internal edge factors to nonzero scalars and regard each whole part as one party. The remaining weighted triangle is rectangular matrix multiplication. Such certificates explicitly mark their dependence on the [pinned OpenAI exact rectangular exponent theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean#L45).
3. **Splice and quotient:** a local contraction at party b swaps matched bundles of edge digits from a–b and b–c into a bundle on a–c. Consume the same weight on both input edges and add that weight on the final one. The operation is a local restriction: in fact, in the contracted coordinates, apply a delta functional at b, which identifies the two edge labels. Residual digits on each edge are independent tensor factors. Replay verifies every such capacity change and the final partition.

Splice search is bounded by depth, states, and amounts. If it finds no improvement, this alone does not prove that none exists. A certificate proves a lower bound, not optimality or an upper bound. The verifier replays the arithmetic and the stated graph rules; it does not reprove the external theorem.

## Results on existing benchmarks

- **K5** reproduces max cut 6 and the known tight lower bound 25/4.
- **C5** reproduces max cut 4 and a three-part lower bound 49/12 using quotient weights (3,1,1). The search visits 16 graphs at the supplied settings and does not improve it. This is not a new C5 bound. The [Zhou upper bound](https://arxiv.org/html/2610.34273v3#S6.SS3) remains 25/6. See [the exact method-limit calculation](C5-method-limit.md) for why repeated path splices still cannot close that gap via this certificate family.

## Matching upper certificates

The search also tries a greedy upper certificate on the selected maximum cut. Route each within-side edge along even paths made entirely of crossing edges; allow splitting rational demand. If the total routed load is at most half of the weight on each crossing edge, the exponent equals the cut weight. This uses [Zhou's path-strengthened CP bound](https://arxiv.org/html/2610.34273v3#S5.SS3), not the rectangular theorem. A missing certificate means only that this greedy search did not find one. The verifier checks all demand totals and half-capacities exactly.

```sh
python3 tensor_bounds.py search weak-c5.json --depth 2 > weak-c5-report.json
python3 tensor_bounds.py verify weak-c5.json weak-c5-report.json
```

The half-weight edge in this example can be routed around the other four edges, giving both lower and upper bound 4. The same check works on every odd cycle with one edge weighing at most half of every other edge. The unweighted C5 does not meet this sufficient condition.
