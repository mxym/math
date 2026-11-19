# The locations and shapes of the largest empty sample polytopes

Yongxian Zhang · AI-assisted research note · 19 November 2026

Take independent uniform points in a fixed convex body in dimension at least two. Among empty polytopes whose vertices are sample points, record both the volume and the actual unordered vertex locations. For any fixed finite set of permitted vertex counts, the centered extreme-volume processes converge jointly to **independent marked Poisson processes**, one for each count. The earlier [one-count result](../empty-sample-polytopes-gumbel/README.md) does not identify this joint law or these locations.

For the largest empty simplex the description is geometric: first choose an affine hyperplane, biased by its section area to the power of the ambient dimension plus one. The limiting vertices are independent uniform points of that section, viewed without labels. Their joint configuration is independent of the limiting centered volume. This describes the vertices in the physical body, not an affine rescaling that preserves the simplex's thickness. No result is claimed for growing or unrestricted numbers of vertices.

The [proof](PROOF.md) uses the local estimates from the earlier paper and a descending-order Palm argument. The [source comparison](SOURCES.md) distinguishes previous unmarked section integrals and general Poisson approximation from the marked law. The initial derivation was developed with an AI research assistant and checked in a separate [internal AI review](REVIEW.md). This is not external peer review or a claim of established priority.
