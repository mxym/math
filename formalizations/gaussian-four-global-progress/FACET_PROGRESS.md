# Actual Gaussian facet charts and singular-limit continuity

**Unconditional partial formalization. The sharp four-cell global inequality
and its complete equality classification are not proved here.**

This checkpoint recovers the six previously uncommitted facet modules on top
of `e036ab2a5abb6ae7f39afcfd2da480f430de8f9d`, reviews their theorem types, and
reverifies all 96 owned modules in a new source tree. The original development
worktree is preserved. Its earlier logs are not presented as this new run.

## Proved statements and their objects

`AffineBoundary.lean` proves dominated convergence for integrals of the actual
Gaussian density over finite strict affine masks. A restricted inequality may
have zero linear part, provided its constant part is nonzero. The integral
uses the actual standard Gaussian measure, not a supplied probability model.

`TripleAffineExclusion.lean` proves that three nonempty strict winning cells
cannot have globally proportional affine score differences. Positive actual
Gaussian cell masses imply the required nonemptiness. `FacetChart.lean`
constructs the pairwise tie plane as a graph and proves that every other
competitor restricts to a nonzero affine function on that plane. This does
not assume affine independence of the inducing scores.

`FacetContinuity.lean` proves joint continuity of the Gaussian facet-chart
integral and its normal-coordinate-normalized weight in both scores and
prices at any valid chart of a positive-mass diagram. Rank-deficient limits,
zero linear parts with nonzero offsets, and disappearing facets are included.

`FacetGraphBridge.lean` identifies these integrals exactly with the existing
Gaussian graph-facet flux coefficients in a positive epigraph chart. When
the graph slopes are distinct, the actual vector-valued Bochner moment is
proved to equal the weighted sum of score differences. No moment/flux
identity is supplied as a hypothesis.

`FacetCoordinates.lean` constructs a fixed orthogonal chart for every
nonzero pair difference using a Householder reflection. Choosing the chart
at the limiting diagram, rather than postulating smoothly moving frames,
gives an actual continuous chart expression in a neighborhood of that limit.

Main entries:

```lean
GaussianFour.continuousAt_pairChartWeight
GaussianFour.actual_epigraph_moment_pairChart_flux
GaussianFour.exists_continuous_pair_chart_of_positive_masses
```

## Exact remaining boundary obligations

These chart expressions have not yet been globally identified with one
coordinate-independent Gaussian surface measure/perimeter. Full compatibility
between different pair charts, the arbitrary singular-cell flux identity,
and the complete limiting covariance/normal-cone argument remain. The
positive limiting masses used in the continuity theorem must still be
established in the intended global limiting construction. Thus this is not
claimed as a complete proof of manuscript Lemma 5 or of the global theorem.

## Source-bound verification

The new run `evidence/facet-continuity/local-r2/verification.json` started on
2026-10-10 at 23:46:31 UTC and finished at 23:50:49 UTC. It passed a clean Lake
build starting with zero owned objects, separate compilation of all 96
modules, and empty-kernel replay of 60,530 declarations for 583 roots at
trust level zero. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
All 11 deliberate Lean mutations were rejected. Five inventory regression
tests also passed. Literal logs and mutation sources are archived with SHA-256
hashes. The source hashes were checked again before publication.

Independent CI of this extension is pending at this source checkpoint; the
successful 90-module baseline is not counted as its independent verification.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. No external funding; AI-assisted research.
Existing licenses and third-party notices remain unchanged. Original additions
retain all rights not otherwise granted. No external peer review is claimed.
