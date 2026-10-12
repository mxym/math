# Four equal Gaussian cells: rank and stationary rigidity

**The global regular-tetrahedron conjecture remains unproved.**

The [complete written note](paper.md) proves:

- Every global maximizer in dimension at least three has moment rank three.
  This excludes all planar Laguerre partitions, including a bounded central cell.
- An origin-conical maximizer is necessarily the regular tetrahedron, by
  an elementary tetrahedron unfolding and exact facet comparison.
- The regular root is locally isolated among all nine-parameter full-rank
  equal-mass stationary solutions, up to rotations. A separate strictly
  negative Hessian proves local optimality for all measurable competitors
  with nearby normalized moments.

The unresolved global step is to exclude noncentral irregular tetrahedral
maximizers. The accompanying 56 numerical starting points provide
discovery data, not a proof or coverage certificate. See [audit](AUDIT.md)
and [prior-work comparison](PRIOR_WORK.md) for precise scope.

The [covariance route](GLOBAL_COVARIANCE_ROUTE.md) derives an exact
price-adjusted Hessian identity and proves that a specified global sign
inequality would imply the complete conjecture. That sign inequality
remains unproved. Its 500 floating covariance cases are discovery data;
they do not give interval enclosures or a coverage certificate.

`formal/Algebra.lean` partially formalizes five finite algebraic steps.
It does not formalize Gaussian variation, Gaussian isoperimetry, unfolding,
or the global analytic theorems. Fresh compilation and an empty-kernel
proof-closure replay are documented with pinned Lean 4.34.1/Mathlib inputs.

Run the exact diagnostic and package verifier:

```sh
python checks/exact.py
python verify.py
```

Fresh partial Lean replay (choose either a matching complete official
library cache or a dependency project with the pinned Lake revisions):

```sh
python formal/replay.py --lean /path/to/lean \
  --library-root /path/to/official-library-cache --output /tmp/four-lean-fresh
python formal/replay.py --lean /path/to/lean \
  --dependency-project /path/to/pinned-lake-project --output /tmp/four-lean-fresh-2
```

Typeset using the repository's pinned TeX helper:

```sh
python build.py --output /tmp/four-paper-fresh
```

Discovery only (NumPy and SciPy required, versions in the result metadata):

```sh
python discovery/stationary_search.py --starts 24 --spread .65 --seed 20261008 --output search.json
python discovery/stationary_search.py --starts 32 --spread 1.4 --seed 20261009 --output broad-search.json
OPENBLAS_NUM_THREADS=1 python discovery/covariance_probe.py --cases 200 --seed 20261012 --log-eigenvalue-min -8 --output covariance-200.json
OPENBLAS_NUM_THREADS=1 python discovery/covariance_probe.py --cases 300 --seed 20261012 --log-eigenvalue-min -10 --output covariance-300.json
OPENBLAS_NUM_THREADS=1 python discovery/covariance_diagnostic.py
```

No historical priority, exhaustive novelty search, external professional
review, or complete conjecture resolution is asserted.
