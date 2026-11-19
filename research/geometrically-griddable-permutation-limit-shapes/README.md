# Limit shapes in geometrically griddable permutation classes

Take a uniformly random permutation of length $n$ in an infinite hereditary subclass of any fixed geometric grid class. Its plot, scaled to the unit square with uniform marginals (a permuton), converges in distribution **along the full sequence**. The grid lines are not part of the sampled object.

The limiting law can be described by a finite mixture. Choose a route through a finite graph. Its dominant components receive random durations uniform on a simplex; within each phase a finite matrix determines the frequencies of the cells. Converting the resulting frequencies to position and value ranks gives the limit. Given the route and durations, the mass is uniform along each of finitely many straight segment pieces. The *law* need not be deterministic: in the union of the increasing and decreasing classes, the two diagonals occur with equal probabilities.

[Proof](SHAPES.md) · [Prior work and a gridding example](SOURCES.md) · [Independent internal proof review](REVIEW.md)

The canonical gridding is inherited from Albert, Atkinson, Bouvel, Ruškuc and Vatter. The new argument tracks local witnesses against canonicity so that every productive component with a cycle has period one. Merely counting each possible gridding would sample the wrong law. In particular, this is not a consequence of a speed-$n$ large-deviation principle when more than one limiting shape is possible.

For the finite checks, run `python3 -BO check.py` and compare with [CHECKS.txt](CHECKS.txt). Run `sha256sum -c SHA256SUMS` for file integrity. These checks test exact finite identities, not the limiting theorems.

This research note was developed with AI assistance and received a separate internal AI mathematical review, not external peer review. It makes no claim of guaranteed priority.
