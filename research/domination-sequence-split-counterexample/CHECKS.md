# Exact reproduction

Use Python 3.10+ (standard library). Run from this directory:

```sh
python3 -B -O verify.py
python3 -B independent.py
sha256sum -c SHA256SUMS
```

The first script uses explicit failure checks; the second uses assertions and rejects optimized mode. Neither script constructs the graph at order $2^{40}$ or evaluates its gigantic coefficients. The rigorous large-graph conclusion comes from [the finite mass argument](PROOF.md).

## Original derivation checks

The first script checks the group probabilities, means, variance proxy, exponent comparisons, integer windows, and optionally reusable representation of the field through a degree-40 irreducible polynomial. It verifies the two incidence bounds in both orientations over the order-2 and order-3 prime fields, and for each clique subset of a 20-vertex model it compares the formula for the number of extensions of every size with direct graph enumeration.

```text
q, N: 1099511627776 7975367974726420198897447170127953920
three closed integer windows: [(3987683987363834351322840067688416013, 3987683987363909909186565982011835148), (3987683987364035838959442505884200375, 3987683987364111396823168420207619510), (3987683987364237326596044944079984738, 3987683987364312884459770858403403873)]
two-sided cut checks at q=2,3: 523744
one-site toy exact subset classifications (ordinary,total,connected): [((False, False, False), 151259), ((True, False, False), 119141), ((True, True, True), 778176)]
```

## Independent check

The second script separately derives constrained-group moments by counting nonempty bit patterns, checks the constants with rational arithmetic, and compares the full polynomial histogram of the 20-vertex model against independent adjacency/reachability enumeration. Its incidence tests count only nonempty subsets on both sides in one orientation, so their total differs from the first script's. The miniature itself is not a counterexample.

```text
N = 7975367974726420198897447170127953920 ; exact phase mass = 63/128 per base position; shifts = 23/42 37/42
conditional group variances = 608/441 412/441 ; exact integer window sizes = [75557863725914323419136, 75557863725914323419136, 75557863725914323419136]
direct finite-field nonempty subset-pair incidence checks: 261346
all 1048576 direct adjacency subsets checked; phase masses [516096, 516096] ; ordinary/total/connected totals 897317 778176 778176
size histogram for ordinary domination: [0, 0, 6, 105, 1047, 5775, 20337, 50781, 95708, 141111, 166132, 157959, 121890, 76296, 38505, 15471, 4843, 1140, 190, 20, 1]
```
