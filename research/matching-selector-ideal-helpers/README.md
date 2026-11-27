# Ideal helpers in matching-selector secret sharing

A matching-selector access structure authorizes a coalition when it contains
some helper and covers that helper's matching. For pairwise edge-disjoint
perfect matchings on m + m endpoints with r helpers, this note gives an exact
resource frontier when the helpers have the minimum possible entropy.

If the secret alphabet has D elements and all helpers are ideal (entropy
log2 D), each endpoint needs at least r symbols' worth of entropy, even
conditioned on all other endpoints on its side. Every positive-probability
conditional law also has maximum atom at most D^(-r). The minimum total
share entropy is (2m+1)r log2 D, and the minimum private dealer-tape
Shannon entropy and min-entropy are both mr log2 D. A standard monotone
formula construction attains them simultaneously. The converse does not
assume a linear scheme. The note also gives an explicit lower bound when
helper entropies are larger, including unequal excesses.

This complements Williamson, arXiv:2608.17047v1, whose cyclic matching
structure is a special case. His unrestricted share lower bound and our
minimum-helper regime are different. No unrestricted optimum, active
adversary model, or security attack is claimed.

Run `sh replay.sh` with Python 3 and GNU-compatible sha256sum. The exact
probability and independent rank verifiers are separate finite checks;
the proof covers all parameter values without relying on them.
