# Two audited avoidance and covering refinements

These source-complete AI-assisted research notes extend two different arguments. Each has a complete proof, editable source, a PDF, and an independent model-conducted mathematical audit.

1. [Bounded cluster avoidance for uncountable selector families](bounded-cluster-avoidance/README.md). A routing blocker puts an entire bounded finite cluster in the small open complement, thereby excluding every pointwise selector at once. The positive logarithmic upper Banach density and countable prescribed null-modulus assumptions remain essential. The added finite-alphabet/profile corollary permits arbitrary uncountable switching families.
2. [Arbitrarily slow critical covering excess in Banach nonembedding obstructions](critical-covering-gauge/README.md). For every finite-valued nondecreasing gauge h:[1,infinity)->[1,infinity) with h(t)->infinity, every infinite-dimensional real Banach space contains a countable compact subset with upper box dimension zero, Assouad dimension exactly two, and no bi-Lipschitz embedding into any finite-dimensional real normed space. Its critical exponent-two excess is unbounded and bounded above by the prescribed h, up to a universal factor.

The profile-family dimension in the first note and the metric-space dimensions in the second are dimensions of different objects. Neither substitutes for logarithmic density.

[Pinned provenance and source snapshots](avoidance-covering-provenance/README.md) credit the OpenAI 084 routing engine and OpenAI 098 sheet-crossing obstruction, together with mxym entries 003, 004, and 006. The preceding entries are not changed by these notes. Finite computations certify the displayed finite examples only. These notes make no human-peer-review, formal-verification, universal C1-avoidance, minimal-dimension, or literature-priority claim.

To reproduce: run `python3 notes/avoidance-covering-provenance/verify.py`, then `bash notes/avoidance-covering-provenance/build.sh` from the root of the extracted package. The public manifest lists the exact permitted files and their hashes.
