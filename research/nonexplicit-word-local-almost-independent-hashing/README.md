# Optimal nonexplicit locality for almost k-wise independent hashing

**Existence in the word-probe model, not an explicit construction.** For equal n-bit inputs and outputs, 2≤n≤k≤2^n, word width w, and statistical error 2^(-n) against k adaptive input queries, the optimal number of key words read per evaluation at key size O(ceil(kn/w)) is

    Θ(max{1, n/w, n / sqrt(w log₂(2+kn/w))}).

The construction is existential in the cell-probe model. Its fixed map catalog can be exponentially large, and no polynomial-time evaluator or explicit construction is claimed. For example, w=n and n≤k≤poly(n) gives Θ(sqrt(n/log n)); w of order log n with polynomial k≥n gives Θ(n/log n). The lower bound holds even for selective input queries and arbitrary key-adaptive word access. We also prove a selective lower bound when some whole access pattern has probability at least twice the error, showing an address-entropy distinction between static access and the existential optimum.

This is an existential counterpart to the explicit locality gap in Dodis–Lovett–Wichs, ePrint 2026/622 §6. The common-union lower-bound method is theirs; the new upper bound uses full stacked rank instead of sequential fresh positions. The efficient construction question remains open here. The bit-local case already has optimal order, as the primary source recognizes. No protocol or implementation is tested.

See PROOF.md and SOURCES.md. Run: sh replay.sh | diff -u RESULTS.txt -
