# Uniform cancellation for sparse graph-orbit characters

Let H be an n-vertex graph with independent fair edge bits. For an edge set α, average the sign of the parity of α against πH+H over all vertex permutations π. We give a uniform high-probability bound on the magnitude for every nonempty edge set of size at most D, and for their complements. When D is polylogarithmic in n the bound tends to zero, uniformly; more generally it tends to zero for D=o(n/√log n) at any fixed inverse-polynomial failure rate. The proof uses the classical read-k inequality with an exact transitive orbit load.

This makes rigorous the sparse character-sum heuristic in Abram–Beimel–Ishai–Kushilevitz–Narayanan, ePrint 2023/1929, §4.3 following Eq. (3). AICR c/0084's all-nonzero-frequency version does not inherit the source's weight restriction: it is false because the full edge set has sign +1 for every H and every π. We classify all frequencies attaining magnitude exactly one, but do not infer cancellation for unrestricted frequencies after excluding the invariant ones.

This is a statement about graph parities, not a result about distinguishing planted instances, the source's low-degree advantage, or the security of its constructions. See PROOF.md and SOURCES.md. To reproduce the finite checks, run: sh replay.sh | diff -u RESULTS.txt -
