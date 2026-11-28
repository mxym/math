# Deterministic factoring from a known group exponent: an unconditional Burgess bound

Let \(N>1\) be an integer, put \(R=\operatorname{rad}(N)\), and let
\(E\) be an even positive multiple of \(\lambda(N)\), with
\(\log E=(\log N)^{O(1)}\).

**Complete-factor theorem.** For every fixed \(\varepsilon>0\), \(N\)
can be completely factored deterministically in
\[
 R^{1/(4\sqrt e)+\varepsilon}
 (\log N+\log E)^{O_\varepsilon(1)}
\]
bit operations. The algorithm does not need to know \(R\); this is a
stopping-time bound. In particular it implies the weaker
\(N^{1/(4\sqrt e)+\varepsilon}\) bound for arbitrary inputs.

**Exact-\(\lambda\) first-split theorem.** If \(N\) is an odd composite
squarefree integer and the supplied value is the exact \(\lambda(N)\),
a nontrivial factor is found deterministically in
\[
 N^{1/(6\sqrt e)+\varepsilon}(\log N)^{O_\varepsilon(1)}
\]
bit operations. This smaller exponent is only claimed for the first
split. It uses polynomial exact-\(\lambda\) algorithms for semiprimes
and for a prime factor larger than \(\sqrt N\); the remaining cases
need only quadratic characters of conductor at most \(N^{2/3}\).

The proof combines the standard Miller/Rabin square chain with the
unconditional theorem of Lau--Wu on the least character nonresidue for
a cube-free modulus. The character is used only in the correctness
proof: the algorithm scans ordinary integer bases and validates gcds.
No factor, conductor, or character is supplied to it.

These are worst-case arithmetic-advice bounds. They do not give
ordinary deterministic polynomial-time factoring. No absolute
priority is claimed for this synthesis.

See [PROOF.md](PROOF.md) and [UPSTREAM.md](UPSTREAM.md). Run
python3 verify.py for finite exact checks of the splitting lemma and
the quadratic-character cases.
