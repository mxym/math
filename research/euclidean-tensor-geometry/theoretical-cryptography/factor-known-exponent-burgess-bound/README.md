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

**Short-multiple first-split profile.** Suppose \(N\) is odd,
\(k=\omega(N)\ge3\), and the supplied \(E<N\) is any positive multiple
of \(\lambda(N)\). Put
\[
 \tau=\frac{\log E}{\log N}.
\]
A nontrivial factor is found deterministically in
\[
 N^{\frac1{4\sqrt e}\max\{(1+\tau)/4,\,2/k\}+\varepsilon}
 (\log N+\log E)^{O_\varepsilon(1)}
\]
bit operations. Neither squarefreeness nor exactness of \(E\) is
required, and the algorithm need not know \(k\).

For exact \(E=\lambda(N)\), one always has \(E<N\). Prime powers and
inputs with at most two distinct odd primes are already polynomial by
the pinned exact-\(\lambda\) algorithm. Thus every remaining exact-
\(\lambda\) input admits the coarser
\(N^{1/(6\sqrt e)+\varepsilon}\) first split; when \(k\ge4\), this
improves to \(N^{1/(8\sqrt e)+\varepsilon}\). These smaller exponents
are only claimed for the first split.

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
