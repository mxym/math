# Unbounded prime support with low-rank approximate multipliers

Only the ordinary integer N is given. At each bit length L, a fixed efficient public rule lists positive rational slopes at least 1. Their multiplicative rank is bounded by a fixed h, but no basis, valuation vectors or prime factorizations of the slopes are supplied. Join distinct prime divisors p<q if |q−mp|≤L^c for some listed slope m, where c≥0 is fixed. The error need not be known and may be rational.

**Result.** For connected support the full prime-power decomposition is recoverable in deterministic polynomial bit time, and class membership can be decided. There is no fixed bound on the number of distinct primes or on their multiplicities. The approach enumerates only the possible aggregate multiplicative scale, not a prime graph, a tree shape or a multiplicity pattern.

The key points are a polynomial bound on distinct short products in the public multiplicative group, a bound on how local errors accumulate even along a path with a growing number of edges, and exact recovery of the rest of a connected component once one prime is available. The rank is a global hypothesis on the dictionary, not a hidden condition inferred from N. The running time is a theorem rather than a practical recommendation; the word ball can be very large.

This remains a thin class, not general factoring. With at least two distinct primes it has fewer than X/(log X)^J members up to a constant for each fixed J>0, even without the low-rank requirement. Conversely it includes, unconditionally, examples with arbitrarily many primes, all much larger than a polynomial in L. That latter example uses ordinary short intervals and is not itself an algorithmic novelty.

See PROOF.md, UPSTREAM.md and RESULTS.txt. The two finite Python 3 checkers accept no data or targets: `python3 -B verify_word_ball.py` and `python3 -B verify_graph.py`. SHA256SUMS covers the other six files.
