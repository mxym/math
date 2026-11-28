# Bare-integer factorization on one or two hidden prime-relation blocks

Let the fixed public rule for bit length L list polynomially many positive labels m, in deterministic polynomial bit time. On the distinct prime divisors of N join p and q whenever q=mp+1 for a listed m (ignore direction when taking components). The graph, its primes, labels actually used and all multiplicities are unknown. With at most a fixed number k of distinct primes, there is a deterministic bit-polynomial recognition and factorization algorithm for the union of the following classes:

* the graph is connected;
* it has exactly two components, and the two minimum primes differ by at most L^c times the square root of the smaller one, for fixed nonnegative integer c.

Only N is supplied. No totient, group exponent, auxiliary factorization or approximate root is supplied. Multiplicities need not be fixed. The connected case is an elementary one-parameter baseline. The substantive extension is the second case: two unknown rational-affine templates can differ in shape, coefficients and multiplicities. Following a spanning tree from a component minimum controls every normalized affine offset even on reversed edges with very large labels. This turns a shifted weighted AM–GM inequality into a polynomially short list for the integer weighted sum of the two minima. Neither Fermat's method, weighted AM–GM, prime chains nor univariate elimination is new.

These are thin promise classes. For fixed exactly s≥2 distinct primes the respective counts up to X are at most X^(1/s) and X^(3/(2s)), each times a polylogarithm, not density or general factoring improvements. No existence of unbounded simultaneous prime patterns or priority beyond the comparisons in UPSTREAM.md is asserted.

See PROOF.md for the complete argument. The scripts are finite certificate/replay tests of toy mathematical data, not a general-purpose factoring implementation. Run `python3 -B verify_shapes.py` and `python3 -B verify_center.py` from this directory. Neither takes arguments, needs data, or uses third-party packages. RESULTS.txt records their outputs; SHA256SUMS covers the other six files.
