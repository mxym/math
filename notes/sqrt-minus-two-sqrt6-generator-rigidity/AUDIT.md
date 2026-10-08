# Exact proof audit: optimal period-1122 generator classification

Date: 8 October 2026. Model-assisted mathematical self-review; not an
external referee or mathematical priority determination.

## Dependencies and proof closures

1. **Previously proved inputs.** The preceding note proves that
   1122 is the least successful scalar period for the 14-step
   graph, using 682 negative period witnesses, and that all
   seven primes over 2,3,11,17 yield a successful complete
   positive 204800-point quotient partition. These existing
   exact proof packages are cited, not silently assumed to be
   additional work by this addendum.
2. **General all-composites reduction.** In any UFD with
   `Q ~ product(pi_i^e_i)`, a generator h of period dividing Q
   actually divides Q. If the ideal `(pi_i)` is missing from
   the literal generator list, `(h)` lies inside either one of
   the other `(pi_j)` or `(pi_i²)` (if repeated). Hence all
   possibly composite and redundant generators are dominated
   by a single maximal omitted-prime sieve. This is an
   infinite quantifier argument proved in Lemma 2 of the paper.
3. **All relevant failed cases.** Exactly seven primes occur in
   the factorization of 1122; all have exponent one except
   `t=sqrt(-2)`, with exponent two. Therefore the seven
   omitted-prime lists plus the repeated ramified-square
   replacement form a complete finite family of eight witnesses.
   The independent checker validates every step of each path
   by exact two-coordinate quadratic-ring divisibility
   in `Z[sqrt(-2)]`, checks the entire exhaustive index set,
   and verifies nonzero final displacement modulo 1122.
4. **Infinite graph proof.** Every maximal omitted-prime
   sieve is 1122-periodic. Concatenating the corresponding
   verified nonzero-voltage path with its translates gives an
   infinite component. Since arbitrary sieve allowed points
   include those of the relevant maximal negative sieve,
   the missing prime list cannot succeed. This implication is
   supplied as written mathematics, independent of the checker.

## Reproduction and trust boundary

```sh
python3 code/check.py
python3 -O code/check.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The untrusted producer `code/generate.py` deterministically
reconstructs `code/obstructions.json` (byte-identity independently
observed), but the checker never invokes or imports it. The
certificate format contains **literal paths**, not Boolean solver
flags. Python standard-library integers are used throughout;
all failure conditions raise explicit `ValueError` and are not
disabled by Python `-O`. The mutation suite corrupts the
omission family and steps, requiring rejection.

Analytic input trust remains the written UFD proof, the
combinatorial containment lemma, and elementary translation
periodicity. The result is not yet proved in Lean and has not
undergone human referee review or a comprehensive literature
comparison. No priority assertion is made.
