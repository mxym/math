# Proof and certificate audit

Date: 7 October 2026. This record describes mathematical proof
dependencies and tests performed with AI assistance. It does not
represent external independent human peer review.

## Claims and exact proof interfaces

1. **Infinite-grid reduction.** Paper §2 gives Eisenstein
   multiplication/divisibility rules, the Euclidean-norm
   argument and exceptional-irreducible classification. Paper §4
   proves any principal-ideal sieve of scalar period Q contains
   the norm-coprime allowed grid V_rad(Q), and a nonzero
   translation walk implies an infinite component.
2. **Small-period exclusion.** Four compressed JSON chunks encode
   an explicit start point and ordered admissible path
   for each of 333 squarefree q in [1,545]. The checker proves
   complete index coverage (no omissions or duplicates), admissible
   vertices after *each* step, and final displacement a nonzero
   multiple of q. These are proofs, through a written lemma, for
   each of 333 infinite-component obstructions.
3. **Positive-period partition.** The five endpoint compressed files
   encode complete sets of lifted integer points modulo 546. The
   checker independently enumerates every residue in the 546²
   square and tests unique coverage of allowed classes, eight-neighbor
   closure in the infinite grid, and connectivity within each set.
   Paper §5 proves these hypotheses imply finite bounds for every
   lift and classify the four successful prime-generator lists.
   A separate composite-rigidity proof then excludes all other
   four-generator lists, even those allowing composite elements.
4. **Actual irreducible-component maxima.** The two exceptional
   closure files encode the full finite closure of every exceptional
   irreducible. The checker reconstructs exceptions from generator
   associates, checks literal neighbor closure and reachability, and
   tests irreducibility using exact norm-bounded divisor enumeration.
   Paper §6 shows any other irreducible component lies within an
   allowed-sieve component, giving **global** exact maxima.
5. **Composite rigidity.** The 36 compressed nonzero-voltage
   walks in the composite-replacement bundle cover all four
   successful prime lists, four replacement positions, two
   unused prime factors, and the one repeated ramified factor.
   There are nine cases per prime list: eight unused-factor
   replacements and one repeated ramified-prime replacement.
   The independent checker tests every intermediate vertex
   against the **literal product ideal** using integer division,
   validates the exact case set, and checks nonzero displacement
   modulo 546. Paper §5 reduces every composite four-generator
   candidate to one of these walks or a redundant ideal.
6. **Algebraic cross-check.** For **all 298,116** residue pairs
   modulo 546, the checker compares six modular principal-ideal
   predicates with the exact two-coordinate divisibility criterion,
   and compares the full mask with gcd(N,546)=1.
7. **Analytic hexagons.** Paper §3 proves the six-step periodic
   hexagonal decomposition directly by subgroup index and
   degree-two counting. The checker covers all 36 residues modulo
   six and tests their closure and connectivity.

## Commands and expected results

From this directory:

    python3 code/check.py
    python3 -O code/check.py
    python3 code/self_test.py
    python3 -O code/self_test.py
    sha256sum -c SHA256SUMS

Python standard library only. Main checker uses explicit exceptions,
never language assertions: optimization mode never disables a
verification. The tamper tests deliberately corrupt in-memory negative
walks, an endpoint component, and an exceptional closure, requiring
rejection. The irreducibility test also checks small primes, a
composite, and zero.

Producer commands, **for discovery/rebuilding only**:

    python3 code/generate.py --lower-start 1 --lower-end 180
    python3 code/generate.py --lower-start 181 --lower-end 350
    python3 code/generate.py --lower-start 351 --lower-end 455
    python3 code/generate.py --lower-start 456 --lower-end 545
    python3 code/generate.py --endpoints --closures
    python3 code/generate_composite.py

The checker must pass against committed raw witness data regardless
of whether the generator can be executed. The generator is not an
independent theorem prover.

## Boundaries and work not claimed

The eight-step scalar-period result optimizes within **finite
principal-ideal periodic sieves**, not nonperiodic blocking
strategies. The exact **four-generator classification** now covers composite
generators as well, via prime replacement and the 36 separately
checked composite-rigidity paths. The **two-generator six-step
classification** also covers composites by an explicit horizontal
line obstruction. No classification is claimed for successful
lists using more than the minimum number of generators.
The note treats only the specified two step sets and Eisenstein
integers, not every quadratic order. It does not replace
entry 002 v3's general existence argument. Finite arithmetic is exactly
replayable but analytic arguments are written rather than Lean kernel
checked; systematic literature matching and external referee review
remain outstanding.
