# Mathematical review and exact-proof scope

Date: 8 October 2026. Internal model-assisted review; not human
referee certification or mathematical priority assessment.

## Independently checkable mathematical dependencies

1. **Integral geometry and unique factorization.** With `t^2=-2`,
   `N(a+bt)=a^2+2b^2`. Coefficient rounding proves the norm Euclidean
   inequality `N(remainder) <= 3 N(divisor)/4`. The ring is a UFD,
   with only `+-1` as units. We derive the literal two-coordinate
   divisibility test rather than using an opaque computer algebra API.
2. **Complete exceptional-prime classification.** The ramified factor
   `t` divides exactly the elements with even first coefficient.
   Factors `1+t` and `1-t` divide precisely the congruence classes
   `a-b=0` and `a+b=0` modulo three. Every irreducible with norm
   divisible by 2 or 3 is one of the six associates of these three
   factors. Direct finite neighboring-point inspection gives two
   3-vertex closed prime components, and the proof handles every
   other vertex with the mod-6 congruence classes, without a spatial
   cutoff.
3. **Natural Euclidean radius.** The complete nonzero steps of
   squared norm below four are exactly norm 1, 2 and 3, and together
   comprise the eight coefficient neighbors. The parity restriction
   rules out new prime edges at norm three. The two exceptional
   triples already exist at norm-one steps.
4. **Smaller-period obstruction.** Every generator of scalar period
   Q divides Q. Its ideal removes no vertex with `gcd(N,Q)=1`.
   Four explicit vertical lines and one explicit 3-step repeat show
   an infinite allowed walk for every Q in 1,...,5. The supplied
   finite paths give an equivalent replayable witness for each Q.
5. **Optimal sieve classification.** A scalar-period-six generator
   divides `6` and is among the eleven ideals indexed by factors of
   `t^2*(1+t)*(1-t)`. Three positive minimal lists are proved
   with finite complete quotient decompositions. Any other list is a
   subset of one of four stated maximal failing ideal collections.
   Each maximal failure has a nonzero-translation walk in its allowed
   lattice; the checker tests every intermediate vertex against all
   nine remaining ideals. Universal containment finishes the proof.

## Exact computational reproduction

From the directory with this AUDIT.md:

```sh
python3 code/check_exact.py
python3 -O code/check_exact.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The checker verifies all 12 finite certificates independently of
`code/produce.py`. It also computes the quotient criterion for all
2,048 ideal subsets, retaining 896 successful ones, as a **redundant
cross-check** rather than an imported mathematical oracle.
The mutation suite corrupts positive partitions and negative walks,
verifies failure, and independently checks small irreducibility cases.
Checks use integers, exact divisibility, explicit exceptions (not
Python `assert`), no floating-point inequalities, random experiments
or external solvers.

**Trust boundary:** The elementary algebra, factorization,
combinatorial subset reduction, and infinite periodic-lift implications
are supplied as written proofs in `paper.md`; they have not been
machine-formalized. The Python runtime and hardware remain the usual
computational trust assumptions. The tests do not replace external
human review or priority determination.

## Related work and exclusions

The Gaussian moat strategy is credited to OpenAI/math result 028
(pinned publicly at `adc7f12`). The quadratic-order framework is
in manuscript 002 v3 and the analogous sharp Gaussian and real-
quadratic period results in 002 v4. Earlier work such as Prasad's
*Walks on Primes in Imaginary Quadratic Fields* (2014,
arXiv:1412.2310) and the 2026 finite-radius numerical paper by
Bandara provides related context. No claim of first proof or
novelty certification is made.

This note classifies only the small-radius graph `D<2` of
`Z[sqrt(-2)]`, and finite principal-ideal sieves of optimal scalar
period for the specified eight-neighbor steps. It does not determine
sharp component counts at radius two or beyond, nor provide a new
solution of the arbitrary-radius Gaussian moat question.
