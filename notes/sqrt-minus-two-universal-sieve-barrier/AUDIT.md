# Mathematical dependency and exact arithmetic audit

8 October 2026. Model-assisted mathematical self-review, not an
external referee report or worldwide priority verification.

## Certified inputs and infinite implications

1. **Universal sieve reduction (written lemma).** For any finite
   principal generator set in the quadratic ring, take its
   scalar period Q. The norm of every generator divides Q²,
   so every multiple of that generator has norm divisible by
   a rational prime dividing Q. Thus *every* norm-coprime
   point survives the entire sieve. A connected finite pattern
   that can be translated off all norm-zero classes modulo
   every prime then survives any finite Q by the coordinatewise
   CRT. The lemma is stated more generally for integer-rank
   normed domains; no actual simultaneous prime elements are
   asserted.
2. **All large rational primes (traditional proof).** For a
   pattern S of m points, every prime p>m has a successful
   translation under N=a²+2b². At an inert odd prime the
   norm-zero set is one point, so at most m translations fail.
   At a split odd prime the zero set is two distinct lines;
   each linear projection contains at most m<p residues,
   and an invertible 2-by-2 map independently selects two
   missing projected residues. Prime two is included in the
   finite witness scope. This argument covers infinitely
   many primes and is not an extrapolation from the checker.
3. **Small-prime finite evidence.** The exact 197-point
   configuration (integer coordinate bounds 369..413 and
   -34..34) is connected under all fourteen differences.
   Every one of the **45** primes p<=197 has a pinned local
   integer shift leaving N nonzero modulo p for **all 197**
   vertices. `code/check.py` proves the literal claims; a
   second program independently checks all 45 local
   split/inert projection conditions without consulting the
   shift table. They agree: one ramified, twenty split,
   twenty-four inert primes.
4. **Method interval (precise predecessor dependency).** The
   parent [241-sieve proof](../sqrt-minus-two-prime-bound-241/paper.md)
   explicitly constructs one finite principal-ideal sieve whose
   entire allowed infinite lattice has component maximum 241,
   certified using a complete 1122-period partition and
   layered congruence refinement. The universal 197 bound
   applies to *that* and every other finite principal-ideal
   sieve. It does **not** constrain the actual prime-only
   graph from below, whose established interval remains
   [90,241].

## Exact reproduction

```sh
python3 code/check.py
python3 -O code/check.py
python3 code/check_projection.py
python3 -O code/check_projection.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The checkers use only Python standard-library exact integers;
all proof decisions are explicit exceptions rather than
`assert`, so `-O` does not disable them. The two checkers use
**distinct approaches**, literal shifts versus projected residue
images. `code/generate_local_shifts.py` is discovery-only,
never imported by the verifier. Tamper tests intentionally
introduce duplicate or deleted vertices, omitted or composite
prime indices, and an invalid shift modulo 19.

## Trust boundary and open questions

The CRT, norm-divisibility and split/inert linear algebra are
full traditional mathematical arguments, **not** Lean-certified.
Correctness of the exact Python kernel is the computational
trust assumption. The 197 vertex shape is a feasible
universally norm-admissible pattern, not a proved maximum over
all such shapes. The true minimum obtainable by this finite
principal-ideal sieve method may lie strictly between 197 and
241; the actual irreducible-only component maximum is a
**different** open problem. External human referee review and
systematic novelty comparison remain outstanding; no priority
claim is made.
