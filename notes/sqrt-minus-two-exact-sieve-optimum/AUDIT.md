# Proof audit and exact trust boundary

8 October 2026. Internal model-assisted correctness audit; not external peer review.

## Logical proof dependencies

1. **Lower bound 197.** The [universal 197-point obstruction](../sqrt-minus-two-universal-sieve-barrier/paper.md) gives an explicit connected lattice shape universally norm-admissible for every rational prime. The predecessor verifies all 45 primes up to 197 with two independent implementations, and proves every larger rational prime admits a translation via an algebraic split/inert residue argument. A general norm-divisibility/CRT lemma shows every finite principal-ideal sieve leaves a connected translate of this shape. This proves the **method lower bound**, not a 197-element prime graph.
2. **Inherited complete partition.** The [period-1122 paper](../sqrt-minus-two-sqrt6-period/paper.md) supplies a complete, closed, connected partition of 204,800 allowed residue representatives in 6,688 pieces, with all infinite lifts justified by a written periodic-component lemma. The new checker checks the immutable SHA256 hash of that parent partition and its exceptional 92-point closure before using them.
3. **New finite upper bound.** A written iterative congruence lemma reduces all translations of the parent pieces to mixed-radix shifts for 19, 5, 41, 43, 59, 67, pruning only connected pieces at most 197. `code/check_exact.py` independently forms literal integer-neighbor graphs and traverses every still-large piece for all required shifts. It verifies all exact per-stage shift counts, oversized-component counts and maxima, ending with no piece above 197 and an attaining piece of size exactly 197. The verifier uses no floating point, solver or random search.
4. **Prime-only transfer.** Every irreducible whose norm has a prime factor among 2,3,5,11,17,19,41,43,59,67 is associate to one of the complete listed prime ideals. The checker independently verifies the modular norm-divisibility equivalence for all square residues at each of the six new primes, and tests all 22 new associates lie in the pinned predecessor's 90-prime closed component. Therefore every other irreducible component lies inside the refined 197-bounded allowed lattice.
5. **Two optimization equalities.** The lower 197 pattern and upper 197 sieve imply the finite principal-ideal sieve optimum is 197. If a universally norm-admissible connected pattern of more than 197 vertices existed, CRT would translate it inside this same 197-bounded sieve, contradiction. Thus the maximum size of *universally norm-admissible connected patterns* also equals 197. Neither equality asserts the actual irreducible-only graph has a component of size 197.

## How to replay

```sh
python3 code/check_exact.py
python3 -O code/check_exact.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

No third-party dependency; standard-library Python integers only. The verifier does not import a generator and does not accept a stored success flag. It validates the expected full counts as well as the upper-bound predicate directly. The negative controls tamper with a parent hash, omit an exceptional point, duplicate a graph vertex and demand final-stage rejection. `-O` cannot disable proof checks because they raise explicit exceptions.

## Scope and open work

The exact optimum 197 concerns **finite principal-ideal sieve allowed graphs**, rather than actual simultaneous irreducibility of the 197 pattern. For the true irreducible-only graph, the proven interval is only [90,197]. Exact determination may require actual prime-value existence/exclusion arguments beyond finite congruence sieves. Full Lean formalization, independent human referee review and worldwide literature novelty assessment remain outstanding.
