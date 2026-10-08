# Exact universal finite principal-sieve optimum: 197

Research note, 8 October 2026. [Complete theorem and proof](paper.md) · [independent six-stage integer checker](code/check_exact.py) · [negative controls](code/self_test.py) · [proof audit](AUDIT.md) · [replay log](results/replay.txt).

For the actual fourteen Euclidean steps of squared norm at most six in the quadratic integer ring `Z[sqrt(-2)]`, this note **completes the exact optimization over every finite principal-ideal sieve**. Write `M` for the infimum, over all successful finite principal-ideal generator lists, of the largest connected component in the complete allowed lattice graph. Then

\[
\boxed{M=197.}
\]

The lower bound uses the [separately published universal 197-point admissible connected pattern](../sqrt-minus-two-universal-sieve-barrier/README.md). The matching constructive upper bound is an explicit sieve with 18 prime-element generators over the rational primes 2, 3, 5, 11, 17, 19, 41, 43, 59 and 67. Its period is 742840526010, but no astronomical quotient grid is enumerated.

Instead, the independent integer checker reuses the already certified [complete period-1122 partition](../sqrt-minus-two-sqrt6-period/README.md) and refines all relevant finite components through **six exhaustive congruence levels**:

| Added rational prime | Largest refined component | Remaining components exceeding 197 |
| ---: | ---: | ---: |
| 19 | 298 | 140 |
| 5 | 241 | 12 |
| 41 | 217 | 36 |
| 43 | 205 | 20 |
| 59 | 201 | 12 |
| 67 | **197** | **0** |

The same computation, combined with the certified 90-prime exceptional component, proves for **the actual irreducible-only graph**:

\[
\boxed{90\le B_D\le197},\qquad \sqrt6\le D<\sqrt8.
\]

**These are different problems.** The sieve optimum is now proved exactly. The maximum connected component consisting exclusively of irreducibles has **not** been proved to be 197 (or 90); exact determination of that number remains open in this work. The universally admissible 197-point pattern does *not* imply existence of 197 simultaneously irreducible elements.

## Exact reproduction

From this directory, with Python 3 and no extra packages:

```sh
python3 code/check_exact.py
python3 -O code/check_exact.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The complete check is deterministic exact integer arithmetic. It loads the **SHA256-pinned, previously independently certified** 204,800-point quotient partition and 92-point exceptional closure from the adjacent predecessor note; it does not call or trust a search solver or producer. A complete run recomputes every relevant component and mixed-radix translation and rejects any final piece exceeding 197. Mutation controls reject altered parent hashes and invalid closure/connectivity cases. A separate count-verifying all-primes local-pattern checker provides the matching 197 lower bound.

For machine-to-machine auditing, the checker also accepts `--part i --parts 4` for each `i=0,1,2,3`, partitioning the original components without omitting any parent components. The unpartitioned run checks all totals against expected exact integers.

## Scope and attribution

This is an additive continuation of the independent [sharp period-1122 theorem](../sqrt-minus-two-sqrt6-period/README.md), [seven-generator uniqueness theorem](../sqrt-minus-two-sqrt6-generator-rigidity/README.md), [241-prime bound](../sqrt-minus-two-prime-bound-241/README.md) and [universal 197-obstruction theorem](../sqrt-minus-two-universal-sieve-barrier/README.md). The periodic sieve approach is motivated by OpenAI/math result family 028 (pinned upstream at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`). Earlier manuscripts are not modified. No claim of mathematical first priority, full literature review, external refereeing or Lean kernel formalization is made.
