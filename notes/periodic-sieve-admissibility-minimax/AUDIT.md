# Mathematical self-audit: finite lattice-sieve minimax principle

Date: 8 October 2026. Model-assisted traditional-mathematics review. Not an external referee or historical priority assessment.

## Universally quantified theorem: no hidden number theory

**Data.** Integer dimension `d>=1`; fixed finite symmetric integer step set `F` with no zero step; for *each* rational prime `p`, arbitrary local allowed residues `U_p`. Neither positivity, periodic connectivity, a norm, nor any prime-value distribution is assumed.

**Forward implication.** For a finite connected pattern admissible modulo every rational prime, every finite prime sieve leaves a translate of it, using the usual coordinatewise CRT. Therefore the size of any universally admissible pattern is a lower bound on the allowed-component supremum of every finite sieve.

**Reverse implication.** For each fixed cardinality `k`, every connected shape with a chosen root at the origin fits inside a finite ball containing sums of at most `k-1` steps from `F`. Hence there are finitely many translation types. If no `k`-point shape is universally admissible, each of these finitely many types has at least one obstructing rational prime. Collect these obstruction primes into one finite sieve. Any component of at least `k` vertices would contain a connected `k`-subset, whose root-normalized shape would contradict one obstruction prime. This proves finite attainment and excludes the possibility of a hidden arbitrarily large component surviving all these finite checks.

**Boundary cases.** If no locally admissible singleton exists, the proof chooses `k=1` and a finite prime sieve of empty allowed set; both optima zero. If arbitrarily large universally admissible shapes exist, CRT gives unbounded components under every finite sieve. If `F` is empty, only singleton shapes are connected and the argument remains valid.

**Quantitative existence.** The finite sieve can be chosen with at most as many distinct prime conditions as the rooted connected shapes of size `A*+1`. This bound may be enormous and is not intended as an efficient algorithm for finding them.

## Principal-ideal corollary: specific assumptions audited

The ring is explicitly `R=Z[sqrt(-2)]`, norm `N(a,b)=a²+2b²`. Nearest-integer rounding proves norm Euclideanity and hence PID property. At ramified rational 2, the norm-zero ideal is `(sqrt(-2))`; at an odd inert prime, it is `(p)`; at an odd split prime, the two factors are the kernels of the two distinct linear congruences `(a±r b)≡0 (mod p)` with `r²≡-2`, each a principal index-p prime ideal by the PID property. Consequently finite norm-coprime sieve graphs are **exactly realized** by finite principal-ideal lists. For the other inequality, the nonunit norm of each generator divides `Q²`, so its deleted ideal cannot intersect the norm-coprime sieve for primes dividing the scalar period `Q`.

Combining both shows the minimax optimum over norm residue sieves equals the optimum over all finite principal-ideal sieves in this ring. This equivalence is proved, not postulated, in Section 4 of the paper.

## External inputs for the numerical example

The *general* theorem has no computation. Its `197` specialization uses two separately frozen public proof packages: `../sqrt-minus-two-universal-sieve-barrier` for exact connected universally admissible 197-point data and all-prime local admissibility, and `../sqrt-minus-two-exact-sieve-optimum` for the matching period-sieve upper bound. Both have detailed independent integer checkers, tamper controls and full SHA256 hashes. No undisclosed numerical optimizations or unknown certificates are required.

The actual irreducible-only graph is **not** the sieve allowed graph. This paper does not claim it contains a connected 197-point all-prime pattern. The unconditional true prime graph bounds remain `[90,197]`; Schinzel-H conditional equality is separately labeled in the related note. Full Lean formalization, systematic literature novelty review and independent human refereeing have not yet taken place.
