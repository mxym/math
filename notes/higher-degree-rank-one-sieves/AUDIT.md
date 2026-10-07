# Audit and exact verification

Reviewed source date: 7 October 2026. This is a public summary of the frozen
mathematical audit, with new checks of the public derivatives. It is not a
formal proof verification or a mathematical-priority assessment.

## Mathematical verdict

The independent audit found no core mathematical gap in:

1. The translation-uniform bounded-norm intersection theorem, including every
   nonmaximal order, and its all-degree exceptional-restoration corollary.
2. The rank-at-most-one closed-walk-voltage completion theorem, with its complete
   labelled quotient, actual subgroup generator, maximum level jump, prime
   exclusions, and CRT slab bound.
3. The complete cubic certificates: exact avoiding-component maxima 6 for F6
   and 56 for the explicitly defined F8chain.
4. The structural two-ideal zigzag gate, impossibility of completion by any one
   extra nonzero nonunit principal ideal for F8chain, and two-prime CRT slabs.
5. The stronger k^2 * 2^{16(r+1)} associate-class intersection/restoration
   interface, the finite-index unit-rank argument for arbitrary orders, and
   both restored decimal cardinality bounds.

This verdict is confined to these statements and exact frozen inputs. It does
not establish an initial gate for every finite step set, the 26-neighbor graph,
a universal cubic moat, or any higher-dimensional entropy theorem.

## Independent arithmetic routes

The independent checker imports no author checker or search/generator code.
Multiplication uses polynomial reduction by X^3-2; determinants use the Leibniz
permutation formula; ideal membership uses exact Fraction Gaussian elimination.
It reconstructs all quotient states, directed step-labelled edges and components
from the exact arithmetic, retaining labelled edges separately from adjacency.
It also reconstructs the complete mod-6 two-ideal F8chain voltage gate, including
loops and parallel edges, and certifies V=2, H=Z(0,1,1), K=1.

For F6 it finds eight allowed states, twelve directed edges and component sizes
2,6. For F8chain it finds eighty allowed states, 216 directed edges and component
sizes 6,9,9,56. The respective undirected cycle ranks are 0 and 32. Every allowed
directed edge satisfies the exact integer identity y_r+f=y_s. These identities
prove that lifting does not enlarge the quotient components.

The 729 vectors in [-4,4]^3 supply 2,916 F6 and 3,645 F8 membership comparisons,
and each variant has 729 determinant-versus-norm-polynomial comparisons. These
finite-box checks corroborate the arithmetic. Global kernel equalities instead
follow from exact kernel inclusion and equal lattice index; the infinite-graph
conclusion follows from all-edge voltage identities, not a window cutoff.

## Strict-schema hardening

The historical author checkers reconstructed the correct graphs but accepted
three numerically equivalent non-integer metadata changes in each certificate:
state 1 -> true, norm 2 -> 2.0, and allowed_count -> its float representation.
This was a schema weakness, not a false graph proof: arithmetic vectors, states,
norms and edges were independently reconstructed.

The public derivatives now use type(value) is int rather than equality alone
for arithmetic metadata. Their added checks cover norm lists, allowed-state
lists, modulus, component state IDs, summary scalar integers and component
sizes. Lift state IDs and coefficient vectors were already strict. Seventeen
built-in controls per author derivative are rejected: the original seven and
ten additional metadata controls. The strict independent checker rejects its
fifteen controls per variant. The separate metadata regression reproduces all
three original acceptances and all corresponding rejections by both strict
implementations. Exact unified diffs and unchanged originals are included.

The only independent-checker change is its certificate lookup from a frozen
subdirectory to the public package directory. No arithmetic, validation or
negative-control code changed, and its output is byte-identical to the frozen
independent result. The historical output key frozen_sha256 still records the
unchanged frozen certificate bytes.

## Optimization and source integrity

The reproduction command runs all four checks normally and with python -O;
outputs must be byte-identical to the supplied fixtures and to each other.
No validation relies on an assert statement. Original certificate hashes and
original-checker hashes are recorded and checked. The stronger source note was
separately frozen rather than overwriting the first reviewed revision; both
revision hashes are retained in SOURCE_HASHES.json. The certificates and
original author checker code were unchanged across that revision.

## Arithmetic inputs and scope

The Beukers-Schlickewei input has exactly the scope of solutions to X+Y=1 in
the Q-closure of a finitely generated subgroup of (C*)^2 of torsion-free rank R,
with bound 2^{8R+8}. The constructed subgroup has rank at most 2r+1 and is
contained in that closure. Coefficients involving the translation add one
multiplicative pair, not one place for each of its prime divisors.

The order-level prime supply uses a ray class field modulo f O_K with
f O_K contained in O and Chebotarev in its normal closure. Integral generators
congruent to 1 modulo f O_K lie in O and give norm-prime ideals. This imported
supply guarantees completion only after a rank-one gate has been supplied.

The graph completion and restoration arguments are given in full in paper.md.
See SOURCE_MAP.md for the imported primary sources and frozen audit provenance.
