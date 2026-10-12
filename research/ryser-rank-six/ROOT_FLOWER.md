# Necessary root-flower normalization for a rank-six counterexample

7 October 2026. This is a search reduction, not a solution of Ryser's problem
or an exclusion theorem. It adds structure to the existing finite search.

Let H be an intersecting six-partite six-uniform hypergraph with cover
number six. Fix any edge e={e_0,...,e_5}, with e_i in part i. For each i,
the five vertices e without e_i fail to cover H. There is therefore an
edge f_i disjoint from those five vertices. Since H is intersecting,
f_i intersects e, and the only possible intersection is exactly {e_i}.
These six f_i are distinct from e and from one another: an edge cannot
intersect e in two different singleton sets simultaneously. Thus every
counterexample contains at least seven edges consisting of e and these
six private neighbours.

After relabeling e to the all-zero tuple, put these edges into rows 1
through 6, with f_i in row i+1. Their zero entries form precisely the
diagonal: f_i has zero in part i and a nonzero label in all other parts.
Relabel nonzero values in each part by their first occurrence in this
ordered row list, followed by the remaining rows. Then row 1 has label 1
in parts 1 through 5, and row 2 has label 1 in part 0. All other labels
have increasing order of first appearance. These relabelings preserve
intersection and all cover sizes.

Consequently, for N>=7 and q>=6, `--root-flower --label-precedence`
preserves every counterexample within the existing finite N-edge,
q-vertices-per-part scope, allowing duplicate rows to pad to N as before.
It is not an assertion that every intersecting hypergraph has such a
flower: cover number six is essential. The order-five affine-plane
baseline does have private neighbours in each of its six directions,
and provides a direct normalization regression example even though its
cover number is only five.

Encoding details: private-neighbour zero/nonzero entries are unit clauses.
For v>=2, the clause
`not x(row,part,v) or OR_{earlier row} x(earlier row,part,v-1)` forces
appearance of v-1 before v. This is justified by value relabeling and
does not constrain the incidence structure. The root flower is only a
necessary condition; the exact five-cover separation loop remains required.

The independent option `--private-neighbours` applies the same necessary
singleton-intersection condition to **every** encoded row and every part.
For each candidate neighbour, an auxiliary variable is equivalent to one
coordinate equality and five coordinate inequalities, using the existing
pairwise equality variables. Their disjunction requires a neighbour. This
also remains valid with duplicate padding rows: any distinct private edge
present in H occurs in some encoded row. No neighbour can be the row itself.

```sh
/tmp/ryser-six-venv/bin/python search.py --edges 36 \
  --root-flower --label-precedence --seconds 240 --output candidate.json
python3 verify_witness.py candidate.json
```

The second command is meaningful only if a candidate file was produced.
No theorem follows from a timeout or unverified solver UNSAT status.

The regression checker `check_root_flower.py` constructs the affine-plane
baseline, selects all six private neighbours, applies the normalization,
and checks every root-flower and value-precedence property. It also checks
that the new necessary condition does not falsely certify cover number
six. Its finite checks are diagnostics for the implementation; the general
normalization proof is the elementary argument above.

For the stronger every-row condition, append `--private-neighbours`.
It does not replace the exhaustive five-cover test for a proposed witness.

## Edge criticality at nineteen edges

The proved nineteen-edge necessary bound gives a second complete reduction
for that first remaining case. If H has nineteen edges and tau(H)=6,
deleting any edge leaves at most eighteen edges and hence a five-cover C.
C must avoid the deleted edge, since otherwise it would cover all of H.
It has exactly five vertices: a cover of at most four for the remaining
edges, plus any vertex of the deleted edge, would give a five-cover of H.

`--edge-critical` encodes, for each row, exactly five selected vertices,
all outside that row, meeting every other row. The decoded choices are
checked directly. Duplicate rows cannot satisfy this requirement. The
option is currently accepted only with `--edges 19`, whose completeness
uses the nineteen-edge theorem. It does not assume criticality of all
larger counterexamples.

```sh
/tmp/ryser-six-venv/bin/python search.py --edges 19 --vertices-per-part 9 \
  --root-flower --label-precedence --private-neighbours --edge-critical \
  --seconds 240 --output candidate.json
```

At N=19, degree>=2 gives at most nine appearing vertices in a part, so
this vertex width does not restrict a possible nineteen-edge counterexample.
The five-cover separation loop and independent candidate checker remain
necessary. A timed-out solve is not an exclusion theorem.
