# EFX for four agents and eight goods under alternating symmetry

Let \(I=\{0,1,2,3\}\) be the agents and \(M\) a set of eight goods.
The functions \(v_i:2^M\to\mathbb R_{\ge0}\) are normalized and monotone;
no additivity or submodularity is assumed. Suppose the alternating group
\(A_4\) acts on \(M\) and acts naturally on \(I\), with
\[
                  v_{\pi i}(\pi S)=v_i(S)
       \quad(i\in I,\ S\subseteq M,\ \pi\in A_4).                 \tag{1}
\]

**Theorem.** There is a complete EFX allocation. Precisely, some labelled
partition \(M=X_0\sqcup X_1\sqcup X_2\sqcup X_3\) satisfies
\[
                 v_i(X_i)\ge v_i(X_j\setminus\{g\})
           \quad(i\ne j,\ g\in X_j).
\]
The condition includes deleting a good of zero marginal value. We do not
require the output partition itself to be invariant under \(A_4\).

The case of four agents and eight goods with *unrestricted* monotone
valuations is not settled here. It is the first remaining boundary case
in [Akrami et al., *EFX Need Not Exist*, arXiv:2604.18216v4, §7](https://arxiv.org/abs/2604.18216v4).
Their examples with three agents and eight goods and with \(n\) agents
and at least \(n+5\) goods are not contradicted by this result. Our
hypothesis concerns an actual simultaneous action, not just each
valuation being a relabelling of one base valuation. The result includes
\(S_4\)-equivariant profiles by restriction; it need not have identical
valuations. For instance, on a natural orbit \((a_i)_{i\in I}\) and four
fixed goods \(b_j\), the functions
\(v_i(S)=|S|+4\mathbf1_{b_1\in S}
          +3\mathbf1_{\{a_i,b_2\}\cap S\ne\varnothing}\)
are distinct nonadditive monotone valuations satisfying (1).

## 1. Two analytic reductions and the action types

Suppose one player has a top singleton in an orbit \(O\subseteq M\) of size
at least four. Make a bipartite graph between the players and \(O\), with
an edge when the good is a top singleton for the player, among all eight
goods. By (1), the player degrees are a constant \(d>0\), the good
degrees a constant \(e>0\), and \(4d=|O|e\). For a set of players \(J\),
\(|N(J)|e\ge |J|d\ge |J|e\); Hall's theorem supplies distinct top
singletons. Give each player its matched good and one other good.
The allocation is EFX: what remains of another pair after deletion is
only a singleton, and each player holds a pair containing a top singleton.

Every transitive orbit of \(A_4\) on a set of at most eight elements
has size \(1,3,4,\) or \(6\), up to unique equivariant isomorphism in
each size. Indeed it is a coset action of a subgroup of \(A_4\) of the
corresponding index. There is no index-two subgroup: a homomorphism to
\(C_2\) kills every 3-cycle, which generate \(A_4\). For index three the
subgroup is the unique Klein four group \(V_4\) of double transpositions
and the identity; there are no elements of order four. All subgroups
of order three are conjugate by the transitive action on the four
vertices, and all subgroups of order two are conjugate by cycling the
three double transpositions. Realize the four actions respectively
as a fixed good, the three opposite-edge pairings of a tetrahedron,
its four vertices, and its six edges. The statement for the pairings
also shows directly that \(V_4\) fixes the size-three orbit pointwise.

If all goods are in size-one or size-three orbits, \(V_4\) acts trivially
on the goods and transitively on the players. Thus all four valuations are
identical. The standard [Plaut–Roughgarden identical-valuation argument](https://doi.org/10.1137/19M124397X)
applies: maximize lexicographically the sorted list of pairs
\((v(X_i),|X_i|)\). If an EFX comparison fails after deleting \(g\)
from \(X_j\), move \(g\) to \(X_i\). Both changed entries now exceed
the old \(i\)-entry: for \(i\) use monotonicity and cardinality, and
for \(j\) use the strict inequality of the failed comparison.
The old \(j\)-entry already exceeded that \(i\)-entry by monotonicity,
so the sorted list strictly increases, a contradiction.

Otherwise, after the top-singleton reduction, the multiset of good-orbit
sizes must be one of
\[
                    (1,1,1,1,4),\qquad (1,1,6),\qquad (1,3,4).  \tag{2}
\]
In fact if there were two size-four orbits, every singleton would be in
an orbit of size at least four. For each type in (2) it suffices to
consider one representative top singleton from each possible small
orbit size. The fixed goods can be arbitrarily relabelled and the
stabilizer of player 0 is transitive on the size-three orbit: it has
order three, intersects \(V_4\) trivially and induces the regular
action on the pairings. Thus the numbers of cases in (2) are \(1,1,2\).

## 2. A finite order obstruction, not sampling valuations

For contradiction, suppose a counterexample exists in one of the four
cases. Every allocation in it has a strict violation; select one per
allocation. These form finitely many strict inequalities. Pick a
sufficiently small perturbation, constant on each orbit of pairs
\((i,S)\), that makes inclusion monotonicity strict and breaks all ties
between distinct orbit classes. For example add a small multiple of
\(|S|+\rho(i,S)\), where \(\rho\in[0,1)\) takes distinct values for
distinct classes, is zero for \(\emptyset\), and ranks the chosen
top singleton above other originally tied singleton classes.
This preserves (1), every selected strict violation and the chosen
top class. Thus it suffices to consider strict total orders of the
orbit-class values. Equalities *within* an orbit class are retained.
All nonempty bundles have positive value after this perturbation.

An allocation with an empty bundle cannot be EFX now: another player
has at least two goods, so after deleting one there remains positive
value from the empty player's perspective. Consequently the only
allocations to test are the \(4!{8\brace4}=40{,}824\) surjections.
Their own bundles have size at most five, and their nonempty
single-deletion bundles have size at most four. To represent a
value \(v_i(S)\), transport \(i\) to 0, and choose the smallest subset
mask among all transports of \(S\). This is the same symbol exactly
when the pairs \((i,S)\) are in the same group orbit.

Write \(a<b\) for order between two such symbols. The base strict edges
are inclusions at player 0 and all other singleton classes below the
designated top singleton. For each surjection impose the clause
\[
          \bigvee_{i\ne j,\ g\in X_j,\ X_j\setminus\{g\}\ne\emptyset}
                    \bigl[v_i(X_i)<v_i(X_j\setminus\{g\})\bigr].   \tag{3}
\]
This means the allocation fails EFX. Terms with empty right bundle
could not witness failure, so their deletion is safe. Thus a
counterexample would give a strict total order simultaneously
extending the base and satisfying all clauses. The finite question
is exactly whether that order exists. Conversely, if there is such
an order, ranks yield strict monotone valuations on bundles of
size at most five, and all larger classes can be placed above them
in increasing cardinality to give full monotone valuations.

The attached checker refutes all four order systems. Its operations
are elementary:

* Maintain the reflexive transitive closure of forced edges.
  In a clause, a forced true comparison satisfies the clause; a false
  comparison is removed. An empty remaining clause is a contradiction.
* Initially one may also remove a literal \(a<b\) if the same clause
  contains \(c<d\) with \(c\le a\) and \(b\le d\) in the base closure:
  the former implies the latter. Such implication by the coordinate
  inequalities is acyclic on distinct pairs of endpoints, so each removed
  literal implies one kept. Duplicate clauses and clauses implied by
  another clause's being a subset can be discarded.
* A remaining clause with one literal forces that edge. Adding \(x<y\)
  refutes the branch if \(y\le x\). Otherwise, connect every predecessor
  of \(x\) to every successor of \(y\) to update the closure.
* If necessary branch on the order of one incomparable pair. One of
  its two strict directions must hold. A branch with no unsatisfied
  clauses admits an order by extending its finite acyclic graph;
  a branch with both children refuted is refuted. There is no numeric
  tolerance, randomized search, or use of bounds on ranks.

## 3. Reproduction

Run `python3 verify_factor_efx_a4_eight_goods.py` (standard library;
without `-O`). In addition to enumerating all surjections, it verifies
that the coded actions are permutation representations. For the four
cases it returns the following closure search counts.

| Orbit sizes | Top orbit size | Symbols | Reduced clauses | Visited nodes |
|---|---:|---:|---:|---:|
| \(1,1,1,1,4\) | 1 | 105 | 228 | 6,858 |
| \(1,1,6\) | 1 | 81 | 186 | 54 |
| \(1,3,4\) | 1 | 81 | 177 | 69 |
| \(1,3,4\) | 3 | 81 | 28 | 4 |

In development, an independent formulation over integer variables,
using left-coset actions and **without** a top singleton assumption,
also returned UNSAT in each of the three mixed action types under
Z3 4.13.3 with quantifier-free integer difference logic. That check
is not a dependency of the supplied closure replay. It differs both
in construction of the good actions and in the order-feasibility
routine.

[Mahara's \(m\le n+3\) theorem](https://doi.org/10.1287/moor.2022.0044)
covers up to seven goods for four players without symmetry. The
[2608.08590 additive result](https://arxiv.org/abs/2608.08590) covers
four additive agents up to nine goods; the restriction here is
equivariance rather than additivity. General profiles at eight goods,
even weaker symmetry groups, and additive profiles with more goods
are not decided by this theorem.
