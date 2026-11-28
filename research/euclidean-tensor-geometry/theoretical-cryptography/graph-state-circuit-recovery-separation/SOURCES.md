# Sources and scope

Literature and repository search performed 2026-11-28 UTC.

- Sayantan Ganguly, [Symplectic Matroids, Stabilizer Codes, and
  Quantum Secret-Sharing](https://arxiv.org/html/2611.27300v2),
  arXiv:2611.27300v2, 25 November 2026. The [version history](https://arxiv.org/abs/2611.27300)
  showed v2 as current. In [§VI](https://arxiv.org/html/2611.27300v2#S6),
  problem 2 (HTML lines 1007–1008) asks whether a circuit-induced
  quantum access structure at a dealer of a **simple** graph
  implies containment in that dealer's operational recovery
  family. It is a fixed-dealer hypothesis; the graph matroid's
  additional all-dealers property is separately defined in §IV-B.
  Problem 3 (lines 1010–1011) asks for all-dealers equality in
  binary graph states. The current note answers problem 2
  negatively, including under the stronger all-dealers premise,
  and gives the bipartite subclass of problem 3 only.
- Precise definition map from the same paper: Definitions 2
  and 3 (§IV-A/B) distinguish an abstract quantum access
  structure (nonempty, monotone and intersecting) from an
  operationally authorized set. Proposition 5 and Theorem 5
  (§IV-B) identify circuit-family membership with admissible
  supported vectors and describe the odd-neighbourhood rule.
  Definition 4 (§IV-C), Theorem 9 and Corollary 5 (§IV-E) are
  the specific dealer-shortened model, the rank-two/one/zero
  recovery/intermediate/forbidden distinction, and its cut-rank
  specialization. Those general tools are not new here.
- Ganguly §IV-G, Theorem 11 proves the inclusion with
  self-duality. Example 6 has a self-loop and is not a
  simple-graph counterexample. Theorem 13 and Table I have
  strict containment in the **opposite** sense from the
  counterexample here: at six vertices some actual recovery sets
  do not contain a circuit-induced set, while every circuit-induced
  set still recovers if the circuit family is a quantum access
  structure. Table I verifies the implication through six
  vertices. Our exact seven-vertex census also reproduces the
  Table I entries. The companion paper, [Representability of
  Graphical Symplectic Matroids](https://arxiv.org/abs/2611.01241v2),
  arXiv:2611.01241v2, treats Chow's **edge-indexed** graphical
  matroids, not the vertex-pair recovery question here.
- Pradeep Sarvepalli, [Quantum Codes and Symplectic
  Matroids](https://arxiv.org/abs/1104.1171), §§II and IV,
  is prior art for the stabilizer-matroid association and
  circuit access structures. Pradeep Sarvepalli and Robert
  Raussendorf, [Matroids and quantum-secret-sharing
  schemes](https://arxiv.org/abs/0909.0549), establish the
  identically self-dual matroid construction. Neither result is
  claimed as new.
- Pradeep Sarvepalli, [Non-Threshold Quantum Secret Sharing
  Schemes in the Graph State Formalism](https://arxiv.org/pdf/1202.3433),
  *Phys. Rev. A* 86, 042303 (2012), §III, Lemma 3 and
  Theorem 4, gives the bipartite/CSS graph-state background and
  proves sufficiency of the orthogonal bipartite adjacency block
  for perfect sharing at every dealer, with an odd-neighbourhood
  description of its access generators. The separate additions
  here are the fixed-dealer circuit/operational equivalence under
  the access axiom and the exact necessity of the block condition
  for equality at every dealer. We do not claim the sufficient
  construction, the CSS representation, or the odd-neighbourhood
  formula as new. Jérôme Javelle, Mehdi Mhalla and Simon Perdrix,
  [New Protocols and Lower Bounds for Quantum Secret Sharing with
  Graph States](https://arxiv.org/abs/1109.1487), also use
  cut ranks and complement recovery in graph-state sharing.
- Brendan McKay's [connected simple graph
  lists](https://users.cecs.anu.edu.au/~bdm/data/) were an
  exploratory source for finding the small graphs. Neither
  checker downloads or depends on those data; the census
  re-generates the graph classes, and the examples are given
  directly by their edge sets.

The bounded duplicate search used the 2026 paper title and IDs,
the exact combinations “circuit-induced”/“operational” with
“quantum access structure,” “simple graph,” “counterexample,”
“bipartite” and “all dealers,” and the cited 2010–2013
graph-state papers. It also checked nearby directory names on
[the research branch at its then head](https://github.com/mxym/math/tree/feac2dc53a33384908beeb397fc8c396349cc851/research),
including the unrelated graph-state monogamy result.
No matching simple-graph counterexample or all-dealers clone
construction was found. This is a bounded check, not an absolute
priority claim.
