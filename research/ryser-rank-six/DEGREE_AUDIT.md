# Nineteen-edge theorem: proof audit and limits

Primary-model audit, 7 October 2026. The root theorem has a complete written
proof; it is not a SAT nonexistence claim or externally reviewed result.

- Simplicity is necessary for the intersection-size bound s<=5. Duplicate
  edges are explicitly removed, which preserves tau, partiteness and intersection.
- Every appearing vertex has degree>=2 by the five-cover obtained on deleting
  a degree-one vertex from its unique edge. Hence each part has between six
  and floor(N/2) appearing vertices; no unproved finite-width assumption is used.
- The two-vertex union bound uses only pairing the at most six remaining
  edges and choosing their common vertices. It does not assume remaining
  edges are disjoint, linear or uniformly represented in a solver.
- S and repeated-codegree sums are exact double counts. For every distinct
  edge pair, 1<=s<=5 gives 2*C(s,2)<=5*(s-1).
- The degree-pattern replacement increases the numerical necessary
  expression; it does not claim the replacement is a realizable hypergraph.
- The eighteen-edge pattern space has 19 members. Independent partition
  generators agree; all 134596 six-part combinations have negative deficit.
  The 462 count combinations and three domain-wide Lean statements provide
  a separate certificate path.
- All checks pass with ordinary and optimized Python. Validation uses explicit
  exceptions. SAT statuses and floating-point arithmetic are not dependencies.
- The 19-edge case admits necessary degree patterns. They are not examples;
  no tau=5 theorem at 19 edges or unrestricted rank-six theorem is claimed.

`results/degree-lean-axioms.txt` records three exports depending only on
propext, Classical.choice and Quot.sound, with no sorryAx or new axiom.
Only the scalar inequalities are formalized. The primary model developed
and reviewed the mathematical proof; GPT-6 Luna at High reasoning effort
performed preliminary source comparison, not proof validation.
