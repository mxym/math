# No backtracking in the complementary-triple case

**Claim.** For every n >= 9 and r = n-3, every legal prefix in the selection phase of Algorithm 1 of Carlet, Feukoua and Salagean, *The stability of the algebraic degree of Boolean functions when restricted to affine spaces*, [Designs, Codes and Cryptography 93 (2025)](https://doi.org/10.1007/s10623-025-01702-z), extends at its next variable. In particular the algorithm terminates regardless of its nondeterministic choices, subject to the stated rule not to retry failed candidates. This settles precisely the possible obstruction raised in their journal Remark 2 (after Proposition 6); it does not assert the construction captures all affine-equivalence classes in their Open Problem 1. The degree/worst-case and average complexity bounds of Proposition 6 are not needed or asserted here.

## Translation of the algorithm

Write X for the variable labels. A chosen degree n-3 monomial m_j omitting x_j is encoded by its complementary triple H_j, with j in H_j. Think of j as the label that selected H_j, and P_j=H_j minus {j} as its designated pair. The Step 9 forbidden set V_j consists exactly of the triples P_j union {t}, t outside H_j. Thus after any valid prefix, each P_j belongs to just one *distinct* selected triple, namely H_j. Distinct labels may have selected the very same triple; this is allowed by the algorithm (the candidate set does not exclude F). Every selected triple has at least one selecting label; no label selects twice.

For a new label v, choosing T={v,a,b} is admissible precisely when (i) T contains no previous designated pair, except when it equals the previous triple designating that pair; (ii) no previously selected triple other than T contains {a,b}. These are respectively the earlier Forbidden test in Step 8 and V_v intersection F test in Step 10. In particular an already selected T can be reused if {a,b} is private. The Failed_v set only excludes candidates previously tested and found to violate (ii) for this same fixed prefix. The final arbitrary addition of allowed monomials takes place only after all labels have witnesses and is not a prefix under discussion.

## Proof

Fix any prefix and any unassigned v, and suppose no admissible triple exists. Put m=n-1. For each selected triple {v,h,b}, one of its selecting labels is an endpoint h different from v; direct an edge h -> b on the remaining m labels. Multiple selecting labels for the same triple would give both orientations. Because {v,b} is the private pair designated by h, b is incident with just this one undirected edge. Distinct oriented edges have distinct tails (each label selects once) and distinct heads (a head is incident with just this edge).

Every undirected edge {a,b} requires a previously selected triple off v containing both a,b: otherwise its original triple could be reused to serve v. In particular no edge can have both orientations. If it did, a and b have already selected the triple on v and cannot select a second triple. Any further triple {a,b,c} covering {a,b} would have to have selector c, and c's designated pair {a,b} would not be private. Furthermore no head can be a tail: since its incident undirected edge is unique, its outgoing edge would have to be the forbidden reverse edge. It follows that the edges form a matching. Denote their number by b, their head set by B, and the other vertices by S, with s=m-b. The letter b henceforth denotes the edge count, not a vertex.

Every pair of S must occur in a previously selected triple off v. Indeed, if a pair {x,y} in S is absent from all such triples then it is absent from the triples on v as well (every matching edge has a head in B). Try T={v,x,y}. The new pair is not present earlier. No designated pair off v can invalidate T unless it equals {x,y}, which is absent. A designated pair containing v is {v,z} with z a head in B; neither x nor y is a head. Thus T is admissible, contrary to the supposition.

The b matching edges each require a covering triple off v; these b triples must be DISTINCT, because two disjoint edges use four vertices. Every such triple contains a head and covers at most one pair of S. There are at most m-b=s distinct off-v triples altogether: at most m labels have been processed, and b distinct labels already selected the b triples containing v. Therefore

    binom(s,2) <= b + 3(s-b) = 3s-2b.

Substituting b=m-s yields s^2-11s+4m<=0. For m>=8 the left member is at least s^2-11s+32=(s-11/2)^2+7/4>0, including n=9. This contradiction proves extendability. The finite retry loop cannot avoid a valid candidate forever, because failed candidates cannot be retried. Correctness of the final output follows from preservation of private pairs, exactly as in the authors' Theorem 5. QED.

This is entirely independent of any classification of nine-variable forms.
