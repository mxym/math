# The exact coherent Condorcet maximum on ten alternatives

For the full coherent class of [Karpov–Markström–Riis–Zhou, 2025](https://doi.org/10.1016/j.dam.2025.03.007), the ten-alternative maximum is **1046**. Here one common axis is required, and each triple \(a<b<c\) may independently choose either \(1N3\) (never rank \(a\) last) or \(3N1\) (never rank \(c\) first). There are **40** maximal-size sets on a fixed labelled axis, in **six** ordinary relabelling classes. The numbers of same-axis domains in those classes are \(4,4,8,8,8,8\). All 40 are copious, therefore inclusion-maximal as Condorcet domains, and have trivial automorphism groups. Ranking reversal fixes four ordinary classes and interchanges the other two.

This is the enlargement from \(n\le9\) in [the packet-model proof](CondorcetCoherentExactMaxima.md). It does not decide the catalogue's unrestricted nine-alternative question or the unrestricted ten-alternative maximum. The 2025 article's ten-alternative set-alternating optimum is \(973\), while the larger general peak-pit class already contains a ten-alternative domain of \(1104\) by [Karpov–Markström–Riis–Zhou, 2026, Table 1](https://arxiv.org/abs/2601.07336). No new general lower bound is claimed.

## Exact upper bound and equality audit

For completeness, the finite search begins with every \(321\)-avoiding ranking, of which there are the Catalan number \(16796\). Every coherent ranking avoids \(321\), and if \(c\) is ranked before \(a\), its relative placements of the intermediate labels \(b\) determine all required rules on the triples \((a,b,c)\). Two such rankings with conflicting requirements on a triple occur in distinct style groups of the same \((a,c)\) packet. Conversely, in the absence of such a conflict the common rules may be completed arbitrarily on triples without requirements. Therefore a closed candidate state satisfying all conflicts can be accepted, and a conflicting state may branch into the surviving noninverters plus one surviving style group for the chosen packet. This branching is exhaustive; disjoint packet pieces give the same exact additive loss bounds as in the preceding proof. Only states with upper bound **strictly below** the current achievable value are pruned, retaining all ties. The optimized integer traversal visited \(414835\) states (including calls pruned or previously visited); an independent variant seeking only strict improvements previously gave the same \(1046\) with \(409777\) calls.

At every maximum the projection onto each triple has exactly four permutations. A fifth necessarily creates a majority cycle on that triple, which is why each listed domain is inclusion-maximal even in the larger class. To compare two domains under relabelling, list all relabellings that send one of their own rankings to the increasing ranking. Every possible comparison with another fixed-axis coherent domain is in this list, since every maximum contains the increasing ranking. The least sorted ranking list over all those relabellings is a complete ordinary isomorphism key. The number of relabellings returning the same original labelled domain is the automorphism order; in each of the 40 cases it is one. Reversing every ranking and taking the same key checks duality without counting ranking reversal as an ordinary relabelling.

## Independent lower witness

Order the nonadjacent endpoints \((a,c)\) lexicographically, using labels \(0,\ldots,9\). Bit \(b-a-1\) selects \(3N1\) when set and \(1N3\) otherwise. In this order the 36 masks are:

```
0,0,4,2,12,18,82,210,0,2,1,6,9,41,105,1,1,3,3,11,43,0,1,2,10,26,
1,1,5,13,0,1,5,1,3,1
```

Testing the 120 literal ternary rules independently on all \(10!\) permutations gives exactly \(1046\) orders, and this set is among the enumerated optima.

Run `python3 verify_coherent_condorcet_ten.py` beside the preceding `verify_coherent_condorcet_maxima.py`. Option `--witness-only` tests only the explicit witness; `--direct` additionally changes the search's candidate generator from the insertion rule to exhaustive filtering of all \(10!\) orders. The exact bound relies on the proved search, not on the quick witness test.
