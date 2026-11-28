# Exact small coherent Condorcet maxima, and one exceptional rule

**Result.** For \(n=1,\ldots,9\), the exact largest sizes of coherent Condorcet domains are
\[
1,\ 2,\ 4,\ 9,\ 19,\ 43,\ 94,\ 211,\ 465.
\]
At \(n=9\) there are exactly sixteen maximizing domains with the axis fixed to the increasing order. They give four classes under ordinary relabelling, four fixed-axis domains per class. All four classes have trivial relabelling automorphism group and are not self-dual, so rank reversal pairs them into two pairs. Every maximizing domain at \(n=9\) is copious and therefore is inclusion-maximal even as a Condorcet domain.

On nine alternatives, allowing **at most one exceptional rule** of type 2N1 or 2N3, with all other rules coherent along the same axis, raises the exact maximum to **476**.

This is the full class of **coherent** domains of [Karpov–Markström–Riis–Zhou (2025)](https://doi.org/10.1016/j.dam.2025.03.007), not just the set-alternating subclass. In particular the values \(43,94,211,465\) improve the respective sizes \(42,91,202,437\) of the set-alternating examples in their Table 1 within this comparison, and are upper bounds for every coherent domain. These are not bounds on general peak-pit or general Condorcet domains. For comparison, the same authors' [2026 record](https://arxiv.org/abs/2601.07336) gives \(492\) on nine alternatives in the larger peak-pit class and leaves the unrestricted maximum open.

We also give the exact form of the projections of their common Fibonacci subdomain, correcting a statement about arbitrary triples in Proposition 1(i) of the 2025 paper, and give an alternative proof of the ample-to-copious implication in its Lemma 3.

## 1. Two possible signs per triple, one packet per pair

Relabel the alternatives to fix the societal axis as \(1,2,\ldots,n\). A coherent domain has, for each \(a<b<c\), either the never-last rule for \(a\) (1N3) or the never-first rule for \(c\) (3N1). A set satisfying these rules is a Condorcet domain by Sen's three-alternative value-restriction characterization. For finding an optimum we may complete a domain to all orders satisfying some chosen rule at every triple, since adding such orders cannot violate a chosen rule.

Writing the rankings of a triple in relative-order notation, both rules allow \(123,132,213\) and reject \(321\). Rule 1N3 adds \(312\); rule 3N1 adds \(231\). Start, therefore, with all \(321\)-avoiding permutations. They are generated without repetitions by inserting the new largest letter at a location whose following suffix is increasing: a decreasing pair in that suffix is exactly how the insertion could make a new \(321\). This enumerates the Catalan numbers \(1,2,5,\ldots,4862\) for \(n=1,\ldots,9\). There is also a replay mode that checks the decreasing triples directly on all \(n!\) permutations, independently of the insertion recursion.

Fix an axis pair \(a<c\) with an intermediate letter. Orders that put \(a\) before \(c\) require no particular one of the two signs on any \((a,b,c)\). In an order that puts \(c\) before \(a\), an intermediate \(b\) cannot be between them, which would give \(321\). If \(b\) is before \(c\), the rule must be 3N1 on that triple; if \(b\) is after \(a\), it must be 1N3. Thus an order with \(c\) before \(a\) prescribes an entire string of signs on the triples with this pair of extremes. Its **style** is the subset of intermediate letters before \(c\).

The packet of orders inverting \((a,c)\) is partitioned into these style groups. A coherent domain may intersect at most one group of each packet. Conversely any set of the \(321\)-avoiding orders with that property is coherent: every triple belongs to just one packet, that for its two extremes, and all signs prescribed by those orders agree. Pairs consecutive on the axis have no triples of which they are the extremes.

## 2. Exact optimum search

A state is a bitset \(S\) of still possible orders, initially all \(321\)-avoiding orders. If some packet has two or more nonempty style groups in \(S\), branch on which one to retain, preserving all orders outside the packet. Any feasible subdomain of \(S\) survives in at least one child: if no order in it inverts the pair, it survives in all children. Branching eliminates at least one order. A state in which no packet conflicts is itself feasible.

There are two exact integer pruning bounds. At a conflicting packet with \(b\) orders of \(S\) and largest subgroup of size \(h\), any child or descendant has size at most \(|S|-b+h\). For a stronger bound, visit several conflicting packets in sequence; in each use only the part of that packet not used by an earlier one. These pieces are disjoint. On each piece take the same packet bound using its own largest style count. The losses add and give an upper bound on any feasible subset of \(S\). There is no presumption of disjointness among the original packets. The pruning compares these upper bounds to the size of a real witness obtained either from a tested set-alternating assignment or from a conflict-free leaf. In the all-optimizers run the pruning uses strict inequality, so it does not discard ties. The state \(S\), rather than the history of assignments, suffices to determine its possible feasible subsets, so repeated states can be merged.

The companion checker runs this finite proof with arbitrary-precision integers only, and checks every resulting maximizing domain directly against the relevant never-position conditions. The direct witness below is checked independently by testing the chosen rules against all \(9!\) rankings. No optimization tolerance or numerical sampling is used.

## 3. The nine-alternative optimum and its isomorphisms

One size-465 witness is encoded by the following 28 style integers, for pairs \(1\le a<c\le9\) with \(c-a\ge2\), in lexicographic order, first by \(a\), then by \(c\):
\[
(0,0,2,4,10,42,106,\ 0,1,2,5,21,53,\ 1,1,3,5,21,\
 0,1,5,13,\ 1,1,5,\ 1,3,\ 1).
\]
Bit \(b-a-1\) (starting at bit zero) is one exactly when the rule on \((a,b,c)\) is 3N1, and zero when it is 1N3. This is a full rule assignment, not just a list of sample orders.

The search reaches sixteen distinct maximum bitsets. The increasing order belongs to each. To test unrestricted relabelling isomorphism between two such domains, any relabelling taking one to the other must send one order of the source to the increasing order; each source order specifies exactly one such relabelling. Testing these maps (equivalently, comparing the least normalized image of each domain) gives four classes, with four listed domains each. Reversing every ranking and normalizing in the same way pairs the four classes, with none fixed. The same check counts one automorphism for each domain. Direct triple projections have cardinality four for all of the sixteen domains. A size-four acyclic triple projection determines its unique never condition, so no extra order can be added to a full such domain preserving the Condorcet property, as also argued in the 2025 paper.

## 4. The Fibonacci projections and the ample-to-copious step

The common Fibonacci domain is the set satisfying both coherent rules on every triple. In an order in this domain, an inversion of \(a<c\) with an intermediate letter \(b\) would yield one of \(231,312,321\), each forbidden. Thus all inversions compare consecutive axis labels. Two such inversions cannot share a label, since that would force a nonconsecutive inversion. Conversely disjoint swaps of adjacent axis labels have no nonconsecutive inversion and satisfy both rules. This gives the original Fibonacci cardinality.

For an arbitrary set \(A\) of retained labels, a projected swap can only take place between a pair in \(A\) that was consecutive on the *original* axis. All independent choices of disjoint such swaps can be extended by leaving the other labels fixed. If the maximal runs of consecutive labels in \(A\) have lengths \(s_1,\ldots,s_k\), the projection therefore has size \(\prod_i \mathrm{Fib}_{s_i+1}\), with \(\mathrm{Fib}_1=\mathrm{Fib}_2=1\). For a triple it has size \(1,2,\) or \(3\) depending on whether zero, one or two original neighbor pairs lie in the triple. For example at \(n=4\), the set \(\{1,3,4\}\) has only the two projected orders \(134,143\), not also \(314\). The claim of three orders for every triple in Proposition 1(i) is thus false as written. Its Fibonacci counting conclusion is unaffected.

The subsequent ample-to-copious conclusion admits a repair that does not require the incorrect projection claim. In a full coherent domain an adjacent inversion in any ranking can be swapped to remove the inversion while retaining every coherent rule. Indeed the only changed triples contain both swapped letters, and among allowable relative patterns the only descending adjacent moves are
\[
132\longrightarrow123,\quad 213\longrightarrow123,\quad
231\longrightarrow213,\quad312\longrightarrow132.
\]
Every changed pattern is allowed by either rule. Repeated inversion removal takes any ranking to the increasing order in the domain.

Fix a triple \(a<b<c\) and for a pair \(x<y\) let \(I_{xy}\) be one when some ranking in the full domain places \(y\) before \(x\), and zero otherwise. The pattern \(213\) occurs on the triple exactly when \(I_{ab}=1\): an \(a,b\) inversion can otherwise occur only in \(231\), and its inversion-removal path passes through \(213\) before reaching \(123\). Similarly \(132\) occurs exactly when \(I_{bc}=1\). One of \(231,312\) occurs exactly when \(I_{ac}=1\), and they cannot both occur because they require different coherent rules. Together with the increasing pattern, the projection size is exactly
\[
1+I_{ab}+I_{bc}+I_{ac}.
\]
For a full coherent domain on at least three alternatives, ampleness (both orders on every pair) consequently implies copiousness, and the converse follows from the same formula. A maximal coherent domain is full for its chosen rules, as otherwise a rule-satisfying ranking could be added; this proves the implication of Lemma 3 with the original hypotheses.

## 5. One exceptional middle-letter peak or pit rule

Allow one triple \(T=(a,b,c)\) to use 2N1 (the middle axis letter \(b\) is never first) or 2N3 (it is never last), and keep coherent rules everywhere else. Neither of these two exceptions forbids the increasing ranking. Simultaneously reversing the axis labels and all rankings preserves the increasing ranking, interchanges 1N3 with 3N1, and interchanges 2N1 with 2N3. It therefore suffices to consider a 2N1 rule and each possible position of \(T\).

Every candidate order either avoids \(321\) everywhere, or has exactly one \(321\) and it is at \(T\), since every coherent triple excludes \(321\). The candidate list for \(T\) is precisely all the first kind that satisfy 2N1 on \(T\), together with all the second kind. In the nine-alternative permutation enumeration there are 4862 orders of the first kind before the 2N1 filter, and 6188 orders with exactly one \(321\) when summed over all 84 possible triples. These lists are constructed by directly scanning the triples of every permutation.

For a packet with extremes \(u<w\), the style omits the coordinate \(v\) if \((u,v,w)=T\). Every non-omitted intermediate still lies either before \(w\) or after \(u\) when \((u,w)\) is inverted, as otherwise that other triple would be a \(321\). The proof in §1 now applies unchanged to all coherent triples. Within the candidate list, satisfying the exception is already guaranteed. Accordingly the same disjoint-packet bounds and exhaustive branches test each of the \(\binom93=84\) 2N1 cases. Each gives an upper bound of 476; the zero-exception case has upper bound 465.

For a matching example, set \(T=(6,8,9)\), impose 2N1 there, and use the same pair encoding as §3 for the other triples, with style vector
\[
(0,1,2,10,5,26,37,\ 1,1,5,5,13,21,\ 0,1,1,5,9,\
 1,1,3,5,\ 0,1,2,\ 1,1,\ 1).
\]
The omitted coordinate has no meaning in this vector. Directly evaluating the explicit rules on all \(9!\) orders gives 476 orders, of which 76 have the reversed restriction at \(T\). Since 476 exceeds the coherent maximum with any axis, this is genuinely noncoherent. This does not determine the maximum with two or more exceptions. In particular, any nine-alternative domain of size at least 492 that is represented using only these four types of rules must have at least two noncoherent rule positions in every such representation.

Run `python3 verify_coherent_condorcet_maxima.py` (Python 3.10 or later), or append `--direct 9` to repeat the nine-alternative calculation from direct permutation generation. Run `python3 verify_coherent_condorcet_one_defect.py` from the same directory to check the explicit 476 witness and all 84 exceptional-rule cases. These are exact finite mathematical checks, not Lean proofs or an unrestricted nine-alternative solution.
