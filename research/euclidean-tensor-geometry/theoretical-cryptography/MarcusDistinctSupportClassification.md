# Exactly which distinct-support pair circuits have a universal common minor law

Let a word consist of two-coordinate unitary gates, each acting on its specified pair and as the identity elsewhere. A word is **universal** if for every choice of the local gates there is a single probability measure on permutations $\pi$ of the coordinates such that
\[
 |\det U[I,J]|^2=\Pr(\pi(J)=I)
\tag{1}
\]
for every equally sized pair of subsets $I,J$, where $U$ is the chronological product. This is the spectrum-independent common minor law, stronger than the original Marcus–de Oliveira conjecture.

**Theorem.** For an ordered word with **distinct pair supports**, universality holds exactly under the following two conditions:

1. The simple support graph has no cycle of length at least four.
2. At every vertex of every support triangle, no gate outside that triangle is incident at the vertex and occurs strictly between its two triangle gates there.

When either condition fails, the word can be made to violate (1) using only real plane rotations (including signed swaps). There is no matrix-dimension or gate-count bound. In particular, among one-pass circuits, the graph and the interposition test give a decision procedure without any minor-polytope optimization.

The positive cases use the [earlier forest composition law](MarcusForestedGates.md), which also covered arbitrary block gates of size at most three. The two four-gate obstructions needed for the negative cases specialize that note's exact classification. The new part is the obstruction for every larger simple cycle, including alternating cycles that cannot be reduced to four gates by a single support contraction, and the resulting necessity and sufficiency in all dimensions. [Drury's counterexample](https://doi.org/10.1016/0024-3795(92)90296-M) originally showed the stronger assertion false; the [four-dimensional fourteen-term representation](https://clopen.solutions/submissions/openproblemsinnla-holden-mi05-2026-09-13-report/v1/) gives a complementary description in dimension four. We do not claim a counterexample to the original determinant conjecture or an exact test for words with repeated pairs.

## 1. The positive cases

A simple graph with no cycle of length at least four has every nontrivial block equal to a bridge edge or a triangle. Indeed, a 2-connected block with a triangle and an additional vertex has a path with internal vertices outside the triangle joining two distinct triangle vertices (by 2-connectivity); adjoining the two-edge route inside the triangle makes a cycle of length at least four. A 2-connected block without a triangle already has a cycle of length at least four. The incidence graph of blocks and their vertices is a forest, the usual block-cut tree with non-cut vertices attached as leaves. Different blocks share at most one coordinate.

At a shared coordinate the occurrences from different blocks are totally ordered by block: the two triangle gates incident at that coordinate form an interval into which no other incident gate is allowed, and a bridge has just one occurrence. If two triangles share the coordinate, their two occurrence intervals are disjoint, since overlap would put an endpoint of one inside the other. Direct a block precedence arrow according to this order whenever two blocks share a coordinate. This precedence graph has no directed cycle. A shortest directed cycle cannot use the same shared coordinate for two consecutive dependencies, since the total order at that coordinate would permit a shortcut; it would therefore lift to a closed nonbacktracking walk in the block incidence forest, which is impossible.

Take a topological order of the blocks. We may group all gates block by block in that order, retaining the original order within each block: any individual order changed by doing this involves disjoint pairs, so it can be effected by exchanges of commuting gates. Each grouped block is now a unitary on at most three coordinates, and consequently has (1). The block incidence forest then allows composition with the earlier forest theorem. This proves sufficiency.

## 2. Reductions for the obstructions

If a gate is interposed at a triangle vertex, retain just the three triangle gates and that external gate, setting all others to the identity. The four retained gates are a triangle with a pendant edge temporally between its two center-incident triangle edges. Up to common relabelling, reversal and exchange of disjoint gates, the only two words are $12,13,14,24$ and $12,13,24,14$. The original four-gate note gives exact real counterexamples for both; the companion checker replays the five-term minor inequalities and the word check. The fourth coordinate is distinct because this is a distinct-support word.

If the support contains a simple cycle of length $\ell\ge4$, retain just its edges. All orders of a four-cycle already fail by the earlier four-gate classification. For a longer cycle, consider the rank of each gate in the chronological order, arranged around the cycle. If some edge $e=ab$ has rank strictly between those of its two neighboring edges, set its gate to a signed swap of $a,b$. Commute that monomial matrix to one end by conjugation. Exactly one of the two neighboring edge supports is then relabeled by the swap; the other stays fixed. Deleting $e$ has now shortened the cycle by one, leaving the unused endpoint as a spectator. Monomial factors do not affect existence of (1), and a spectator must be fixed by any permutation law, by (1) at size one. This reduces inductively to a shorter cycle word. Conjugating a real plane rotation by a signed swap retains a real plane rotation on the relabelled pair.

If every edge is a local extremum of the temporal ranks around the cycle, the local minima and maxima alternate, hence $\ell=2m$ is even. Adjacent minima precede their neighboring maxima. All other minima-maxima pairs are disjoint, so they commute; the word rearranges into a first matching followed by a second matching. The case $m=2$ is already known. The following proof treats every $m\ge3$ simultaneously.

## 3. Alternating cycles: the routing law and its forced marginals

Write the $2m$ coordinates as $u_i,v_i$ for $i$ modulo $m$; the first parallel layer has pairs $A_i=(u_i,v_i)$ and the second pairs $B_i=(v_i,u_{i+1})$. Give every gate in these local orders the same block
\[
     \begin{pmatrix}c&s\\-s&c\end{pmatrix},\qquad
     c,s>0,\quad c^2+s^2=1.
\]
Put $p=c^2$ and $L=2m$. We show that (1) is impossible whenever $0<p<1/3$.

A permutation with positive mass under (1) must send the two inputs in $A_i$ one each to the output blocks $B_{i-1},B_i$. Size-one minors vanish to all other output blocks. Moreover the two-by-two transfer block to either permitted block has rank at most one, because its unique common middle coordinate is one-dimensional. Hence (1) at size two forbids sending both inputs to the same permitted block. For any such permutation, the middle port assigned to an input is determined by its output block; the final port assignment to the two output labels then determines the switch at that output block. It follows that the permitted permutations are precisely the unique deterministic routings with switch bits $b\in\{0,1\}^L$, where bit 0 means do not exchange the two local coordinates and bit 1 means exchange. Let $q(b)$ be the probability mass in a possible law (1). For comparison let
\[
   q_0(b)=p^{L-|b|}(1-p)^{|b|}
\]
be the independent switch law.

The bipartite overlap graph of the first and second gates is a cycle on $L$ vertices, with middle coordinates as its edges. A set of occupied middle coordinates gives each gate an occupation count of $0,1,$ or $2$. Call a gate active if its count is $1$. Counts at the first gates are the selected input counts and those at the second gates are the selected output counts.

**Every marginal omitting two specified switch bits is the product marginal.** For any chosen two gates, choose middle occupations so that just those two gates are inactive: walk around the overlap cycle and toggle the occupation bit as one passes each active gate; the number of toggles is even. Given any switch assignment at the active gates, prescribe the selected input and output sets by its routing of these occupations. The inactive gate counts are 0 or 2, so each fixes both adjacent middle occupations, and all other counts then propagate these fixed occupations uniquely around the cycle. Consequently the event that a permitted permutation maps the prescribed input set to the output set fixes exactly the specified active bits and no others. In the exterior-power product the same counts give just one intermediate set. Its squared amplitude is the product of the active gate probabilities, since an inactive block contributes a minor of modulus 1. Equation (1) thus gives exactly the stated marginal.

**Every complementary pair of bit vectors has a fixed interference.** Start instead with the alternating middle set consisting of all $u_i$; every gate is active. Given $b$, prescribe inputs and outputs by that routing. There are exactly two intermediate sets allowed by the counts, the given alternating set and its complement. The corresponding switch vectors are $b$ and $\bar b$, with every bit flipped. The amplitudes for the two exterior-power paths give
\[
 q(b)+q(\bar b)
  =q_0(b)+q_0(\bar b)
     +2(-1)^{m-1+|b|}(cs)^L.
\tag{2}
\]
To check the sign, order selected inputs by their $A_i$ and selected outputs by their $B_i$. The two induced bijections differ by a cyclic shift of $m$ blocks, of sign $(-1)^{m-1}$. Changing to the natural input and output orders gives a common factor for both amplitudes. At a first gate the two local entries use one input column and the two output rows; their product is $-cs$ for bit 0 in the specified first-port routing and $cs$ for bit 1. At a second gate the specified middle set uses its second input port; the two entries use one output row and the two input columns, again giving $-cs$ for bit 0 and $cs$ for bit 1. Multiplying across the even number $L$ of gates gives the extra sign $(-1)^{|b|}$ and magnitude $(cs)^L$. This proves (2) for all $b$.

## 4. The Fourier obstruction

Let $d=q-q_0$ as a function of switch bits. The marginals just proved imply that all Walsh coefficients of degrees at most $L-2$ vanish. Hence for suitable real $D,E_i$,
\[
 d(b)=(-1)^{|b|}\left(D+\sum_{i=1}^L E_i(-1)^{b_i}\right).
\tag{3}
\]
Complementing all bits preserves the even-degree term and reverses the odd-degree terms. Equation (2) therefore forces $D=(-1)^{m-1}(cs)^L$. If a nonnegative law $q$ existed, average $q$ over all permutations of its $L$ bit positions. The independent law is invariant and (3) is stable under these permutations, so one obtains a nonnegative function of this necessary form with all $E_i$ equal, say $E$. This step does not require the original minor observations to be invariant under arbitrary bit-position permutations.

Put $x=(1-p)/p$ and $\tau=2E/D$. At Hamming weight $m+k$, divide the averaged mass by $(cs)^L$ to obtain
\[
          x^k-(-1)^k(1-\tau k).
\]
Since $m\ge3$, both $k=-2$ and $k=-3$ occur. Their nonnegativity requires
\[
 -\frac{1+x^{-3}}{3}\le\tau\le\frac{x^{-2}-1}{2}.
\tag{4}
\]
At $x=2$ these endpoints agree. For $x>2$ the lower endpoint strictly increases from that common value and the upper endpoint strictly decreases. This contradicts (4) whenever $p<1/3$. Thus all even alternating cycles of length at least six fail, completing the inductive obstruction for every simple support cycle of length at least four.

The proof gives a reusable distinction: size-one and size-two support can pin down the permitted routings, while higher-order minors detect coherent interference that cannot be assigned nonnegative routing weights. It says nothing about a convex representation whose coefficients are allowed to depend on the spectra.

**Reproduction.** Run `python3 -O verify_marcus_distinct_support.py`. It replays every four-cycle order and every interposed triangle-pendant order against the required small separating certificates. Independently, it enumerates all complementary-pair interference observations and all two-omitted marginal observations for alternating cycles of lengths 6, 8 and 10 with rational gates $(c,s)=(5,12)/13$, computing each minor by exact fraction-free elimination. The all-length proof is the routing and Walsh argument above.
