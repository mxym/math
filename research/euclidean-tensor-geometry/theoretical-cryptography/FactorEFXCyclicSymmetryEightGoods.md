# EFX for four agents and eight goods under a cyclic player symmetry

Let four agents have arbitrary normalized monotone valuations of bundles
of eight goods. Suppose that simultaneously rotating the agents by one
step and permuting the goods by some permutation \(\sigma\) preserves
all bundle comparisons. Formally, indices are modulo four and for every
agent \(i\) and bundles \(S,T\),
\[
        v_{i+1}(\sigma S)\le v_{i+1}(\sigma T)
             \quad\Longleftrightarrow\quad v_i(S)\le v_i(T).        \tag{1}
\]

**Theorem.** There is a complete EFX allocation, including the comparisons
obtained by deleting an item of zero marginal value. The allocation
need not respect the symmetry itself.

This is a distinct symmetry case from the
[alternating-symmetry theorem](FactorEFXAlternatingSymmetryEightGoods.md):
\(A_4\) has no four-cycle. Both results allow genuinely distinct and
nonadditive valuations. Neither gives EFX for arbitrary four-agent
monotone profiles on eight goods. That unrestricted question is the
first remaining \(m=n+4\) case in
[Akrami et al., arXiv:2604.18216v4, §7](https://arxiv.org/abs/2604.18216v4).
Their \(3\times8\) and \(m\ge n+5\) obstructions are not covered here.

## 1. Reduce to one four-orbit and a top singleton outside it

We can replace each valuation by the ordinal ranks of its distinct
values. The ranks satisfy equality under the simultaneous relabelling
in (1), because this is a bijection between all bundle orders.
Thus we can reason with exact numerical equality under the relabelling.

If the order of \(\sigma\) is divisible by eight, \(\sigma\) is an
eight-cycle (there are only eight goods). In that case distinct top
singletons can be matched to the agents. In general the same holds if
one top singleton belongs to a good orbit of size at least four under
the simultaneous action. The bipartite graph on the agents and that
orbit, with edges for top singletons, is biregular by transitivity.
If player degree is \(d>0\), good degree is \(e>0\), and the orbit
has \(s\ge4\) goods, then \(4d=se\).
For any group \(X\) of players, \(e|N(X)|\ge d|X|\ge e|X|\).
Hall's theorem gives distinct top singletons, and each agent gets
that good together with one other. All opponent bundles trim to
singletons, so this is EFX.

Otherwise raise the simultaneous relabelling to the odd part of its
order. The resulting permutation of the players is still a four-cycle
and the permutation of the goods has order dividing four. We can
therefore label both actions as those of one generator of \(C_4\).
The good orbits have sizes 1, 2 and 4. If none has size 4, the square
of the generator acts trivially on the goods and swaps each opposite
pair of players. Therefore there are at most two valuations, and
[Mahara's two-type theorem for general monotone valuations](https://doi.org/10.1287/moor.2022.0044)
gives EFX. If there are two size-four orbits, there is a top singleton
in a large orbit and the preceding matching argument applies.

The only remaining good-orbit types are
\[
                      (1,1,1,1,4),\quad (1,1,2,4),\quad (2,2,4).  \tag{2}
\]
Each has a top singleton outside the size-four orbit.

## 2. Six finite order problems

If a counterexample exists, preserve one strict violation for every
allocation while perturbing the value scale at player 0. The other
players' scales are transported by the action. A perturbation by a
sufficiently small multiple of \(|S|+\rho(S)\), with distinct
\(\rho(S)\in[0,1)\) and \(\rho(\varnothing)=0\), makes all distinct bundles strictly ordered,
all proper inclusions strict, and all nonempty values positive.
It can put a chosen originally maximal singleton first among ties.
An empty bundle then fails EFX for its recipient, as another bundle
contains at least two goods.

We use zero-based good labels. The first four goods are the short
orbits in the order in (2); the last four are a regular orbit labelled
\(4,5,6,7\). Relabel within the centralizer of the good action to sort
the fixed singleton values, orient each two-cycle so its first good
is more valuable to player 0, and place the favorite among the regular
orbit at label 4 by a shift within that orbit. When two two-cycles
are interchangeable, arrange that a top singleton lies in the first
one. Simultaneously reversing the cyclic labels of agents and goods,
while fixing player 0 and label 4, arranges that singleton 5 is
preferred to singleton 7. Reversal transforms the generator into its
inverse and preserves the class of profiles; the shorter orbits and
the other stated conventions are unchanged.

At \((1,1,1,1,4)\) this leaves just top 0; at \((2,2,4)\) it leaves
top 0 in the first two-cycle. At \((1,1,2,4)\) the top is either 0
(the preferred fixed good) or 2 (the preferred good of the two-cycle).
For top 0 in that case, distinguish 1, 2 or 4 as the next most
valuable singleton: these are the maximal representatives of the
three remaining good orbits. This gives six cases in total. No
comparison other than inclusions and the stated symmetry choices
is fixed in the base order.

It is sufficient to record ranks up to bundle size five. A surjection
onto four bundles has no larger bundle, and its one-deletion comparisons
use only sets of size at most four. The \(219\) rank variables are
one agent's ranks for these subsets; the other players' comparisons
are obtained by the inverse cyclic transport of the subsets. Any
strictly monotone feasible order on the recorded subsets extends to
larger subsets by putting them above all recorded sets, in increasing
cardinality. A strictly ordered solution can be ranked into integers
\(0,\ldots,218\). Conversely an integer solution with ties in unrelated
sets still gives monotone valuations, and any strict comparisons in
a finite witness system survive a sufficiently small perturbation.

## 3. Exact Hall obstruction test

For each of the \(1{,}701={8\brace4}\) unlabelled partitions into four
nonempty bundles, put an edge from player \(i\) to a bundle \(B\)
when assigning \(B\) to \(i\) would be EFX relative to the partition.
This is independent of which opponent would get another bundle.
A complete EFX assignment for this partition is a perfect matching.

Write \(R(i,B)\) for rejection of \(B\). It is the disjunction of
strict comparisons \(v_i(B)<v_i(T)\) for single-deletion subsets \(T\)
of other bundles. Every player accepts at least one bundle, namely a
favorite one, so size-one subsets of players cannot witness a Hall
failure. A failure is equivalent to the existence of a player set
\(X\) of size \(d=2,3,4\) and a bundle set \(Y\) of size \(5-d\)
such that all pairs \(X\times Y\) are rejected. Indeed the complement
of \(Y\) contains at most \(d-1\) possible neighbors; conversely the neighborhood of any
Hall-deficient \(X\) can be enlarged to such a complement. Therefore
for every partition impose the clause
\[
      \bigvee_{d=2}^4 \
      \bigvee_{\substack{|X|=d\\|Y|=5-d}}
                      \ \bigwedge_{i\in X,\ B\in Y} R(i,B).       \tag{3}
\]
Only one representative per simultaneous orbit of partitions is
needed; comparison (1) sends perfect matchings to perfect matchings.

The checker builds (3) exactly. It uses the transitive closure of the
base order to identify already true and already false comparisons.
If one target \(T\) is forced no larger than a different target \(T'\),
then \(v_i(B)<v_i(T)\) implies \(v_i(B)<v_i(T')\); dropping the former
from the rejection disjunction is valid. A Hall choice with an
impossible rejection is discarded, and requiring additional rejections
beyond another valid choice is redundant. These simplifications use
only forced order, not any numerical valuation guesses.

The conjunction of (3) over the partitions, together with the base
order, is unsatisfiable in all six cases. This is a finite exact
order computation, not a random search. It forces some partition
to have a perfect matching and hence proves the theorem.

## 4. Reproduction

Run `python3 verify_factor_efx_cyclic_eight_goods.py` in normal Python
with a Z3 executable or libz3. Each case can be exported as plain
SMT-LIB via `--case NAME --emit`. It uses quantifier-free difference
logic on the integers by default; `--bv` gives an equivalent exact
eight-bit rank formulation. The alternative `--match` builds the
failure condition independently of Hall rectangles: for all 24
labelled matchings of the partition, at least one edge is rejected.
A timeout or `unknown` is not accepted.

| Case name | Orbit types | Top / second if required | Partition reps | Defined rejection atoms | Hall constraints |
|---|---|---|---:|---:|---:|
| fixed | \(1,1,1,1,4\) | 0 | 461 | 1,995 | 96 |
| second_fixed | \(1,1,2,4\) | 0 / 1 | 457 | 1,945 | 69 |
| second_pair | \(1,1,2,4\) | 0 / 2 | 457 | 1,948 | 76 |
| second_four | \(1,1,2,4\) | 0 / 4 | 457 | 1,952 | 85 |
| pair_top | \(1,1,2,4\) | 2 | 457 | 2,051 | 136 |
| two_pairs | \(2,2,4\) | 0 | 457 | 2,051 | 138 |

All rows returned exact `unsat` in Hall mode and in the alternative
labelled-matching formulation using Z3 4.13.3. These are two encodings,
not two different solver engines. For the two rows with a top good in
a two-cycle, a separate pure-integer ordinal-closure search also refuted
the systems. The small-orbit case uses
Mahara's existing mathematical theorem, and the large-orbit top
case is proved above without computation. The new statement
excludes every cyclic four-player obstruction, not every
transitively symmetric profile (for example, symmetry by only a
Klein four group need not contain a four-cycle).
