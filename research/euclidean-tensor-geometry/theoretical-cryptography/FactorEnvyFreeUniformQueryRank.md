# Exact envy-free division needs n(n−1) queries on the uniform profile

Use the normalized ordinary Robertson–Webb interval model. Each
agent's density integrates to one. An Eval returns the mass of one
interval. A legal Cut starting at a, with a target t in a prescribed
bracket, returns b with mass \(t\) on \([a,b]\). Output shares form a
complete partition into finite unions of intervals. We allow arbitrary
real endpoints both in queries and in outputs, with no charge for
the latter; the lower bound therefore also holds when all endpoints
must have been previously introduced. All the hard profiles can have
finite-step densities in \([1/2,3/2]\), so Cut roots are unique.
Exact envy-freeness means each person prefers their share to every
other, either by maximizing cake value or by minimizing chore cost.

**Theorem.** For every \(n\ge2\), any correct deterministic protocol
has at least \(n(n-1)\) answered queries on the input where every
density is identically one, including at least \(n-1\) to each
agent. The same assertion holds almost surely for a measurable
randomized protocol that returns a correct allocation with
probability one on each input, even with arbitrary input-independent
ideal-real randomness. More generally, a per-input zero-error
protocol allowed to abstain or not return incurs at least this many
answered queries on almost every uniform-input tape that returns
an allocation. Hence its expected uniform cost is at least
\(n(n-1)\) times its probability of returning there.

The uniform-input bound is sharp, with or without requiring cut
coordinates to come from the oracle: one can test a certified equal
partition in exactly \(n(n-1)\) queries, with a general protocol
used only on failed tests. This does **not** determine the minimum
worst-case cost over profiles. For four cake agents we obtain a
worst-case lower bound 12; the published
[Amanatidis–Christodoulou–Fearnley–Markakis–Psomas–Vakaliou protocol](https://www.cs.cmu.edu/~cpsomas/envy_free.pdf)
gives the separate bound 171 (61 Cut and 110 Eval calls).

[Procaccia (2009)](https://ijcai.org/proceedings/2009/49) established
a quadratic deterministic lower bound with a uniform-response
adversary. [Farhadi–Hajiaghayi, v2, Theorem 2.3 and Appendix G](https://arxiv.org/html/2611.11424v2#S2.SS3)
give an expected-cost bound on the uniform profile that applies
even under a success probability \(p<1\) with possible wrong
returns; at \(p=1\) their displayed bound is \(n(n-1)/2\).
Our result improves that endpoint by a factor two and is
almost sure at the endpoint. It does not improve their
two-sided-error result for \(p<1\). The additional ingredients
here are a transcript rank obstruction for tied comparisons
and a countable family of replay-preserving perturbations.

## 1. The interval span of a transcript

Fix a successful finite transcript and output \((P_1,\ldots,P_n)\)
on some baseline of strictly interior finite-step densities,
for instance the uniform input. For agent i record the determining
interval of each query: the interval of an Eval, or \([a,b]\)
if a Cut from a returns b. Add the always-known normalization
interval \([0,1]\). Let \(V_i\) be the real linear span of
the indicators of these intervals, with endpoint values ignored.

**Tie lemma.** For every other agent j with equal baseline
i-values of \(P_i,P_j\), any transcript certifying this output
throughout the density class must have
\(\mathbf1_{P_i}-\mathbf1_{P_j}\in V_i\).
Otherwise there is a density in the class, changing only agent
i, that gives the same whole transcript but reverses the tie
in the unfavorable direction. Its difference from the baseline
can be chosen to be a rational step function with rational
endpoints and heights, arbitrarily small in supremum norm.

Indeed, partition the cake into finitely many open cells using
all determining endpoints and all output boundaries.
A perturbation with integrated mass \(u_k\) in cell k changes
a determining answer by the dot product of u with its
interval's \(0,1\) incidence row. The contrast indicator has
a row c with entries \(0,\pm1\). If c is outside the span of
the determining rows, rational Gaussian elimination gives a
rational u annihilating all of them but with \(c\cdot u\ne0\).
Choose its sign to make the selected comparison unfair,
different signs for cake and chores. Inside each nonempty
open cell choose a positive-length rational-endpoint
subinterval and place the desired perturbation mass there
with constant rational density. Disjointness of cells and
finiteness allow a common positive rational scaling as
small as desired. Thus the density remains in \([1/2,3/2]\);
the total mass is unchanged by the normalization row.

An answered Cut is replayed because its determining mass
is unchanged and positivity makes the original endpoint the
unique root in its bracket. Other agents' queries are
unchanged. Inductively, an adaptive algorithm with the same
tape sees the identical finite transcript and produces the
same allocation. If the model permits oracle responses
reporting an out-of-range target, such a response on the
fixed finite path is a strict inequality with a positive
gap. A further sufficiently small scaling preserves every
such inequality; it never helps the rank budget. Valuation-
independent syntax failures equally give no information.
The ordinary model can instead just require legal queries.

## 2. Uniform lower bound and the randomness quantifier

On the uniform baseline, any complete exactly envy-free
allocation has \(|P_j|=1/n\) for every j, for both cake and
chores. For fixed i the \(n-1\) contrasts
\(\mathbf1_{P_i}-\mathbf1_{P_j}\), \(j\ne i\), are linearly
independent: restrict a vanishing linear combination to
each positive-measure \(P_j\), \(j\ne i\). They have zero
integral, and thus the normalization function
\(\mathbf1_{[0,1]}\) is independent of them. The rank of
\(V_i\) is therefore at least n, since every tie falls
under the lemma. Each answered query contributes at most
one interval row, so i must receive at least \(n-1\)
answered queries. Summing proves the deterministic bound.

For the probabilistic assertion, let \(\mathcal D\) be the
**countable fixed family** of profiles obtained by adding
one finite rational step function to one agent's uniform
density, with densities in \([1/2,3/2]\) and total mass one,
together with the uniform profile. This family is independent
of the tape, including even if every query or output
coordinate is itself an arbitrary ideal real. For a zero-error
protocol, for each fixed profile in \(\mathcal D\) the set of
tapes returning an incorrect allocation on that profile is
null. The union of these bad-tape sets is still null.

Now take a tape outside the union which returns on uniform.
If some contrast is not in its determining span, the tie
lemma constructs a witness in \(\mathcal D\) for that tape.
The tape returns the same allocation on this witness and
is wrong, contrary to how the tape was chosen. Thus every
uniform return outside the one null set has the full rank
for all n agents. In particular on a Las Vegas algorithm
the lower bound holds almost surely, not just on average.
For a correct-or-abstain algorithm it holds on almost every
returning tape. This argument does not treat a wrong return
as an abstention: it requires measure zero of wrong returns on
every input. For two-sided error, countably many positive-error
events cannot be discarded this way.

For sharpness on the uniform profile, ask the first agent
for her \(n-1\) successive landmarks at cumulative masses
\(j/n\) from the left endpoint. They partition the cake into
n equal pieces for that agent. Ask each of the other \(n-1\)
agents to evaluate the first \(n-1\) of those intervals. If
all those evaluations are \(1/n\), normalization supplies
the final value and assigning one piece each is certified
envy-free (or chore-envy-free). Otherwise use a general protocol suitable for the class, such as
[Aziz–Mackenzie](https://arxiv.org/abs/1604.03655) for cake or
[Farhadi–Hajiaghayi, Theorem 2.1](https://arxiv.org/html/2611.11424v2#S2.SS1)
for chores. This test uses \(n-1\)
Cut calls and \((n-1)^2\) Eval calls on every input, passes
on uniform, and uses only existing coordinates. It proves
sharpness of the uniform cost, not of the total fallback
cost on other profiles.

## 3. A graph criterion for the rank and one explicit witness

For each agent build an endpoint graph with a vertex at
each determining or output endpoint, and an edge from a to
b for each determining interval \([a,b]\), including the
normalization edge \((0,1)\). The endpoint derivative of a
step function is its vector of jumps after extending it
by zero outside the cake. This is an injective linear map
on the step functions; an interval indicator maps to
\(e_a-e_b\). On each graph component these edge differences
span exactly the coordinate vectors summing to zero
there, as follows from any spanning tree. Therefore a
contrast is determined if and only if its signed jumps
sum to zero on every component. The rank of an agent's
interval span is the number of vertices minus the number
of components, counting isolated output endpoints.
In an equality transcript on uniform the span is exactly
the span of the n piece indicators. In particular every
determining interval is then, up to endpoints, a union of
whole output pieces; redundant interval equations cannot
count toward equality.

Example: consider four consecutive quarter pieces and one
agent queried for \([0,1/2]\) and \([1/4,3/4]\), with
normalization also known. Every output boundary is touched
but not all piece contrasts are determined. The modified
density taking values \(3/4,5/4,3/4,5/4\) on the quarters
preserves both replies \(1/2\) and the total. It changes the
first two quarter values to \(3/16,5/16\); an agent allocated
the first quarter as cake then envies the second owner.
Negate the perturbation for chores.

The optional checker
~~~sh
python3 verify_factor_envy_free_uniform_query_rank.py
~~~
checks the explicit four-piece lower/upper certificates and
replays the exact rational linear separation and endpoint
graph criterion on a fixed collection of finite partitions.
No computational enumeration is needed for the theorems.
