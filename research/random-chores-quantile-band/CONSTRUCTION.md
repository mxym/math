# A distribution-class-dependent linear improvement below two chores per agent

This is the structural companion to [the fixed-law characterization](PROOF.md). There are n agents, m indivisible chores, iid nonnegative costs in [0,1] from one nonatomic CDF F, additive disutility, and all chores must be allocated. A complete allocation is envy-free (EF) if every agent values her own bundle at cost no higher than each other bundle. Fix a,b>0 and assume for some fixed x₀>0 that

$$
ax\le F(x)\le bx\qquad (0\le x\le x_0).
$$

A PDF bounded globally between a and b satisfies this; no continuity of a density is required. The law does not vary with n.

**Theorem.** There is δ=δ(b/a)>0 such that for every fixed F as above and every sequence 1≤k=2n−m≤δn, with probability tending to one there is a complete EF allocation with exactly k singleton and n−k doubleton bundles. One may use

$$
d=24,\quad L=5+3d^2,\quad p=\exp[-2(b/a)L],\quad \delta=\min\left\{\frac1{2d},\frac p{6(d^2+1)}\right\}.
$$

This explicit small constant is not a proposed threshold. Combining with the known sufficient theorem for m≥2n gives a sufficient coefficient 2−δ for each class with fixed two-sided global density bounds. For the broader, merely local CDF hypotheses the theorem itself only asserts the stated band below 2n.

**Corollary in the band.** If F(x)/x tends to a positive finite ℓ at zero, choose a=ℓ/2 and b=2ℓ locally. The same strictly positive δ(4) works in the stated band for *every fixed such F* (the rate of convergence can depend on F). This covers, in particular, the uniform law, and every density with a positive finite limit at zero. No uniformity in the sample size needed across an unrestricted class of laws is asserted.

## 1. Two bounds on exponential optimal assignments

In a square N×N iid Exp(1) array, the optimum perfect assignment is almost surely unique (finitely many continuous nontrivial cost differences) and its permutation is uniform by column symmetry. By Linusson–Wästlund's and Nair–Prabhakar–Sharma's proofs of the Parisi formula, its expected total is Σ_{i=1}^N i^−2 <2. We use the following two simultaneous high-probability bounds: its total is at most 3, and every selected entry is at most M_N=C log²N/N for an absolute sufficiently large C.

Join entries of cost ≤16 log N/N. For s≤N/4 the probability that some s rows have all their neighbors among some 2s columns is at most

$$
\binom Ns\binom N{2s}\exp\!\left[-\frac{16s(N-2s)\log N}{N}\right]\le N^{-5s}.
$$

Use a union bound over s and transpose for the other side. Any two opposite sets of size ≥N/4 have a joining edge whp, since 4^N exp(−N log N)→0. On this event, for *any* permutation π draw an arc u→v when entry (u,π(v)) is cheap. All directed distances are O(log N): reachable sets in each direction grow at least twofold while of size ≤N/4, and the two large sets have an arc between them. For any i with expensive edge (i,π(i)), take a cheap successor j≠i and a shortest j→i path. This cycle reassigns i and its other rows at total cost O(log²N/N), strictly less than M_N by choosing C large. The short alternating-cycle mechanism is classical; the argument concerns exponential optima, not a claim that a nonlinear transform preserves an optimum permutation.

Cap every entry at M_N and let W^cap be its optimum total. Changing one entire row changes W^cap by at most M_N (use an old optimum in the new instance and vice versa). The N independent rows and bounded differences give Pr(W^cap>E W^cap+1)≤exp(−2/(N M_N²))→0. Its expectation is at most the uncapped expectation <2. On the good cheap-graph event no capped optimum can use a capped edge: the cheap-cycle reassignment just given costs strictly less than M_N, even after capping. Thus the capped and uncapped optima agree there, proving both claimed bounds.

## 2. Reserve cheap singleton candidates; prepare independent rectangular layers

Let N=n−k. Split the m actual chores into n A-columns and N B-columns. Reserve r=⌊n/2⌋ specified A-columns. Generate independent unit exponentials X in the A array: actual cost at an entry is F^−1(1−exp(−X)), with generalized inverse. In reserve order give each column to its cheapest still unused row in X and remove that row from the available group. Assign the remaining n−r rows bijectively to the remaining n−r A-columns using their minimum exponential assignment. Write a_i for i's A-column and X_i for the chosen exponential entry.

In the j-th reserved column the minimum is Exp(n−j+1), independently of previous minimum values (its conditional distribution given earlier columns is the same). Their total has mean at most 1 and variance O(1/n), so is ≤2 whp. All are O(log n/n) whp by exponential tails. The residual independent square array obeys §1, so ΣX_i≤5 and max X_i=O(log²n/n) whp.

Choose fixed pairwise disjoint row sets O₁,…,O_d, each of size k, possible since dk≤n. The sets are determined *before* observing any entries. For B generate d independent n×N iid Exp(1) arrays Y^h, independent also of A, including cells in omitted rows. Actual B cost at (i,j) is

$$
F^{-1}\!\left(1-\exp\!\left[-d\min_h Y^h_{ij}\right]\right).
$$

These entries are iid F, independent of A; d times the minimum is Exp(1). In layer h take the optimal exponential bijection π_h between [n] minus O_h and all N B-columns. These independent permutations are uniform bijections of their specified domains. Use their edges as B candidates; row degrees counting colors are d or d−1, column degrees d. No assertion that these edges are independent of the actual costs is needed.

Put

$$
T_i=\frac{X_i+d\max_{h:\,i\notin O_h}Y^h_{i,\pi_h(i)}}a.
$$

With probability tending to one, ΣT_i≤L/a and max T_i≤τ=C' log²n/n with a suitable fixed C', by §1 in the d independent squares (N≥(1−δ)n) and the A bounds. On this same event, for sufficiently large n, all selected raw exponentials in either kind of array are so small that their arguments u in F^−1 satisfy u≤a x₀. Since F^−1(u)≤u/a for those u, 1−exp(−x)≤x, and the minimum in the true B cost is ≤the corresponding chosen Y, own cost for A alone or A with any candidate is ≤T_i. The event of these raw budget bounds only uses the reserved winners/minima and the unreserved assignment and B data; it does not expose the losing entries of reserved columns.

## 3. Linearly many safe singleton choices, with nonintersecting B neighborhoods

Reveal the reserved winners and their minimum values, the unreserved A-submatrix needed for matching, and B. Conditional on this information, the losing entries in a reserved column among its then-eligible rows are independent exponentials truncated below at the minimum, and entries in earlier removed rows are unrestricted independent exponentials. All these losing entries are conditionally independent across columns: after fixing the sequence of winning labels the eligible set in each column is fixed and the remaining conditioning restricts only within that column. T_i are measurable in the revealed data.

Call a reserve column safe if its cost to each row j other than its assigned owner exceeds T_j. Conditional on the data, different reserve columns are independently safe with potentially different probabilities. On our budget event, these probabilities are ≥∏_j(1−F(T_j))≥∏_j(1−bT_j)≥exp(−2bΣT_j)≥p for n large, because all T_j≤min(x₀,1/(2b)). Truncation below at a known minimum only increases the unconditioned actual cost stochastically. Since r∼n/2 and p>0 is fixed, binomial concentration gives ≥pn/5 safe columns whp. Their distinct owners comprise H.

Select from H at least |H|/(d²+1) owners with pairwise disjoint B neighborhoods: in their conflict graph join two rows sharing a candidate column; its degree is at most d(d−1)≤d². A greedy independent set attains the claimed size. This is after seeing all data as needed; no independence of H and B is presumed. Retain exactly k selected owners as S; the inequality k≤pn/[6(d²+1)] leaves slack. Delete S from the candidate graph. Each B-column loses at most one *distinct* neighboring row, but it can have parallel incidences to that row. This multiplicity is accounted for in §4.

## 4. Conflicts, lost incidences, and local resilience

Mark all n×m *actual* cost entries ≤τ. These are independent Bernoulli with parameter F(τ)≤bτ. Whp distinct 4-cycles in this graph share no vertex. Two meeting distinct 4-cycles have a connected simple union with e≥v+1; finitely many union types each occur with probability O(n^v(bτ)^e)=o(1). The use of overlapping K₂,₂ to remove two-item envy conflicts and then invoke matching resilience is due to Manurangsi–Suksompong in the goods setting; their binomial graph is not this union of rectangular assignment permutations.

In the candidate multigraph call a row-column pair (i,j) bad if another row z≠i has both A-column a_i and B-column j marked. Because row i's own cells in its chosen A and each candidate B are marked on the budget event, a bad edge determines a 4-cycle through rows i,z and distinct columns a_i,j. Distinct bad edges sharing a row give distinct cycles (different B-columns); distinct bad edges sharing a B-column give distinct cycles (distinct A-columns). Thus whp the set of distinct bad pairs is a matching. Remove every copy of each such edge.

For each vertex there is whp at most *one excess parallel incidence in total* beyond its number of distinct neighbors. Indeed at a fixed row, among at most d independent uniform choices in N labels, a triple collision or two disjoint pairs of collisions has probability O_d(N^−2). At a fixed column the choices are independent, each uniform on a subset of N row labels: the same bound applies by conditioning on one draw per pair (or one for a triple). A union bound over O(n) vertices proves the assertion. Thus removing ≤2 distinct neighbors of a vertex costs at most 3 incidences in total. A surviving B column loses at most two distinct neighbors, one to S and one to the deletion of bad pairs, hence ≤3 colors. A surviving row has at most one initially omitted color and at most one distinct bad neighbor (≤2 copies), so it too retains ≥d−3 colors. No degree bound is required of deleted rows.

Here is the expansion calculation for the nonidentical domains. Write q=3 and consider any s with 1≤s≤n/2. The probability that there exist s vertices U on one side and s vertices W on the other such that each element of U originally has edges of at least d−q colors into W is at most

$$
\left[e^2\left(\frac nN\right)^2\binom dq\left(\frac sN\right)^{d-q-2}\right]^s
$$

for each orientation. Choose U,W in ≤(en/s)^{2s} ways, then choose d−q colored demands per vertex. In a given layer an ineligible prescribed row makes the event impossible. Otherwise the probability that all t distinct prescribed images land in W is at most (s)_t/(N)_t≤(s/N)^t; in the reverse direction the set of eligible row destinations has intersection at most s with W. Multiply over the independent layers. This gives the displayed estimate. For d=24 and δ≤1/(2d), n/N≤12/11, and s/N≤6/11. The upper bound on the base at s=n/2 is <1/2: even 8(12/11)^2 binom(24,3)(6/11)^19<1/2. The sum for s≤√n tends to zero by a geometric bound whose ratio vanishes, and the remaining terms have an exponentially small sum. Therefore this bad small-set event fails whp on both sides.

In the surviving balanced graph of N rows and N columns, any Hall violation of size s≤n/2 has all its neighbors in a set W of size s of the original opposite side, contrary to the expansion result since each of its rows retains ≥d−3 colors. For a violation at s>n/2 take N−s+1 columns outside its neighborhood; their own neighborhood has size at most N−s. Since k≥1 this gives a violation on the other side of size ≤n/2. Hence a perfect matching survives.

## 5. Complete allocation and limitations

Give every row its A item. Those in S keep it alone; the remaining N get one B from the surviving perfect matching. The true cost of any agent's own bundle is ≤T_i. She does not envy any other singleton by safeness. Envying any other pair would mean both its costs to her are ≤τ, since costs are nonnegative; this would have removed its B-edge. So every real item has been allocated and exact EF holds. The coupled random experiment has precisely the original iid cost marginal, so existence holds whp in the original market.

There is no conflict with the repository's fixed-law-subsequence construction against *arbitrary* common coefficients below two across *all* PDF-bounded laws: its density contrast can depend on the proposed coefficient. We do not determine the optimal coefficient of any fixed law, prove a sharp threshold, or give an algorithmic complexity claim.
