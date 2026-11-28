# Five-orbit sharp bound for the dyadic-cycle problem

**Theorem.** A nonempty finite simple graph of minimum degree at least three, admitting a free abelian action with at most five vertex orbits, has a simple cycle of length \(4\), \(8\), or \(16\). There are connected cubic graphs of unbounded orders with exactly five orbits under a specified free cyclic action whose shortest power-of-two cycle has length 16.

This adds the entire five-orbit case to the [four-orbit theorem and relation-lattice certificate method](FactorErdosGyarfasAbelianFourOrbits.md). The result concerns existence of a dyadic cycle, not containment through each given vertex and not the unrestricted Erdős–Gyárfás conjecture. For comparison, [Ducoffe–Dumitru](https://arxiv.org/abs/2609.28594) obtain finite-order searches and structural restrictions on hypothetical minimal counterexamples, not this hypothesis on the orbit quotient.

## 1. Exhaust the five-layer quotients

The four-orbit result settles all smaller layer counts. Identify each of the five free orbits with a layer of the acting group. The reductions and edge-orbit deletions in the four-orbit proof are all local, except for invoking a smaller case if the layer graph becomes disconnected. They therefore apply verbatim: a disconnected graph on five layers has only components on at most four. More explicitly:

* Two nonopposite internal steps in one layer give a commuting square.
* Three parallel matchings on a pair of layers give the two-orbit three-matching result.
* A matched pair of layers with internal steps in both gives a square or an 8-cycle, as does a layer incident to two doubled pairs of layers.
* We may repeatedly remove a cross matching if both endpoint layers have degree greater than three, or remove the internal step orbit at a layer if its cross degree is already at least three. Apply the smaller case if the quotient becomes disconnected.

The possible remaining five-layer graphs are represented by \(\ell_i\in\{0,1,2\}\) for internal degrees and \(m_{ij}\in\{0,1,2\}\) for cross multiplicities. These must satisfy:
\[
\begin{gathered}
 \text{the underlying layer graph is connected and the doubled pairs are disjoint};\\
 d_i=\ell_i+\sum_{j\ne i}m_{ij}\ge3;\qquad
 m_{ij}>0\ \Longrightarrow\ {\ell_i\ell_j=0}\text{ and }\min(d_i,d_j)=3;\\
 \ell_i>0\ \Longrightarrow\ d_i-\ell_i\le2 .
\end{gathered}
\]
The [checker](verify_factor_erdos_gyarfas_five_orbits.py) enumerates the arrays, taking only admissible internal degrees for each cross multiplicity list. There are 4,405 labeled arrays and exactly 62 isomorphism types under five-layer relabeling. Arrays are encoded by the five \(\ell_i\)'s, followed by the ten \(m_{ij}\)'s in increasing pair order.

## 2. Check all assignments, not a finite list of group orders

For each of the 62 arrays the proof forms the universal label space \(\mathbb Z^b\) with the first matchings in a spanning tree set to zero (the greedy tree in increasing pair order). A generator represents each of the remaining cross matchings and each of the nonempty internal step orbits. The base relations \(R_0\) impose \(2x=0\) only for a genuine involution step. A required nonzero list imposes distinct labels on doubled links, nonzero involution steps, and \(2x\ne0\) on two-neighbor internal steps.

Given an evaluation \(\phi:\mathbb Z^b\to A\), a cyclic quotient walk lifts to a simple cycle precisely when its total \(w\) lies in \(\ker\phi\) and every partial-voltage difference \(d\) between two recorded vertices in the same layer is outside \(\ker\phi\). At a relation subgroup \(R\) known to lie in \(\ker\phi\), the certificate supplies a \(4\)-, \(8\)- or \(16\)-step walk with \(w\in R\) and every such \(d\notin R\). If the lift is not simple one of these \(d\)'s is zero after evaluation, so the next state is \(R+\mathbb Z d\). This is impossible if it contains an item from the required nonzero list. Otherwise the child state is checked, including all possible further collisions. All row-lattice calculations are over the integers, not over the rational span.

The [frozen decision certificate](erdos_gyarfas_five_orbit_certificate.json) has 378 reached nonterminal states over the 62 templates and maximum verified child depth five. The checker starts at the required \(R_0\), recomputes each child in integer Hermite form, checks every declared walk and every actual possible collision child, and verifies that all listed states are reached. The computation weighs neither the actual order of the acting group nor its torsion. Running the standard-library Python verifier beside the JSON file reproduces the coverage check.

## 3. A connected cubic sharp family with exactly five cyclic layers

Use template \(\texttt{000010111111100}\): the nonempty internal layer is layer 4, with one involution step. The simple cross edges are \(02,03,04,12,13,14,23\). Each layer has total degree three. Its four universal generators, in order, are the three cotree labels and then the involution label. Work first in the formal group \(\mathbb Z^3\times\mathbb Z/2\). An independent exact short-walk check visits all rooted directed cyclically nonbacktracking quotient walks of lengths 4 and 8, respectively 24 and 264. None lifts to a simple cycle in this formal group. Walk
\[
0,7,8,3,4,11,6,1,4,14,5,2,9,10,14,5
\]
does lift simply and has length 16 (indices are the checker’s directed arrows, not layer labels).

Take any odd integer \(M>16(1+33+33^2)\). Evaluate the first three generators at \(2,2\cdot33,2\cdot33^2\) in the cyclic group of order \(2M\), and the involution at \(M\). For any formal vector relevant to a walk of length at most 16 or its collision test, the three free coefficients lie in \([-16,16]\); their base-33 sum is either zero with all three coefficients zero or a nonzero integer of absolute value smaller than \(M\). Its doubled value plus the order-two contribution vanishes modulo \(2M\) exactly if both contributions vanish individually: for odd involution coefficient the sum is odd, and in the even case one tests divisibility of the base-33 sum by \(M\). Hence all short-walk checks remain valid, uniformly in \(M\). Tree shifts are zero, the fundamental cycle with first cotree generator gives shift \(2\), and the loop at layer 4 gives shift \(M\); since these generate the cyclic group the lift is connected. The translation action has exactly five orbits by construction.
