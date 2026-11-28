# Linear-degree SoS gaps for sparse unit negacyclic likelihood instances

For each fixed prime \(q\ge5\) there are adversarial, grid-valued batches in the dyadic ring \(\mathbb F_q[X]/(X^d+1)\) whose maximum wrapped-Gaussian log-likelihood has a constant normalized gap at degree \(\Omega(d)\) in the natural coefficient-indicator sum-of-squares hierarchy. Every public row is a distinct invertible polynomial with at most three nonzero coefficients. One family uses only \(O(d)\) rows; a second family has the **whole public design fixed by dimension** and uses \(O(d^3)\) rows, so only the responses vary between instances. The gap also holds for the corresponding coefficient-Hamming objective and with standard local residual variables added. This is a proof-system lower bound on artificial worst-case data, not an assertion about independently uniform Ring-LWE coefficients or general algorithms.

## 1. The two objective encodings

Take \(R_d=\mathbb F_q[X]/(X^d+1)\), where \(d\) grows through powers of two. Embed each coefficient \(r\in\mathbb F_q\) into the circle by \(r/q\). For \(0<b<1\) let
\[
 f_b(x)=\sum_{j\in\mathbb Z}b^{j^2}e^{2\pi i jx},\quad h(x)=\log f_b(x),\quad
 H_q=\sum_{r\in\mathbb F_q}h(r/q).
\]
The positive periodized Gaussian formula gives \(f_b>0\); it is even, and \(f_b(0)>f_b(r/q)\) for any nonzero \(r\), by the first Fourier harmonic and the nonnegative contributions of the others. A row is an invertible \(a\in R_d\) and full grid response \(y\); its contribution at \(s\in R_d\) is \(\sum_{j<d}h(y_j-(as)_j/q)\). The alternate objective is the number of matching coefficients, rather than the number of mismatches. Both are maximization problems. Generally the objectives need not be affinely equivalent; the blocks used below make them so on these instances.

Use real one-hot coefficient variables \(Z_{i,r}\) and equations
\[
 \sum_r Z_{i,r}=1,\quad Z_{i,r}^2-Z_{i,r}=0,\quad Z_{i,r}Z_{i,r'}=0\quad(r\ne r').
 \tag{1}
\]
For a function \(F\) of the coordinates in a finite set \(I\), its indicator polynomial is
\[
 [F]_I=\sum_{\mathbf r\in\mathbb F_q^I}F(\mathbf r)\prod_{i\in I}Z_{i,r_i}.
\]
The degree is at most \(|I|\). When only a subset of \(I\) is needed for \(F\), the two representations agree modulo (1) with certificates of degree at most \(|I|\), by pulling out the factors \(\sum_r Z_{i,r}\). Each log-score or match term for a row of support at most three has such an encoding of degree at most three.

The second, augmented encoding adds variables for the one-hot residue of every individual response residual. Its exact local defining equations set each such variable equal to its indicator polynomial as above; the augmented objective is then linear in the residual indicators. Extra standard one-hot constraints on the residual indicators are allowed. The result below concerns these two specified encodings, not arbitrary extended proof systems.

## 2. Turning a block into a unary or ternary predicate

Let \(n\) be a power of two, and use the first \(n\) secret coordinates \(s_0,\ldots,s_{n-1}\) as vertices. For \(I\subseteq\{0,\ldots,n-1\}\) of size \(1\) or \(3\), use
\[
 a_I=\sum_{i\in I}X^{-i},\qquad z_I=(a_I s)_0=\sum_{i\in I}s_i.
\]
Choose \(d=C_q n\) with a sufficiently large fixed power-of-two constant, also allowed to depend on the fixed clause degree bound used later. We need \(n<d/2\) and \(n\le\operatorname{ord}_{2d}(q)\). The latter is possible because all the irreducible factors of \(X^d+1\bmod q\) have degree \(\operatorname{ord}_{2d}(q)=\rho_q d\) with a positive eventual constant \(\rho_q\): roots have exact order \(2d\) and \(v_2(q^{2^j}-1)=v_2(q^2-1)+j-1\) for \(j\ge1\). After factoring out \(X^{-\max I}\), the remaining nonzero polynomial has degree \(<n\), so is not divisible by any factor. Thus every nonzero scalar multiple of \(a_I\), as well as every signed cyclic shift of it, is a unit.

A block for \(I\) has \(2q\) rows for each \(u\in\mathbb F_q^\times\), with unshifted coefficient \(u a_I\). At every nuisance coordinate \(j\ne0\) choose each possible grid phase \(r/q\) twice across those rows. In an **active block** with a prescribed two-element set \(C\subset\mathbb F_q\), use active coordinate targets \(u c/q\) with multiplicity \(q\) for each \(c\in C\). In an **inactive block**, use each grid phase twice also at the active coordinate. The multiset at coordinate zero is assigned freely, independently of the nuisance phase order.

The nuisance score cancels to a constant, \(2H_q\) per coordinate and per \(u\). At the active coordinate the sum for an active block is
\[
 q\sum_{c\in C}\sum_{u\ne0}h(u(c-z_I)/q)
 =2q(H_q-h(0))+\kappa\,\mathbf1_{\{z_I\in C\}},
 \qquad \kappa=q\{qh(0)-H_q\}>0.
 \tag{2}
\]
For \(c=z_I\) the inner sum is \((q-1)h(0)\); otherwise \(u(c-z_I)\) ranges over all nonzero residues. The inactive block is constant. For coefficient matches the same construction gives constant nuisance contributions and active contribution \(q(q-1)\mathbf1_{\{z_I\in C\}}\), with an inactive constant.

All public rows can be made distinct without changing these sums. Replace each unshifted pair by \((X^t u a_I,X^t y)\); the observation shift is the signed coordinate permutation on the real torus. The likelihood and matches are unchanged by evenness and by permutation. A support inside an arc of length \(<n<d/2\) has a unique external gap of length \(>d/2\) (for a singleton the unique cyclic gap is the whole circle). It follows that no nonidentity cyclic translation stabilizes it, and its orbit is determined by its sorted relative positions from the first point after that gap. For supports generated by \(I\subseteq[0,n-1]\), each translation orbit of triples contains at most \(n\) of the supports; the singleton orbit has \(n\). To distinguish rows, assign distinct translates within each orbit, without requiring the same translates across different orbits. There are \(d\) translates available in each orbit. At fixed \(q\) and fixed block multiplicity per support this fits by increasing \(C_q\). This argument preserves the linear dimension; requiring all pairwise separations distinct would unnecessarily use a quadratic dimension here.

These equalities also hold **at the level of degree-three indicator polynomials modulo (1)**. On each local support the phase identity is pointwise and its one-hot expansion is linear in the tabulated values of the local function. Rows related by a signed shift can have the columns relabeled and their real score negations removed before doing the expansion. Constants are reduced using \(\sum_r Z_{i,r}=1\), of degree at most the local support size when multiplied by the other sums. Thus no use of the global integer optimum, or of high-degree polynomial identities, is needed to obtain (2) in the specified SoS encodings.

## 3. A bounded-occurrence Boolean gap source

Use [Schoenebeck, Linear Level Lasserre Lower Bounds for Certain k-CSPs, full version](https://schoeneb.people.si.umich.edu/papers/LasserreNew.pdf), Theorem 12 with \(k=3\), size exponent zero, a sufficiently large fixed density, and soundness slack \(1/8\). For instance one can take \(m=32n\) independent uniform three-variable XOR clauses on \(n\) Boolean variables with independent parity bits. With probability \(1-o(1)\), no assignment satisfies more than \(5m/8\) clauses, whereas the corresponding Lasserre system at \(r=\Omega(n)\) rounds assigns local satisfaction one to every clause. The convention for Lasserre is the source's Definition 5 and Claims 6–7.

We additionally require bounded occurrences. For a fixed large \(D_*\), discard every clause incident to a variable whose original degree exceeds \(D_*\). Conditional on one triple, an incidence has remaining degree \(\operatorname{Bin}(m-1,3/n)\). The factorial-moment tail bound gives
\[
 \mathbb E(\#\text{discarded})
 \le 3m(96^{D_*}/D_*!) .
\]
Take \(D_*\) fixed so this is at most \(m/32\). Markov already gives probability at least \(3/4\) of discarding at most \(m/8\); this suffices simultaneously with the preceding high-probability events. Moreover repeated unordered triples have probability \(O(1/n)\) by the union bound over pairs of clauses. Thus for every large dyadic \(n\) there is a source instance with distinct retained triples, \(m'\ge7m/8\), maximum degree \(D_*\), Boolean optimum at most \(5m/8\le5m'/7\), and the same \(r\)-round Lasserre witness for all retained clauses. Deleting constraints only weakens the source feasibility requirement. We are not assuming an unproved SoS theorem on a bounded-degree distribution.

For clarity, the source vector witness yields a Boolean degree-\(2r\) pseudoexpectation as follows. For the squarefree monomial \(x_A=\prod_{i\in A}x_i\), put \(\widetilde{\mathbb E}x_A=\langle v_{x_B},v_{x_C}\rangle\) for any partition \(A=B\sqcup C\) with \(|B|,|C|\le r\). The product consistency identity in Definition 5 makes this well-defined; reducing modulo \(x_i^2=x_i\) gives a functional on all polynomials through degree \(2r\). The Gram matrix gives positivity on squares up to this degree. For any local indicator on at most \(r\) Boolean variables, the source consistency and disjoint additivity identify its moment with its local probability. For a falsifying assignment indicator \(f\) of a retained clause, Claim 7 gives \(v_f=0\). It actually annihilates every allowed multiplier of degree at most \(2r-3\): split a squarefree multiplier into parts \(g_1,g_2\) with \(\deg g_1\le r-3,\deg g_2\le r\); then \(fg_1\) is an indicator on at most \(r\) variables and \(\|v_{fg_1}\|^2=\langle v_{fg_1},v_f\rangle=0\) by product consistency. Hence \(\widetilde{\mathbb E}[fg_1g_2]=0\). This also justifies the localizing constraints used below, not only expected clause values.

## 4. Score gap and proof-system transfer

For every retained triple with parity \(a\in\{0,1\}\), give its active block \(C=\{0,2\}\) for \(a=0\) or \(C=\{1,3\}\) for \(a=1\). On Boolean values the sum of three bits lies in \(0,1,2,3\), with no collision modulo any prime \(q\ge5\); membership in those sets is exactly parity satisfaction. Also give each of the first \(n\) coordinates \(W=D_*+1\) unary blocks with \(C=\{0,1\}\). For the sparse-row family these are all the blocks. For the fixed-design family allocate one block for *every* possible unordered triple, and set every unused one inactive; all unary blocks are always active. The fixed family has the same sorted order, shifts, scalars and rows for all source formulas of a given \(n\). The orbit count in Section 2 guarantees all rows are distinct for this denser family, even though their total number can exceed \(d\). The two row counts are \(2q(q-1)(Wn+m')=O(d)\) and \(2q(q-1)(Wn+\binom n3)=O(d^3)\), respectively.

For either family, subtracting the explicitly known block baseline and dividing by the positive reward coefficient gives the same polynomial objective modulo (1):
\[
 G(s)= W\sum_{i<n}\mathbf1_{\{s_i\in\{0,1\}\}}
       +\sum_{\text{retained triples }I}\mathbf1_{\{z_I\in C_I\}}.
 \tag{3}
\]
Every actual maximizer uses only Boolean values on the first \(n\) coordinates. If \(s_i\) is non-Boolean, replacing it by zero improves the unary part by \(W\) and loses at most \(D_*\) clause rewards; all remaining coordinates are unrestricted. Therefore the true maximum is at most \(Wn+5m'/7\). This is a constant relative gap to \(Wn+m'\), since \(m'/n\) is bounded above and below by positive constants and \(W\) is fixed. One can also normalize \((G-Wn)/m'\) to get upper value \(5/7\) and relaxed value \(1\). These are gaps in an explicitly centered objective, not multiplicative approximation claims about a raw likelihood.

To lift the Boolean pseudoexpectation, substitute \(Z_{i,1}\mapsto x_i\), \(Z_{i,0}\mapsto 1-x_i\), other residues to zero on \(i<n\), and fix each unused coefficient to zero. This uses degree one. All one-hot equations are Boolean identities under the substitution. The unary score is identically \(Wn\); every retained clause is satisfied under the pseudoexpectation, so the degree-\(\Omega(d)\) relaxation admits the *pseudo* value \(Wn+m'\), despite the strictly lower true value. More precisely, choose any degree cutoff at most a sufficiently small constant multiple of \(r\). Positivity for squares and the equality constraints follow by substitution into the source pseudoexpectation. If one encodes the false inequality \(G\ge Wn+m'\) as a localizing constraint for SoS refutation, the score difference after substitution is a sum of negatives of local forbidden-assignment indicators. The annihilation argument in Section 3 gives zero on all its allowed localizing multipliers. Thus there is no SoS refutation at that degree in this formulation.

For the augmented encoding, additionally substitute each residual indicator by its local degree-at-most-three polynomial in the Boolean source coordinates (given the fixed row and fixed response value). Its consistency and one-hot equations hold identically modulo the Boolean equations. Substitution can multiply degrees by at most three, so lowering the degree cutoff by at most this constant factor retains the same pseudoexpectation and degree-\(\Omega(d)\) obstruction. This does not authorize adding arbitrary new equations or nonlinear extensions of unbounded degree.

The likelihood gap is stable under a small positive-measure perturbation of each circle observation, if desired. With \(L_b=\|h'\|_\infty\), moving each coordinate by at most \(\varepsilon\) changes each local table entry by at most \(L_b\varepsilon\). The same bound holds for its lifted pseudoexpectation since every such local table, of support at most three, is integrated against a genuine local marginal under the source witness. Taking \(\varepsilon<\kappa m'/(28\,T d L_b)\) keeps a positive additive separation between the true and pseudo objective values. For fixed \(b\), or \(b=\beta/d\) and fixed \(\beta>0\), this radius is inverse polynomial: in the latter case \(L_b=O(b)\) and \(\kappa=\Theta_q(b)\) by the first Fourier harmonic. This last statement is about stability of the **optimization gap**, not exact refutation of the same threshold after perturbation.

## 5. Scope

* [Schoenebeck's theorem](https://schoeneb.people.si.umich.edu/papers/LasserreNew.pdf) and [Tulsiani's SoS reduction framework](https://doi.org/10.1145/1536414.1536457) supply the prior proof-system ideas. The new part here is the linear-dimension unit negacyclic embedding, its complete-response phase balance, and the bounded-degree transfer to the specified likelihood/nearest-codeword formulations, including the two design regimes. We do not claim a new SoS lower bound for 3-XOR itself; in particular its exact-feasibility problem over \(\mathbb F_2\) is classically easy outside this hierarchy.
* [Our earlier fixed-sparse likelihood hardness note](https://github.com/mxym/math/blob/305aab03fea43ba9748ff4a62badc6e76c8f466f/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-fixed-sparse-likelihood-hardness.md) transfers graph and PCP gaps to two-term unit rows and a fixed design under polynomial dimensions. That deterministic NP-hardness is a different claim. This note gives a linear-degree unconditional certificate obstruction with three-term rows, and uses a degree-preserving embedding rather than relying on NP-hardness or on the PCP gap.
* The inputs here are chosen instances with unlikely sparse coefficients and engineered responses. There is **no** conclusion about random-coefficient samples, arbitrary classical running time, practical decoding, or any concrete cryptographic scheme. The accompanying verifier checks only finite identities on artificial examples.
