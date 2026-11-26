# Exact zero-error capacity for forest-supported affine codes of the seven-cycle

**Yongxian Zhang.** AI-assisted development and internal verification; no external peer review or priority claim.

For \(C_7\) take the symbols \(\mathbb F_7\), with confusability differences \(0,\pm1\). Call a code forest-supported if it is an affine subspace with a parity-check matrix in which each column has at most two nonzero entries, and the simple graph on check rows joining the supports of all two-entry columns is a forest. Several columns may have the same two-row support. This is a restriction on parity representations, not on the strong product defining the channel.

**Theorem.** The largest forest-supported zero-error code of each length \(n\) has exactly \(7^{\lfloor3n/5\rfloor}\) words. Its capacity is \(7^{3/5}=3.2140958497\ldots\). Thus forest-supported affine codes cannot approach the known unrestricted lower bounds. More generally, if an affine code has a parity-check matrix with at most two nonzeros per column and one can delete \(D\) columns to make the support graph a forest, then its dimension is at most \((3n+2D)/5\). In particular, deleting \(o(n)\) columns does not allow a higher asymptotic rate.

## 1. Signed residuals and local spectral interpolation

For a zero-error linear code \(L=\ker H\), no nonzero vector with entries in \(\{0,\pm1\}\) lies in \(L\). Equivalently all binary subset sums of the columns of \(H\) are distinct. Translating a code preserves this condition. We can discard redundant check rows: the kernel is unchanged and deleting rows only removes edges or changes a two-entry column to a one-entry column. It cannot create an edge or cycle. Accordingly assume \(H\) has full row rank \(m\). There are no zero columns (otherwise a single signed coefficient has zero syndrome).

Root each support component. Every node has local unit columns, and every edge has all columns with its two-row support. In a rooted subtree rooted at \(v\), exclude the columns on the edge to its parent, if any. A residual is the value at \(v\) of a signed combination of its columns with coefficients \(0,\pm1\) that vanishes at every other check in the subtree. Let \(S_v\subseteq\mathbb F_7\) be the set of attainable residuals. It is symmetric and contains zero, and zero is attained only by the zero combination. Let \(a(S)=(|S|-1)/2\), the number of nonzero sign-pairs, an integer from 0 to 3.

For a child with residual set \(S\) and \(k\) edge columns to its parent, let \(T\) be the parent residual set after adding those edge columns and enforcing zero at the child. In particular \(T\) includes the parent-coordinate sums of signed edge combinations whose child-coordinate sum is in \(S\), since \(S=-S\). Again the only way to attain zero as a parent residual is using no nonzero coefficient. Write \(H(S)\) for the simple Cayley graph on \(\mathbb F_7\) with nonzero edge differences in \(S\). The \(2^k\) binary subset sums of the edge columns, viewed as a subset of the two-coordinate child/parent plane, form an independent set in
\[
H(S)\boxtimes\overline{H(T)}.
\]
Indeed, if two different sums have child difference in \(S\), their parent difference lies in \(T\). That parent difference cannot be zero: their nonzero signed edge difference could be canceled at the child by using a subtree combination, giving a forbidden zero syndrome. So the parent difference is a nonzero edge of \(H(T)\), and distinguishes the two sums in the complement.

By multiplicativity of the Lovász theta function, \(2^k\le\vartheta(H(S))\vartheta(\overline{H(T)})\). The four values for \(\vartheta(H(S))\) are \(7,t,7/t,1\), in increasing order of \(a(S)\), where \(t=7\cos(\pi/7)/(1+\cos(\pi/7))\). A one-sign-pair Cayley graph is a cycle; a two-sign-pair graph is its complement. Use \(49/16<t<7/2\), immediate from \(7/9<\cos(\pi/7)<1\), to get the integer upper table
\[
\begin{array}{c|rrrr}
 a(S)\backslash a(T)&0&1&2&3\\\hline
0&2&3&4&5\\
1&1&2&3&4\\
2&1&2&2&3\\
3&0&1&1&2
\end{array}.
\]
The table comprises upper bounds, not an assertion that every transition is achievable.

## 2. Sum residuals at a branching check

For each subtree with \(N\) columns and \(M\) rows, we prove \(2N-5M\le p(a(S_v))\), with
\[
p(0)=-5,\quad p(1)=-3,\quad p(2)=-2,\quad p(3)=0.
\]
At a node, a child subtree plus its edge contributes \(2N_{\rm child}-5M_{\rm child}+2k\), at most the following values by the table, indexed by \(a(T)\):
\[
q=(0,2,3,5).
\]
The node contributes \(-5\) for its row and \(2\ell\) for its \(\ell\) unit columns. At most two unit columns are possible by injectivity of their binary subset sums in \(\mathbb F_7\). Their residual set is \(\{0\}\) for \(\ell=0\), one sign-pair with zero for \(\ell=1\), and all \(\mathbb F_7\) for \(\ell=2\) because four distinct subset sums have difference set all of \(\mathbb F_7\).

Add the child messages and the unit message by Minkowski sum. Nonzero parts of two distinct messages cannot overlap (symmetry would allow a forbidden cancellation). Any two disjoint nonzero messages sum to all residues: they already contain sign-pairs of two different classes, and up to scaling and sign the representatives are either \(1,2\) or \(1,3\). In both cases their sumset produces the missing sign-pair as well. Three nonzero messages are impossible because the first two can cancel any nonzero residue from the third. Zero messages cost at most zero and do not change the residual set. For the unit group, \(2\ell\) is also bounded by \(q\) at its corresponding state. With no nonzero messages the bound is \(-5\). With one, the bound is \(-5+q(a)=p(a)\) for \(a=1,2,3\). With two, the sum of their \(q\) values is at most 5 because their nonzero sign-pair counts sum to at most three; the resulting state is 3. This verifies the induction for any branching, including a leaf. At each component root \(p\le0\), giving \(2n-5m\le0\) and \(\dim L=n-m\le\lfloor3n/5\rfloor\).

## 3. Equality and robustness

A length-five rank-two parity-check example is given by columns
\[
(1,0),(0,1),(2,1),(4,1),(1,3).
\]
Its 32 binary subset sums are all distinct. An elementary check: with fifth coefficient 0, the fibres at second coordinates \(0,1,2,3\) have first-coordinate sets \(\{0,1\},\ \mathbb F_7\setminus\{6\},\ \mathbb F_7\setminus\{1\},\ \{6,0\}\), respectively, and other fibres are empty. Including the fifth column translates this set by \((1,3)\); the two occupied supports meet only at second coordinate 3, where the translated first residues are \(\{1,2\}\) and are disjoint from \(\{6,0\}\). The smaller blocks \([1\ 2]\) and \([1]\) have lengths 2 and 1 and dimensions 1 and 0. Take direct sums of five-column blocks and use lengths \(1,2,2+1,2+2\) for remainders \(1,2,3,4\). This gives the claimed dimension at every length. The classical 343-word lower bound is due to Baumert, McEliece, Rodemich, Rumsey, Stanley and Taylor (1971); no priority for that lower-bound size is claimed here.

If deletion of \(D\) columns makes the graph a forest, the surviving matrix retains injectivity of binary subset sums and has at most \(m\) rows. Thus \(2(n-D)\le5m\), proving the dimension bound stated above. A support graph whose cyclomatic number is \(o(n)\) suffices for the asymptotic statement, since each edge supports at most five columns by distinctness of its binary sums in \(\mathbb F_7^2\).

## 4. An explicit bound for all pseudoforests

Suppose the support graph has at most one cycle per connected component. After deleting redundant check rows it still has this property. On a component's unique cycle of \(\ell\) rows, consider only the columns carried by its cycle edges. If this submatrix has \(N\) columns, it still has zero-error kernel and at most \(\ell\) check rows; the global theta bound gives \(7^{N-\ell}\le t^N\). Since \(t<7^{2/3}\), we have \(N<3\ell\). Hence some cycle edge has at most two columns. Delete those columns to make the component a tree and apply the forest bound. For each unicyclic component with \(m\) rows this proves \(n\le5m/2+2\); tree components need no deletion.

For \(m\ge20\) this implies \(n\le13m/5\) directly. For \(1\le m\le19\), the global theta bound and integrality give the same conclusion: \(t<1659/500\) follows by bounding \(\cos(\pi/7)\) by \(1-x^2/2+x^4/24\) at \(x=157/350<\pi/7\), and the exact integer comparison \(1659^{248}<500^{248}7^{153}\) gives \(n<(248/95)m=(13/5+1/95)m\). Rounded-down multiples of \(13/5\) have their next integer at least \(1/5\) away. Thus \(n\le13m/5\) in each component, and adding components bounds the pseudoforest capacity by \(7^{8/13}=3.3117712551\ldots<t\). The strict comparison follows, for example, from \(t>663/200\) and \(7^8<(663/200)^{13}\), using the alternating Taylor lower bound at \(22/49>\pi/7\), verified in the checker; the pseudoforest upper bound is not asserted sharp.

For a broader exact algorithmic method and the strict theta gap at every fixed treewidth, see [bounded-width parity capacity](BoundedWidthParityCapacity.md).

## Scope and references

- L. Lovász, [On the Shannon capacity of a graph](https://doi.org/10.1109/TIT.1979.1055985), IEEE TIT 25 (1979), for theta, multiplicativity, and the cycle evaluation.
- V. Guruswami and A. Riazanov, [Linear Shannon Capacity of Cayley Graphs](https://arxiv.org/abs/2009.05685), Theorem 1, gives \(\Theta_{\rm lin}(C_7)\le7^{2/3}\), weaker than the general theta bound; the work asks for better linear bounds for prime-cycle graphs. The present theorem does not settle the unrestricted linear problem.
- Baumert et al., \emph{A combinatorial packing problem}, Computers in Algebra and Number Theory, AMS (1971), pp. 97–108, credited for the 343-word size by [Polak–Schrijver](https://arxiv.org/abs/1808.07438).
- [Tandon 2026](https://arxiv.org/abs/2608.30273) certifies \(3.2588326203\ldots\) unrestricted, and the [Tao tracker with primary certificate link](https://teorth.github.io/optimizationproblems/constants/9a.html) lists Tang's self-archived \(3.2588387054\ldots\) with an independent verification caveat. These are both above the forest-supported capacity. [Borovikov, 2026](https://doi.org/10.5281/zenodo.24484885) concerns \(2^d+1\) cycles, not \(C_7\).
- Bounded searches for forest-supported parity checks in this linear-capacity setting found no equivalent statement. Ordinary Shannon capacity of \(C_7\) is still open. No publication or priority claim is implied.

The optional [small checker](verify-c7-forest-parity.js) confirms the local transitions for all independent two-entry column sets, the branching inequalities on all eight residue masks, and the lower-bound blocks. The proof above does not rely on its enumeration.
