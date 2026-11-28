# A forest composition law for determinantal convexity and the exact four-gate boundary

**Scope.** The Marcus–de Oliveira conjecture says that for arbitrary complex diagonal matrices \(A=\operatorname{diag}(a_i)\), \(B=\operatorname{diag}(b_i)\), and any unitary \(U\), \(\det(A+UBU^*)\) is in the convex hull of the permutation products \(\prod_i(a_i+b_{\sigma(i)})\). Here we prove it for an arbitrary-dimensional class of relative eigenbases \(U\), with one convex representation valid simultaneously for all spectra. We then classify exactly the ordered four-Givens architectures for which this stronger, simultaneous **minor law** holds for every choice of the four gates. Failure of the law is not a counterexample to Marcus–de Oliveira.

The stronger minor-law assertion for unrestricted unitary matrices has long been known to be false: see [Drury's 1992 counterexample](https://doi.org/10.1016/0024-3795(92)90296-M) and [his 1996 discussion](https://doi.org/10.1016/S0024-3795(94)00361-0). The point here is the forest closure rule and its exact four-gate boundary, not the first counterexample to the stronger assertion. [Kovačec, DMUC 26-11, Proposition 2](https://www.mat.uc.pt/preprints/ps/p2611.pdf) describes the original determinant along a single real Givens rotation. The theorem below uses arbitrary order, complex local unitaries, arbitrary numbers of coordinate blocks, and all exterior powers at once. We make no claim about the general four-dimensional conjecture.

## 1. The common minor law

For a unitary \(U\) on \(n\) labelled coordinates, write
\[
 K_k(U)(I,J)=|\det U[I,J]|^2,\qquad |I|=|J|=k .
\]
Here omitted indices are sorted, and the empty minor is 1. Say \(U\) has a **common minor law** if a single probability law \(\mu\) on permutations of the labels satisfies
\[
 K_k(U)(I,J)=\Pr_{\pi\sim\mu}[\pi(J)=I]
\tag{1}
\]
for all \(k,I,J\). For \(k=1\) this is ordinary Birkhoff–von Neumann. Every unitary of dimension at most three has such a law: since a unitary inverse is its adjoint and has determinant of modulus one, the modulus of a minor equals that of its complementary minor. Thus for \(n\le3\) the \(k=1\) decomposition gives all the remaining nontrivial levels via complementation. A law localized to a subset can be extended by fixing all other labels. Multiplication on either side by a monomial unitary only relabels (1), and inversion just transposes every matrix in (1).

For all diagonal spectra, the square-minor expansion is
\[
 \det(A+UBU^*)=
 \sum_{k=0}^n\ \sum_{\substack{|I|=|J|=k}}
 |\det U[I,J]|^2 \prod_{i\notin I}a_i \prod_{j\in J}b_j.
\tag{2}
\]
Indeed, first expand against the diagonal part \(A\), then expand each principal minor of \(UBU^*\) by Cauchy–Binet. Substituting (1) gives the expectation of \(\prod_i(a_i+b_{\pi^{-1}(i)})\).

## 2. Forest composition theorem

Let \(U=U_\ell\cdots U_1\), where \(U_t\) is the identity outside its coordinate block \(B_t\). Form the incidence graph with one node for each coordinate and one node for each gate occurrence, and an edge \(i\!-\!t\) exactly when \(i\in B_t\). If the graph is a forest and each local \(U_t\) has a common minor law on \(B_t\), then \(U\) has a common minor law: simply sample those local permutations independently and compose chronologically. In particular, every gate may be an arbitrary unitary on any two or three of the coordinates. All spectra in (2) are allowed. For two-coordinate gates with no repeated edge, the hypothesis is precisely that the graph of participating coordinate pairs is a forest.

**Proof.** In the matrix product for the \(k\)-th exterior power, a potentially nonzero path \(J_0,\ldots,J_\ell\) preserves membership outside \(B_t\) at step \(t\). Let the signed change at its incidence edge \(i\!-\!t\) be
\[
 f_{it}=\boldsymbol 1_{i\in J_t}-\boldsymbol 1_{i\in J_{t-1}}.
\]
The edges incident at gate \(t\) sum to zero, since all sets have size \(k\). Those incident at coordinate \(i\) sum to \(\boldsymbol 1_{i\in J_\ell}-\boldsymbol 1_{i\in J_0}\). For two paths with the same endpoints, the difference of their edge changes has sum zero at every graph vertex. A leaf has only one incident edge and forces that difference to be zero there; deleting leaves until none remain proves equality everywhere. Given \(J_0\) and all changes, the full sequence of sets is determined. Consequently the product sum for each exterior-power entry has at most one nonzero path. Its absolute square therefore equals the sum of the squared path magnitudes, i.e. the corresponding entry of \(K_k(U_\ell)\cdots K_k(U_1)\). The product law on local permutations has exactly those transitions by (1). This also covers the case of no nonzero path. \(\square\)

## 3. All four-gate words on four coordinates

A word specifies the chronological order of four pair supports; the same pair may be used more than once. A gate on a pair can be any unitary on it. Call a word **universal** if every choice of its local gates has the common minor law. On four labelled coordinates the \(6^4=1296\) words fall into 31 classes under common relabelling, reversal, and commuting consecutive disjoint pairs. Exactly 24 classes (1080 words) are universal and 7 (216 words) are not. The only nonuniversal classes have the following canonical representatives, with \(\mu\)-independent counterexamples in real rational \(SO(4)\).

For the table, a gate of type A, B, C, or D uses respectively \((c,s)=(3,4)/5,(4,3)/5,(5,12)/13,(12,5)/13\). Its real block is \(\begin{pmatrix}c&s\\-s&c\end{pmatrix}\) in increasing coordinate order. Write \(ab:cd\) for the linear coordinate \(K_2(U)(\{a,b\},\{c,d\})\). The displayed linear form has possible values \(0,1,2\) on permutation matrices; its value at the indicated \(U\), multiplied by the fourth power of the product of the four gate denominators, is the final column.

| Word | Class size | Gates | Linear form | Scaled value |
|---|---:|---|---|---:|
| \(12,13,14,12\) | 24 | AAAA | \(12:23-13:12+14:13+14:14+14:23\) | -5537109375 |
| \(12,13,14,24\) | 48 | AAAA | \(-12:34+13:14+14:13+14:14+14:23\) | -4130859375 |
| \(12,13,24,12\) | 24 | AAAA | \(12:12+12:14+12:23+13:14-14:24\) | -5537109375 |
| \(12,13,24,14\) | 48 | AAAB | \(12:23-13:13+14:12+14:14+14:23\) | -4130859375 |
| \(12,13,24,34\) | 24 | AAAA | \(-12:12+13:13+13:14+13:24+14:24\) | -2187500000 |
| \(12,13,34,24\) | 24 | AAAB | \(-12:12+13:14+14:14+14:23+14:24\) | -2187500000 |
| \(12,34,13,24\) | 24 | AACD | \(-12:23+13:12+13:13+13:34+14:12\) | -3076555218750 |

**Finite proof.** Enumerate the \(6^4\) words in lexicographic order, and close each new word under the three stated operations, obtaining its class. The properties of relabelling and adjoint observed after (1), and commutativity on disjoint supports, show that these operations preserve universality. For each word in a class try the eight ways of placing cuts in its three internal gaps. For every consecutive block between cuts, take the union of the coordinates it uses. If all block sizes are at most three and that block family has forest incidence graph, the previous theorem proves universality for the entire class: each consecutive subproduct is a unitary on at most three coordinates. Exactly the seven rows shown remain. The table evaluates the linear forms, first on each of the 24 permutation matrices and then on rational gate products using squared integer \(2\times2\) minors. A negative value is inconsistent with a probability law (1). The accompanying verifier implements both finite loops exactly, and does not use numerical feasibility or an optimization library.

At most three two-coordinate gates, in any dimension, always have the common law: each support component has at most three coordinates, or else it has exactly four coordinates and is a tree with three distinct edges. The first case is the local result, the second is the forest theorem, and distinct components act independently. Thus four is the exact minimum number of pair gates for a failure, even if only real gates are allowed. The four-gate classification extends directly to larger dimension: with at most four edges, a connected support with five vertices must be a tree, and a component with at most three vertices has the local law regardless of repetitions. Therefore an obstruction must use all four gates inside a four-coordinate component, exactly as classified above. Nonexistence on a component implies nonexistence after adjoining spectators: each spectator \(i\) has \(K_1(U)(\{i\},\{i\})=1\), which forces \(\pi(i)=i\) almost surely.

**An interval of counterexamples with one common angle.** In chronological order \(12,23,34,14\), take the same positive \(c,s\) in all four real gates, with \(c^2+s^2=1\). The five-term functional
\[
 L=12:13+12:14+12:24-13:34+14:13
\]
is again nonnegative on all permutations. A direct product of the four rotation blocks gives, with \(x=c^2\),
\[
 L(K_2(U))=(1-x)(2x-1)(3x-1).
\]
For example the product matrix before reducing \(c^2+s^2=1\) is
\[
 U=\begin{pmatrix}
 c^2-s^4&c(s^3+s)&-cs^2&cs\\
 -cs&c^2&s&0\\
 cs^2&-c^2s&c^2&s\\
 -c(s+s^3)&-s^4&-c^2s&c^2
 \end{pmatrix},
\]
where in the fourth row the second entry is equivalently \(c^2s^2-s^2=-s^4\). In the order of the five terms in \(L\), those minors simplify to \(s(1-2s^2),s^2(1-s^2),-c^3s,-cs,-c^2s\). Squaring with the displayed signs and putting \(x=c^2\) yields the factored expression. Hence the law fails for every \(1/3<x<1/2\), not merely for one isolated gate product. None of these failures, nor any row of the table, asserts that the determinant in (2) escapes its conjectured convex hull.

**Reproduction.** Run `python3 verify_marcus_forested_gates.py`. It checks the complete ordered-word classification, the seven rational separating certificates, and compares a nontrivial higher-dimensional circuit's common law to its squared minors in three arbitrary time orders. The forest theorem itself is proved above, not inferred from these sample runs.
