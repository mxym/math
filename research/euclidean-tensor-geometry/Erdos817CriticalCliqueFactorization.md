# Exact subset-sum factorization of critical clique blocks

**Yongxian Zhang.** AI-assisted exposition and internal checks; no external peer review claimed.

Let \(k\ge3\) and \(s=k-1\). Suppose \(A\) is a finite set of distinct positive integers and its subset-sum set \(H(A)\) is \(k\)-term-progression-free. If \(B\subseteq A\) consists of all \(\binom{s}{2}\) pairwise distances of \(s\) distinct marks, then
\[
 |H(A)|=|H(B)|\,|H(A\setminus B)|=\mathcal F(K_s)\,|H(A\setminus B)|,
\]
where \(\mathcal F(K_s)\) is the number of forests on the \(s\) labelled vertices. The same exact factor applies for each of any collection of generator-disjoint critical clique blocks, even with different marks in each block and with arbitrary remaining generators. No carry-free or spacing assumption is needed.

**Prior work.** The [September 15 workbench, Theorems CI1 and CI4 and Section 5](https://github.com/KokunoYumeto/erdos-problem-817-workbench/blob/bb9c492ad2dbc520b3d619e013fa70d22ed8ac54/research/canonical_isolation/notes/canonical-isolation.md), already proves the product against an arbitrary finite remainder, plus stronger canonical isolation. The argument below is an alternate deduction from the workbench's earlier results, with the forest-count interpretation and independent checks; it is not a new claim of clique multiplication or collision rigidity.

## Multiplication from the prior root packet

Write \(S\) for all tournament-score vectors of \(K_s\). The subset sums \(H(B)\) are an affine image of \(S\) under a linear evaluation \(L\) with signed distinct mark coordinates. Every difference \(r\in S-S\) has total zero and satisfies the root-budget cut inequalities of workbench Theorem 5.2. For each nonzero such \(r\), the theorem constructs \(s+1\) scores whose first \(s\) form a vector progression with difference \(e_j-e_i\), and the last score exceeds the next term by \(r\). Moving just the last score by \(-r\) gives an actual \(s+1\)-term progression in \(S\cup(S-r)\). Its scalar image is nonconstant since the marks at \(i,j\) differ.

Set \(X=H(B)\), \(Y=H(A\setminus B)\). If two distinct decompositions of a point in \(X+Y\) existed, the corresponding \(y,y'\) would differ by \(d\in(X-X)\setminus\{0\}\). Choose \(r\in S-S\) evaluating to \(d\), reversing the roles of \(y,y'\) if needed. Then \(X\cup(X-d)\) contains a nonconstant progression by the preceding argument. Its translate by one of \(y,y'\) lies in \(H(A)\), a contradiction. Thus the addition map \(X\times Y\to H(A)\) is injective. The same argument for each remaining disjoint block gives the product.

Theorem 5.3 of the workbench gives \(|H(B)|=|S|\). The forest count follows because \(S\) is an integral translate of the graphical boundary-vector set; see [the forest identity](Erdos817InjectiveForestEntropy.md). For \(s=4,5,6\) the counts are \(38,291,2932\), respectively. The included [small-case verifier](erdos817-clique-projection.cpp) independently checks these counts and the translate certificate for these three sizes; the proof above covers every \(s\).

## Scope and a nonclique comparison

In a graph admitting such an AP-free marking, a \(K_s\) cannot have an outside path between two of its vertices whose internal vertices are outside the clique: that path is edge-disjoint from the \(s-1=k-2\) internal paths. Hence each critical clique is a whole graph block (a bridge when \(s=2\)); distinct such cliques have disjoint edges. If a fraction \(f\) of the generators lies in these clique blocks, then they alone force
\[
 \log |H(A)|\ \ge\ f|A|\frac{\log\mathcal F(K_s)}{\binom{s}{2}}
   =f|A|(2+o(1))\frac{\log k}{k}.
\]
This does not guarantee that an arbitrary \(A\) admits such a packing, and does not solve [Erdős problem 817](https://www.erdosproblems.com/817).

For \(k=4\), every simple cycle's distance block also factors, without requiring scalar injectivity on its boundary vectors. Orient the edges cyclically, let \(L\) be the signed edge evaluation, and note \(L(\mathbf1)=0\). The translated signed subset-sum set \(X=L(\{0,1\}^{E})\) contains both \(\alpha\) and \(-\alpha\) for every \(\alpha\in X\), by complementation. For a nonzero difference \(d=L(c)\) with \(c\in\{-1,0,1\}^{E}\), reverse \(d,c\) if necessary so that \(\alpha=L(\mathbf1_{\{c=1\}})\ne0\); one of these signs works because \(d=L(\mathbf1_{\{c=1\}})-L(\mathbf1_{\{c=-1\}})\). Then \(2\alpha-d\in X\), since \(2\mathbf1_{\{c=1\}}-c\) is binary. Thus \(X\cup(X+d)\) contains \(-\alpha,0,\alpha,2\alpha\), proving factorization by the same translate argument.

Local scalar injectivity can fail for a nonclique graph. A six-cycle with successive signed differences \(+1,+23,+4,+92,-5,-115\) has distinct marks and distinct positive distances. Its subset sums are the base-23 two-digit product of \(H(\{1,4,5\})=\{0,1,4,5,6,9,10\}\) with itself. The digit set has no nonconstant integer 4-AP (a direct seven-element check), and any modular 4-AP would have second differences bounded in absolute value by 20 and divisible by 23, hence would be integer. Reducing at the first changing digit now shows the two-digit set also has no 4-AP. The scalar set has \(49\) elements, fewer than the \(2^6-1=63\) forests of a six-cycle.
