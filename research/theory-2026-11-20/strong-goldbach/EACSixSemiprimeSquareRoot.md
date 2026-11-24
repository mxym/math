# Square-root count in the six-label all-semiprime class

This proof is independent of [the one-cube analysis](EACSixLoneCubePaper.md). Here every one of the six rows \(N-x\) is a product of exactly two primes, counted with multiplicity. The statement is solely about actual six-label exceptional autonomous components (EACs), not about missing prime-sum representations.

**Theorem.** Let \(p<q\) be the two least labels of an all-semiprime six-label EAC. Then \(pq\ll \sqrt N\). Hence at most \(X^{1/2+o(1)}\) centers \(N\le X\) carry such a component. More structurally, no sequence of such components can have both \(p\to\infty\) and \(q/p\to\infty\); this latter assertion does not use the earlier quarter-power minimum theorem.

We use just two earlier arithmetic inputs from strong-goldbach: the six-label corollary of [EACSemiprimeQuarter](EACSemiprimeQuarter.md) (\(p\ll N^{1/4}\) in this homogeneous class), and the supported-minor plus nonsingular counts ([EACSupportedMinorFive](EACSupportedMinorFive.md) and [EACNonsingularSquareRoot](EACNonsingularSquareRoot.md)). Strong connectivity ensures each input label appears as a factor of some row. The labels are distinct odd primes coprime to \(N\), so no self-factor and all labels \(\le(N-3)/3\). Since \(N-p\) uses factors \(\ge q\), \(q<\sqrt N\).

## 1. Suppose both the minimum and the first ratio diverge

Then \(p=o(\sqrt N)\). A factor label is called high if it occurs in a pair with \(p\). There is at least one, since \(p\) occurs as a factor and no pair \(p^2\) is possible when \(p=o(\sqrt N)\): every product is \(>2N/3\). Each high \(H\) satisfies \(H\sim N/p\), because \(M\le N/p\) for the greatest label \(M\) (every complementary product has another factor ≥\(p\)); \(M/N\to0\). A high can appear only paired with \(p\), since \(Hq>N\) eventually by \(q/p\to\infty\). Each such pair is one distinct row. All other labels besides \(p\) and the highs are called middles.

If there are \(h\) highs, the cofactor graph on the \(n=5-h\) middles has no isolates and exactly \(n+1\) distinct edges (loops allowed). The other \(h\) products give the star \(p\)-high. Hence \(2\le n\le4\), \(1\le h\le3\). Every component in the middle cofactor graph is nonbipartite: a connected bipartite component on four vertices has at most four edges, on three has at most two, and on two has only one; if a bipartite size-two component leaves two more vertices, those contribute at most their two loops and one edge, so the total is at most four, not five. Empty and singleton leftovers are even smaller. Each middle factor thus obeys
\[
  x=\sqrt N+O(M/\sqrt N)=\sqrt N+O(\sqrt N/p).
\]
Indeed set \(w_x=\log(x/\sqrt N)\); along each edge \(uv\) these coordinates sum to \(\log(1-r/N)=O(M/N)\) for the row input \(r\). Alternating along a bounded odd closed walk in each nonbipartite component gives \(w_x=O(M/N)\), hence the claimed size.

Let \(A\) be the row exponent matrix and choose \(c\ne0\) in its left kernel, supported on the middle cofactor rows. Such a vector exists because there are \(n+1\) rows on \(n\) columns; equivalently the high columns force all star-input coefficients to be zero. Along a contrary unbounded sequence there are only finitely many sorted exponent charts, so a single one and a fixed integer \(c\) can be selected. Every row sum is 2, giving \(\sum c_i=0\), and the exact logarithmic identity is
\[
  \sum_i c_i\log(1-x_i/N)=0.                                      \tag{1}
\]
Here and below the coordinate \(i\) of \(c\) is an **input row**, even though which variables its product uses is specified by the output factors. Since the highs are all asymptotic to \(N/p\), the others are \(o(N/p)\), and \(M/N\to0\), multiplication by \(p\) in (1) yields
\[
 \sum_{i:\ x_i\ {\rm high}} c_i=0.                              \tag{2}
\]

## 2. Three highs

Only two middles \(u<v\) remain, and their three products must be \(u^2,uv,v^2\). Their unique relation has coefficients \(1,-2,1\) (up to scaling). No proper nonempty subset of those three coefficients sums to zero. Thus by (2) the three input labels of these products are all highs or none is high. In the first case the remaining inputs \(p,u,v\) would all give star products, forcing a forbidden self-factor \(p\) in the \(p\)-row. In the second case all three inputs lie in \(\{p,u,v\}\) below \(\sqrt N\), since the square rows imply \(u,v<\sqrt N\). Their input differences are below \(\sqrt N\), but distinct products among \(u^2,uv,v^2\) differ by at least \(2u>\sqrt N\) for large \(N\). Both alternatives fail.

## 3. One or two highs force \(c_p=0\)

For one high, (2) already says its coordinate is zero. For two highs, either both coordinates vanish or they are nonzero and opposite. In the latter case each high is an input of a middle cofactor row. The two star rows are then fed by distinct middle inputs \(r,s\), since \(p\) cannot feed its own star. Their equations \(N-r=pH_1,\ N-s=pH_2\) give
\[
 |H_1-H_2|=|r-s|/p=O(\sqrt N/p^2)=o(\sqrt N).
\]
Their combined contribution to \(N\) times (1) is thus \(o(\sqrt N)\), by the mean value bound for \(N\log(1-x/N)\) on \(x\le M=o(N)\). This also holds if all high coefficients vanish. For the remaining terms of \(N\) times (1), the \(p\) term is \(o(\sqrt N)\), each middle contributes \(-c_i\sqrt N+o(\sqrt N)\) by the middle size estimate, and \(c\) is fixed. Consequently the sum of middle coefficients is zero, and since the total and high sums are zero, \(c_p=0\).

## 4. Evaluating the possible support sizes

A relation among pair exponent rows must use at least three rows, because all rows have the same sum and distinct rows cannot be proportional. If it uses exactly three, one row is a nontrivial convex combination of the other two (from the vanishing coefficient sum). A loop row cannot be such a combination, since all its mass sits on one coordinate. For a mixed pair row, both other rows must use only its two endpoints and be distinct from it. Thus they are the two loops. All three corresponding input rows are middles by §3, so their differences are \(O(\sqrt N/p)=o(\sqrt N)\), while the two loops and mixed product have successive gaps at least twice the lesser factor, asymptotic to \(2\sqrt N\), a contradiction. This already finishes the two-high case, which has only three middle input labels.

In the one-high case there are four middles, so the only remaining support size is four and each of its input rows is a different middle. The cofactor subgraph of these four rows is connected: each nonempty component would itself carry a relation supported on at least three rows. Moreover, no used vertex of this support is incident with exactly one edge occurrence (a sole incident nonloop would force that row coefficient zero). If this subgraph is bipartite, its four edges on at most four vertices with no leaves form \(C_4\). Then all four middle inputs are used in that \(C_4\); the high input cannot give its own star product \(pH\) by the no-self-factor condition, so it gives the fifth nonstar row, forcing \(p\) itself into the star row. This is again a self-factor contradiction.

If instead the four-row subgraph is nonbipartite, its own input labels are all middles \(\sim\sqrt N\), so the preceding alternating odd-walk argument applied only to these four rows gives **every factor in their support** equal to \(\sqrt N+O(1)\) (the edge logarithm is now \(O(1/\sqrt N)\)). Put \(T=\lfloor\sqrt N\rfloor\). Expanding their four products as \((T+i)(T+j)\), \(i,j=O(1)\), shows the factor sums all coincide exactly: the input differences are \(o(\sqrt N)\), offset product differences \(O(1)\), and the main differences are \(T\) times an integer. Among at most four distinct labels, a fixed sum admits at most two unordered pairs even allowing loops (each label has a unique possible partner, and there is at most one loop). Four distinct products are impossible. This excludes all supports and proves that no sequence has both divergences.

## 5. From structure to counting

If there were no uniform bound on \(\min(p,q/p)\) among these components, choose one with both quantities exceeding each growing integer, obtaining the forbidden sequence. Hence either \(p\ll1\) or \(q\ll p\), with absolute constants. In the first case \(pq\ll\sqrt N\) since \(q<\sqrt N\); in the second \(pq\ll p^2\ll\sqrt N\) by the earlier quarter-power minimum. This proves the pointwise claim.

For the count, \(A\) is singular, for example by its factor star (or [EACSemiprimeStar](EACSemiprimeStar.md)). Its Perron root is 2 by the equal row sums. If \(B=I-A\) had corank at least 2, its eigenvalue count for \(A\) would include \(0,1,1,2\). Trace zero forces the remaining two to sum to \(-4\); their modulus is at most 2, so both equal \(-2\). This contradicts the algebraic simplicity of peripheral eigenvalues for an irreducible nonnegative matrix. Thus \(\nu\le1\). When \(\nu=1\), the least two labels have product \(O(\sqrt X)\) and are a supported-minor set; when \(\nu=0\) use the nonsingular-\(B\) count. Both are \(X^{1/2+o(1)}\). No enumeration is needed for this result and it does not extend without new work to mixed row arities.
