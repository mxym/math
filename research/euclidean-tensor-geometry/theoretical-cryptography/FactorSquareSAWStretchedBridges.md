# A square-lattice connective-constant lower bound by stretching bridges

Research note, 28 November 2026. Let \(\mu=\lim c_n^{1/n}\) be the connective constant of nearest-neighbor self-avoiding walks on the square lattice, counted from the origin. Then
\[
                     \mu>2.62738682602 .
\]
This is an increase from the [Numaro certificate](https://zenodo.org/records/21546041) bound \(2^{128}/129513673858566230428673965530967449326=2.627385640\ldots\). The same published finite enumeration is used, not rerun here. The additional weight comes from an explicit, reversible construction of wider irreducible bridges, without any transfer-matrix calculation at a larger span. This does not determine \(\mu\) or improve the upper bound of [Tomar](https://hexagonmath.org/pdf/2611.00474v1). It is an improvement over the cited Numaro input, not a claim to the strongest current lower bound: [Pinho's later unrefereed candidate](https://github.com/rpinho/math-certificates/blob/aed5011f71082ab1373bdd8692801dd6cb0ec608/c38/bridges-span18/PROOF.md) states \(\mu\ge8388608/3192535=2.62756962727\ldots\), not independently replayed in this note.

## 1. Crossing counts and a reversible width extension

A bridge \(v_0,\dots,v_n\) has \(v_0=(0,0)\); its horizontal coordinates satisfy \(0<x_j\le x_n=w\) for \(1\le j\le n\). It is irreducible if it is not a concatenation of two positive-length bridges, with the second translated to start at the endpoint of the first. For \(0\le j<w\) let \(h_j\) count edges crossing the vertical gap between columns \(j\) and \(j+1\). Each \(h_j\) is odd: the walk starts to the left of each gap and ends to its right. Also \(h_0=1\), since no later vertex is in column zero.

A bridge of span \(w\ge2\) is irreducible exactly when every internal gap \(1\le j<w\) has \(h_j\ge3\). If an internal gap is crossed only once, cut just before that crossing: the prefix ends on that gap's left column \(j\) and never exceeds it, and the ensuing translated suffix lies strictly to its right after its first vertex. Both parts are nontrivial bridges. Conversely, a decomposition at a vertex with horizontal coordinate \(j\) has a prefix that never exceeds \(j\) and a suffix that stays strictly above \(j\) after its starting vertex, so this gap is crossed exactly once.

For an irreducible bridge of length \(n\) and span \(w\), put \(h=\min_{1\le j<w}h_j\), and choose the leftmost gap attaining this minimum. Horizontal edges already number at least \(1+(w-1)h\). Between consecutive crossings of the selected gap there is at least one vertical step. Otherwise the two crossings, in opposite directions, would use the same row and repeat a vertex. The intervals between consecutive crossings are disjoint for this count, so there are at least \(h-1\) vertical steps. Hence
\[
                         h\le n/w .
\]
In particular \(h\le H(n,w)\), the largest odd integer no greater than \(\lfloor n/w\rfloor\).

Fix \(a\ge1\). Insert \(a\) columns into the selected gap, shifting all old columns to its right by \(a\) units and extending every crossing edge horizontally through the new columns. All crossing edges of the original gap are at distinct heights, since the walk is self-avoiding. Their interior subdivisions lie in otherwise empty columns and cannot meet one another. Thus the result is self-avoiding, starts at the same origin, and is a bridge of span \(w+a\) and length \(n+a h\). Its internal crossing-count sequence replaces the chosen entry \(h\) by \(a+1\) consecutive copies of \(h\), preserving irreducibility. The leftmost minimum of the new sequence is still the chosen gap. Locate that gap and contract the \(a\) inserted columns just to its right to recover the original walk. This is an injection for each \(a\); across different \(a\) the images have disjoint spans. No ending-height or vertical-order assumption is needed.

## 2. A renewal inequality and exact check

Let \(b_{n,w}\) and \(a_{n,w}\) count bridges and irreducible bridges of length \(n\) and span \(w\), respectively. The bridge renewal recursion and Kesten identity (see [Jensen, equations (3)–(4)](https://arxiv.org/abs/cond-mat/0409381)) give the irreducible coefficients from the bridge counts:
\[
 B_w(z)=A_w(z)+\sum_{i=1}^{w-1} A_i(z)B_{w-i}(z),
 \qquad
 \sum_{w\ge1} A_w(1/\mu)=1,
\]
where \(B_w(z)=\sum_n b_{n,w}z^n\) and \(A_w(z)=\sum_n a_{n,w}z^n\). The recursion follows by splitting at the first renewal vertex, and the smallest positive span is one. It applies coefficientwise even with a fixed finite length cutoff \(N\).

Take \(W=17,N=260\). Use all irreducible bridges up to these cutoffs, and add the images of span-\(W\) bridges by the width extension with \(a=1,2,3,4\). Their spans \(18,19,20,21\) are outside the original table and disjoint from one another. For \(0<z<1\), \(z^{n+a h}\ge z^{n+aH(n,W)}\), so
\[
 \begin{aligned}
 \sum_{w\ge1} A_w(z)\ \ge\ \Phi(z)
   =&\ \sum_{n=1}^{260}\sum_{w=1}^{17}a_{n,w} z^n\\
    &+\sum_{n:a_{n,17}>0}^{260} a_{n,17}
                         \sum_{a=1}^4 z^{\,n+aH(n,17)} .
 \end{aligned}
 \tag{1}
\]
This is an inequality of **values**, not a coefficientwise bound for the artificially lengthened exponents in \(\Phi\). There is no double count even when two source lengths differ because the contraction recovers the entire source walk.

Use \(p=262738682602\), \(q=10^{11}\). If \(\Phi(z)=\sum c_n z^n\) and \(D=320\), the exact calculation gives
\[
 \left\lfloor 10^{30}
  \frac{\displaystyle\sum_{n=0}^D c_n q^n p^{D-n}-p^D}{p^D}
 \right\rfloor
 =4754550554063873066>0.
\]
Thus \(\Phi(q/p)>1\). By (1), monotonicity of the irreducible series and its value 1 at \(1/\mu\), \(q/p>1/\mu\), proving the claimed strict bound.

The [standalone verifier](verify_factor_saw_stretched_bridges.py) reads the \(206604\)-byte file `bridge_table_record_L17.json` from [Numaro's archived dataset](https://zenodo.org/records/21546041). Its raw MD5, published by Zenodo and reproduced in this calculation, is `17a65c9ac2990e13785b79639abc6861`. It computes the irreducible coefficients and checks the inequalities with integers, without re-enumerating the upstream table. It also verifies that omitting the second line of (1) fails at the new rational threshold. In the optional small geometric replay (`--small-test`), all 1,042 irreducible source walks of spans two through four and length at most twelve are checked against the direct renewal-cut definition and each is stretched, contracted, and checked for collisions at both test insertion sizes. The general proof above is independent of this small test.
