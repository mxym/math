# A lower bound of 13 in the B-variant of 2-adic Littlewood

Research note, 27 November 2026. For an irrational \(\alpha=[a_0;a_1,a_2,\ldots]\), write \(B(\alpha)=\limsup_{i\to\infty}a_i\).

**Theorem.** For every irrational real \(\alpha\),
\[
                        \sup_{k\ge0} B(2^k\alpha)\ge13.
\]
If \(\alpha\) is not a quadratic irrational, then already \(\max_{0\le k\le41}B(2^k\alpha)\ge13\).

This improves the lower bound of \(12\) in [Giraudin's November 2026 preprint](https://hexagonmath.org/pdf/2611.00009v1) for [Vitorino–Vukusic, Problem 5](https://doi.org/10.1112/mtk.70073). The finite part is a new exact calculation at digit cap \(12\). To make it feasible, we generate only counters following an emitted run switch, retain only edges internal to a strongly connected component, and identify the two orientations of the letter alphabet.

This concerns the limsup of partial quotients, not the supremum over all digits. It does not prove the full 2-adic Littlewood conjecture, give uniform escape at a finite doubling level for quadratic inputs, or modify the stronger known numerical bound on \(M(\alpha)=\sup_i a_i\).

## 1. Synchronous states and their necessary fibres

We use the Raney framework as in [David Niedbala Giraudin, Hexagon 2611.00009v1](https://hexagonmath.org/pdf/2611.00009v1), which proves the earlier \(B\)-bound \(12\). We give the new state-space reduction and its completeness proof.

Use column-vector Möbius matrices
\[
 L=\begin{pmatrix}1&1\\0&1\end{pmatrix},\quad
 R=\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
 D_j=\begin{pmatrix}2^j&0\\0&1\end{pmatrix}.
\]
A positive irrational has the letter expansion \(L^{a_0}R^{a_1}L^{a_2}\cdots\). We can assume \(0<\alpha<1\) by subtracting an integer; all \(B(2^j\alpha)\) are invariant under this change. Its input is therefore an alternating stream of nonempty runs starting with \(R\).

Any nonsingular nonnegative integral \(2\times2\) matrix \(A\) of positive determinant has a factorization \(A=W M\), with \(W\) a word in \(L,R\) and \(M\) *reduced*, meaning the two rows are incomparable coordinate by coordinate. Indeed if the first row dominates the second, the only possible first letter is \(L\); subtract the second row from it. In the other domination case the only possible first letter is \(R\). Repetition terminates with a reduced matrix, and one may subtract the maximum possible multiple in each run. This also proves uniqueness and \(\operatorname{red}(W'A)=\operatorname{red}(A)\) for an additional nonnegative word \(W'\). If \(M=\begin{pmatrix}a&b\\c&d\end{pmatrix}\) is reduced with positive determinant \(D\), then \(a>c\) and \(d>b\). The identities \(D=a(d-b)+b(a-c)=d(a-c)+c(d-b)\) show that \(a,d\le D\). Thus for each fixed determinant the reduced state space is finite.

At the end of an input prefix \(U\), write \(D_jU=W_j M_j\). The letter word \(W_j\) is an output prefix of \(2^j\alpha\): the remaining input tail is positive, and \(M_j\) maps it to a positive tail. On reading another input run \(X^a\), reduce \(M_jX^a=W'M_j'\), append \(W'\) to the output, and take the new state \(M_j'\). Along an irrational input the emitted word is infinite. Otherwise eventually no output is emitted, and successive right multiplications by both positive-length input letters force the entries to grow without bound, contradicting the reduced state bound. An irrational's letter word has infinitely many switches, so this also holds for its emitted word.

Let \(\mathcal A_2,\mathcal A_4\) be the finite sets reached by starting respectively at \(D_1,D_2\) and reducing after a single input \(L\) or \(R\). The code obtains these closures directly (of sizes 4 and 12). Each true extension of adjacent levels satisfies
\[
 M_j\in\{\operatorname{red}(N M_{j-1}):N\in\mathcal A_2\},
\]
and for \(j\ge2\) also
\[
 M_j\in\{\operatorname{red}(N M_{j-2}):N\in\mathcal A_4\}.
\]
For the first inclusion, use \(D_jU=D_1W_{j-1}M_{j-1}\) and factor \(D_1W_{j-1}\) first. For the second use \(D_2W_{j-2}\). Moreover \(M_j\) is primitive as an integer matrix: \(D_jU\) has gcd of entries 1, invariant under left and right integral unimodular operations. The implementation can therefore discard all-even matrices. It does not require a sufficient criterion for a compatible fibre; retaining additional matrices is safe.

## 2. New graph reduction: suffix seeding and eventual components

Fix a digit cap \(C\). Start with a graph of the input-run parity, permitting every label \(1,\ldots,C\) and alternating the parity. This captures the eventual input of any \(\alpha\) with \(B(\alpha)\le C\). Suppose the graph at level \(j-1\) captures an eventual trajectory whenever \(B(2^k\alpha)\le C\) for \(0\le k\le j-1\). First attach each candidate \(M_j\) from the displayed necessary fibres to each old vertex. Lift each old edge with the same label using the state transition for \(M_j\) and record its emitted block. Discard an edge emitting a run longer than \(C\). This gives a base graph; we still need to impose the length bound across output-block boundaries.

The added counter is a pair \((i,s)\), last output letter \(i\) and \(1\le s\le C\) its current run length. When an edge emits output, reject a counter transition if the previous run and the first emitted run join to length exceeding \(C\). Otherwise update it by this joining rule for a one-run output, or by the last emitted run for a multi-run output. An empty output leaves it unchanged.

**Suffix seeding.** Do not enumerate all \(2C\) counters at every base vertex. At the target of any base edge with nonempty output, seed the counter equal to the last run *inside that output block*. Follow forward transitions from all such seeds. To see this still captures every necessary infinite trajectory, take an edge sufficiently late on the actual trajectory that contains an output letter switch, including a switch at the very start of its emitted block. Such edges occur infinitely often. At its target the actual last-run length is exactly the last run inside that block, so it is one of the seeds. The entire later trajectory is then in the forward closure. Seeds that would not genuinely occur from a valid past only enlarge the graph.

**Eventual components.** A finite directed graph's strongly connected components can be indexed so that an edge from one component to another strictly decreases the index. The implementation checks this inequality on every edge of its computed partition. An infinite path can decrease the index only finitely often. Hence we can discard all edges crossing a component boundary and then vertices with no internal outgoing edge. Every compatible irrational still eventually lies in the retained graph. This is stronger than trimming vertices with zero in-degree or out-degree: it removes links between cycles too. We apply it at every level, not only at the last level; the induction concerns eventual trajectories, so a new finite head can be discarded each time.

**Orientation quotient.** Conjugation by \(J=\begin{pmatrix}0&1\\1&0\end{pmatrix}\) exchanges \(L,R\) and commutes with reduction (with the emitted letters exchanged). The two small transducer closures are invariant under this conjugation, which is checked directly. We normalize the next input letter to \(L\) at each vertex by conjugating all its matrices and exchanging the saved output letter if the actual next letter is \(R\). After reading each run the next input letter switches, so the successor matrices and its last output letter are conjugated again. Run lengths, admissible counters, and digit labels are unchanged. This gives the same eventual-path inclusion even though the stored parity no longer has two separate copies.

If the retained graph has all out-degrees one, every infinite label word admitted by it is eventually periodic (if the graph is empty, there is no such word). Each level is finite; the input letters alternate, and the labels remain exactly the partial-quotient lengths. Thus for such a verified closing level \(j\), an irrational with \(B(2^k\alpha)\le C\) for \(0\le k\le j\) must be quadratic by the continued fraction periodicity theorem.

## 3. Quadratic inputs

For completeness a quadratic irrational cannot satisfy \(B(2^k\alpha)\le C\) for all \(k\). A quadratic irrational is the attracting fixed point of an integer hyperbolic Möbius matrix \(T\) of determinant \(\pm1\), obtained by conjugating its period matrix by its initial convergent matrix. For any fixed \(k\), some positive power \(T^r\) is the identity modulo \(2^k\). Apply \(T^{jr}\) to the column \((1,0)^\top\), writing \((u_j,v_j)^\top\) for the result. Diagonalizing \(T\), its dominant eigenline has slope \(u/v=\alpha\) and the eigenvalue moduli are \(\lambda,\lambda^{-1}\) with \(\lambda>1\). The vector \((1,0)^\top\) does not lie on either quadratic eigenline. Consequently \(|v_j|\asymp\lambda^{jr}\) and \(|v_j\alpha-u_j|=O_\alpha(\lambda^{-jr})\); in particular the product stays bounded by a fixed constant depending only on \(T\), not on \(k\) or \(r\). Also \(v_j\equiv0\bmod2^k\). With \(q_j=|v_j|/2^k\) this gives
\[
 \liminf_{q\to\infty}q\|q\,2^k\alpha\|\ll_\alpha 2^{-k}.
\]
The usual continued fraction bound \(\liminf_{q\to\infty}q\|q\beta\|\ge1/(B(\beta)+2)\) gives \(B(2^k\alpha)\to\infty\).

## 4. Finite computation

Run the [standalone verifier](verify_factor_littlewood_b13.js) with `node --expose-gc verify_factor_littlewood_b13.js`. It includes both the fibre construction and the graph recurrence, with no external data or dependencies. The selected rows at \(C=12\) are:

| Doubling level | Seed-reachable states | Retained states | Internal edges | Excess |
|---:|---:|---:|---:|---:|
| 1 | 36 | 34 | 364 | 330 |
| 11 | 63904 | 32587 | 110294 | 77707 |
| 20 | 1809737 | 764570 | 1175691 | 411121 |
| 24 | 3248245 | 905166 | 1067461 | 162295 |
| 30 | 80310 | 24266 | 24368 | 102 |
| 35 | 73914 | 23758 | 23779 | 21 |
| 40 | 72524 | 23797 | 23799 | 2 |
| 41 | 73349 | 23464 | 23464 | 0 |

Every retained vertex has at least one internal outgoing edge, so excess zero at level 41 completes the strict out-degree check. In a separate run without identifying the two letter orientations, counts of seed-reachable vertices, retained vertices and internal edges agreed at twice their quotient values, including the \(46928\) retained states and \(46928\) edges at level 41. As a baseline check, the quotient at \(C=11\) closes at level 31 with 12204 states (half of Giraudin's 24408 states), peaking at 770148 seed-reachable states. The table verifies a sufficient closing level, not its minimality among possible presentations or the exact set of genuinely realizable periodic orbits. No Lean verification is claimed.

The process below is integer-exact. All reduced matrices at level \(j\) have entries at most \(2^j\). Multiplying by one input run gives entries at most \((C+1)2^j\). The size guard keeps this strictly inside the exact integer range of JavaScript numbers; the row subtractions stay in that range. Taking the floor of a quotient of two such nonnegative integers is exact: if the quotient is not an integer, its distance below the next integer is at least the reciprocal of the denominator, larger than half a floating-point unit at its magnitude. In the two-level fibre filter, equal matrices have equal fingerprints, so collisions can only retain extra matrices, never exclude a true one. Vertex packing limits are checked. The sorted component numbering is verified when edges are retained, ensuring the eventual-path argument even independently of the component routine's maximality.
