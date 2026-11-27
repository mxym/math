# Anchored energies of tensor root lattices: exact amplitudes two and three, and an eventual coding reduction

## Statement

For \(k\ge1\) and integers \(q_i\ge3\), let
\[
L=\bigotimes_{i=1}^k A_{q_i-1},\qquad
A_{q-1}=\{z\in\mathbb Z^q:\textstyle\sum_x z_x=0\}.
\]
This is the Euclidean tensor product with the indicated standard embeddings. An element is an integer array \(f(x_1,\ldots,x_k)\), \(0\le x_i<q_i\), whose sum on every coordinate line is zero. Fix the focal cell \(o=(0,\ldots,0)\) and let \(m(a)=\min_{f(o)=a}\|f\|^2\). Write \(p=\#\{i:q_i=3\}\). A box is a signed elementary tensor of roots; a box **through \(o\)** means the normalized box with value \(+1\) at \(o\).

The exact results are
\[
\boxed{m(1)=2^k,\qquad m(2)=2\cdot 2^k+2,\qquad
m(3)=3\cdot 2^k+2^{\lfloor p/3\rfloor+1}(3+(p\bmod 3)).}
\tag{1}
\]
The minimizers at amplitude two are two boxes agreeing only at \(o\). More generally the entire part of the lattice with some cell of magnitude at least two and energy below \((9/4)2^k+2\) is explicitly counted below. At amplitude three, every minimizer is a positive sum of three boxes through \(o\), **except for 16 additional signed minimizers when \(k=p=4\)**. In that exception the fixed positive focal cell has 112 minimizers in total.

For every integer \(a\ge1\) there is also a rigidity threshold: any \(f(o)=a\) with \(\|f\|^2<(a+2^{-a})2^k\) is a positive sum of \(a\) boxes through \(o\). Consequently, for fixed \(a\) and sufficiently many axes, the exact norm correction reduces to a finite pairwise agreement problem on \(a\) words; this yields a sharp exponent for arbitrary mixed \(q_i\) and a particularly simple binary exponent.

No parameters from a cryptosystem or computational lattice problem are used. The result is a sectional lattice-energy statement, not a method for finding short vectors in arbitrary lattices.

## 1. Integer tensor realization and the marginal energy identity

Write \(e_x\) for a coordinate vector. The normalized boxes through \(o\) are
\[
P_b=\bigotimes_{i=1}^k(e_0-e_{b_i}),\qquad b_i\in\{1,\ldots,q_i-1\}.
\]
They form an integral basis. Indeed \(e_0-e_b\) form the corresponding root lattice basis; alternatively any integer line-zero array is determined by its values on the product of the nonzero local symbols, because the remaining entries are obtained by taking the negative of the other entries on one axis at a time. For \(f=\sum_b c_b P_b\), those nonzero-symbol entries are \((-1)^k c_b\). Thus the array model is exact and \(f(o)=\sum_b c_b\).

For a subset \(I\) of the axes, let \(c_I(z)=\sum_{b:b|_I=z}c_b\). The local Gram entry is \(2\) for equal symbols and \(1\) for unequal symbols, so the tensor Gram entry is \(2^{e(b,b')}\) where \(e\) counts agreements. Expanding each local Gram factor as \(1+\mathbf 1_{b_i=b_i'}\) yields
\[
\boxed{\|f\|^2=\sum_{I\subseteq[k]}\sum_z c_I(z)^2.}
\tag{2}
\]
For \(a\ge0\), each inner sum is at least \(a\), since the entries are integers of total \(a\); the empty marginal contributes \(a^2\). This gives \(m(a)\ge a2^k+a^2-a\). The slice energy at any negative anchor has the same bound with \(|a|\), by changing signs. For amplitude three there is a sharper bound:
\[
m(3)\ge3\cdot2^k+6+2p.
\tag{3}
\]
Indeed each of the \(p\) single-axis marginals with only two bins and sum \(3\) has sum of squares at least \(1^2+2^2=5\), rather than \(3\). More generally the minimum sum of squares for a fixed integer total over a fixed number of bins is attained by making the entries differ by at most one; this follows by moving one unit from a higher entry to a lower one whenever their difference is two or more. In particular, equality in the full-axis bin bound for \(a=3\) forces nonnegative coefficients, whether there are two bins or at least three.

The shortest nonzero energy is \(2^k\), by applying (2) at a nonzero cell, whose label can be renamed \(o\). If an array has norm strictly below \(3\cdot2^{k-1}\), it is a signed box: a coordinate direction with at least three nonzero slices already costs three times the shortest energy \(2^{k-1}\) of a slice. Otherwise there are exactly two nonzero slices in every direction, by the line-zero constraint. On the resulting two-symbol product the signs must alternate and all magnitudes are identical; a magnitude at least two costs \(4\cdot2^k\). For \(k=1\) the slice convention is \(\mathbb Z\) with shortest nonzero energy \(1\). For induction we also use the empty product as \(\mathbb Z\) with its single unit box.

## 2. Two-box rigidity and complete low-energy nonunit counts

We first prove the slightly stronger additive threshold
\[
f(o)=2,\quad \|f\|^2<(9/4)2^k+2
\ \Longrightarrow\ f=P_b+P_{b'} .
\tag{4}
\]
Slice along any axis, and put \(n=2^{k-1}\). The central slice has focal value \(2\) and energy at least \(2n+2\). Since the other focal values sum to \(-2\), their total absolute value is at least two; a positive off-center value raises it to at least four. Bounds from (2) then rule out any positive off-center focal value under \(4.5n+2\). A nonzero slice with zero focal value would add at least \(n\) to the minimum \(4n+2\) already spent on the nonzero focal slices, and is also excluded.

There are only two partitions of two into magnitudes of the off-center focal values. If it is one part \(2\), the line-zero property makes the two slices negatives of one another; factor the corresponding root and apply induction since the energy halves. For parts \(1+1\), each off-center slice has energy strictly below
\[
4.5n+2-(2n+2)-n=1.5n.
\]
Both are therefore negative normalized boxes in the remaining axes; lift them using their respective fixed root choices on the sliced axis. The line-zero condition fixes the central slice as minus their sum. The empty-product case is immediate. This proves (4).

Two boxes have energy \(2\cdot2^k+2^{t+1}\), where \(t\) is the number of axes on which their choices agree. Distinct alternative symbols on every axis are possible and attain \(m(2)\), confirming (1) and its classification. The larger-amplitude lower bound from (2) rules out any \(|f(x)|\ge3\) below (4)'s threshold, so every array with some magnitude at least two in this range has this form after orienting the two boxes to agree at a maximal cell. The **unanchored signed multiplicity** at energy \(2\cdot2^k+2^{t+1}<(9/4)2^k+2\), restricted to arrays with some magnitude at least two, is
\[
\sum_{\substack{C\subseteq[k]\\|C|=t}}
\prod_{i\in C}\binom{q_i}{2}\,
\prod_{i\notin C}q_i(q_i-1)(q_i-2).
\tag{5}
\]
On \(C\) pick the common two symbols. Outside \(C\) pick the intersection symbol and the two ordered distinct alternatives. The first choice includes their order only outside \(C\): the two support boxes can be swapped globally, a factor of two canceled by the two overall signs. The strict energy condition excludes \(t=k\). There is no extra multiple counting from the possible focal cells: for any focal cell of magnitude two, choose an axis with distinct alternatives. The two off-center slices there each identify exactly one support box, so the unordered pair of support boxes is uniquely recoverable. Their alternating signs agree on their whole common support once fixed at a single common cell, and only the overall sign remains. For all \(q_i=3\), (5) simplifies to \(\binom{k}{t}3^t6^{k-t}\); in particular the smallest such shell has \(6^k\) vectors. This count excludes all arrays with coefficients in \(\{0,\pm1\}\), including ones with the same norm.

## 3. Exact amplitude-three energy for every tensor size

Let
\[
E(p)=2^{\lfloor p/3\rfloor+1}(3+(p\bmod3)).
\]
The best possible energy of a *positive sum of three boxes* is \(3\cdot2^k+E(p)\). For the three pairs of boxes, denote their agreement counts by \(e_1,e_2,e_3\). On a two-alternative axis (one of the \(p\) ternary axes), at least one pair must agree. On every other axis choose the three alternatives distinct. The correction is \(2\sum_{\ell=1}^3 2^{e_\ell}\). Given a total number of agreements, transferring one agreement from a count higher by at least two to a lower count reduces this sum strictly. As the minimum strictly increases with that total, the best choice has total \(p\) and counts differing by at most one. It is feasible: assign each ternary axis to its designated agreeing pair, with two available symbols, and let all choices be distinct on the other axes. This proves the claimed upper bound and its exact attainment conditions among positive triples.

For \(p\le3\), \(E(p)=6+2p\), so (3) already proves the result. For \(p\ge4\) we will use
\[
E(p)\le 2^{k-3}+6+2p,
\tag{6}
\]
strict unless \(k=p=4\) or \(k=p=5\). It suffices to check \(k=p\): at \(p=4,5\) equality holds, at \(p=6\) it is strict, and for \(p\ge6\) the increment of \(E\) is \(2^{\lfloor p/3\rfloor+1}\le 2^{p-3}\), less than the increment \(2^{p-3}+2\) on the right. The right side increases strictly in \(k\). Also \(2E(p-1)>E(p)\) for \(p\ge1\), immediately from the formula.

Suppose by induction on \(k\) that the exact formula holds for shorter tensors, and consider an array of energy **strictly below** \(3\cdot2^k+E(p)\) with \(f(o)=3\). Slice along any axis. Let \(n=2^{k-1}\ge8\), and \(p'\in\{p-1,p\}\) be the number of ternary axes remaining. The central slice has energy at least \(3n+6+2p'\) by (3). Bounds (2)–(3) give total focal-slice energy at least \(6n+6+2p'\). A positive off-center focal value adds at least \(2n\); a nonzero slice at zero focal value adds at least \(n\). Both are excluded since \(E(p)\le n/4+8+2p'\) by (6) and \(n\ge8\). Negating off-center focal values thus gives a partition of three describing precisely the nonzero off-center slices.

* For the single part \(3\), the array factors along that axis. Its energy is at least \(6n+2E(p')>6n+E(p)\) by induction, impossible.
* For parts \(2+1\), the amplitude-two slice has energy less than \(2n+E(p)-6-2p'\le (9/4)n+2\). It is a sum of two negative boxes by (4). The amplitude-one slice has energy less than \(n+E(p)-8-2p'\le(5/4)n<1.5n\), hence one negative box.
* For parts \(1+1+1\), each off-center slice has energy less than \(n+E(p)-6-2p'\le(5/4)n+2\le1.5n\), hence one negative box.

Lifting these boxes on their respective slice alternatives and using the line-zero relation reconstructs \(f\) as a positive sum of three boxes through \(o\). Such a sum cannot have energy below our candidate. This contradiction proves (1) for all \(k\).

## 4. All anchored amplitude-three minimizers, including the signed exception

For \(p\le3\), equality in (3) forces all coefficients \(c_b\ge0\) by (2), so the positive-triple classification applies. If \(p\ge4\) and (6) is strict, the same partition argument at the exact candidate energy still makes the decisive bounds in (4) and the shortest-box criterion strict. Thus the same classification holds. For \(k=p=5\), use the now established exact central minimum \(m_{k-1}(3)=64\) instead of (3)'s 62. At candidate energy 116, the amplitude-two off-center slice is then at most \(116-64-16=36<(9/4)\cdot16+2\); the amplitude-one slice is at most \(116-64-34=18<24\). Since the first axis is ternary it has only two off-center slices. This settles that equality case too.

For \(k=p=4\) the energy is 64. Along a fixed axis the partition must be \(2+1\); the central slice has energy at least 36, the amplitude-one slice at most 10 and thus a single negative box \(-W\). Since evenness follows from \(\sum_x f(x)^2\equiv\sum_x f(x)=0\bmod2\) for any nonempty tensor array, the amplitude-two slice at energy at most 20 is either at 18 or 20. At 18 it is two negative boxes, giving an ordinary positive triple. At 20 the center \(S\) has exactly energy 36, so it is a sum of three boxes in three binary-choice axes, pairwise at Hamming distance two. Their choices are precisely a three-element subset of a fixed parity class of the Boolean cube. The required other slice is \(-(S-W)\), with \(\|S-W\|^2=20\), equivalent to \(\langle S,W\rangle=12\). The only choices for \(W\) are the three already in \(S\) (yielding ordinary triples), or the bitwise antipode of the missing fourth choice in the same parity class. To see this, the missing fourth itself has inner product \(2+2+2=6\); the four other-parity choices have either all three distances one (that antipode, giving \(4+4+4=12\)) or distances one, one, three (giving \(4+4+1=9\)). The latter antipode construction yields a genuine signed coefficient in the anchored box basis: the amplitude-two slice expands as \(S-W\), with a negative coefficient at \(W\), and the other axis alternative has coefficient \(+1\) at \(W\). It is not an alternative positive triple.

For \(k\ge2\), the number of ordinary minimizers at a fixed positive focal cell is
\[
\frac16\binom{3}{s}\,
\frac{p!}{((\ell+1)!)^s(\ell!)^{3-s}}\;
2^p\prod_{i:q_i\ge4}(q_i-1)(q_i-2)(q_i-3),
\qquad p=3\ell+s .
\tag{7}
\]
The factorial and binomial factors allocate the ternary axes among the three agreeing pairs. Each has two choices of the symbol for that pair; the remaining factors choose three distinct alternatives on every nonternary axis. The three boxes are distinct when \(k\ge2\) (no pair has enough agreements), and the anchored basis is unique, so division by six is exact. When \(k=1\), the count is \(\binom{q_1-1}{3}\) if \(q_1\ge4\), and two if \(q_1=3\). In the sole exceptional case \(k=p=4\), formula (7) gives 96. For the signed exception choose which off-center slice is the single box (two choices), the center parity class (two), and its missing member (four). For a fixed slicing axis the reconstruction is unique and all such arrays are distinct. This adds exactly 16, giving 112.

## 5. Rigidity threshold for every amplitude and the eventual agreement exponent

**General threshold.** For any \(a\ge1\), if \(f(o)=a\) and \(\|f\|^2<(a+2^{-a})2^k\), then \(f\) is the sum of \(a\) boxes through \(o\), with repetitions allowed. Induct in \(a\) and then in \(k\). At \(a=1\) this is the shortest-box criterion in section 1; at \(k=0\) it is immediate. Slice with \(n=2^{k-1}\). The lower bound \(|b|n\) on a slice of focal value \(b\), and \(n\) on a nonzero zero-focal slice, again force all positive focal mass in the center and all other nonzero slices to have negative focal values, of magnitudes summing to \(a\): the forbidden alternatives cost at least \(2an+n\), and the budget is strictly below \(2an+2^{1-a}n\le 2an+n\). A single other magnitude \(a\) factors the corresponding root and lowers \(k\). Otherwise each magnitude \(b<a\) has slice energy less than \(bn+2^{1-a}n\le(b+2^{-b})n\). Applying the induction hypothesis to its negative and lifting the boxes completes the proof. Unlike (4), this simple threshold does not keep track of additive slack for small \(k\).

Fix \(a\ge2\), and put \(C=\binom a2\), \(s_i=\min(q_i-1,a)\). Let \(A(a,s)=\min_{\sum_{j=1}^s n_j=a,\ n_j\ge0}\sum_j\binom{n_j}{2}\) for integer occupancies; the minimum is obtained by splitting \(a\) as evenly as possible among the \(s\) bins. Define \(T=\sum_i A(a,s_i)\). Among all \(a\)-tuples of anchored boxes, if \(e_{uv}\) is the agreement count between its \(u\)-th and \(v\)-th choices, their squared norm is
\[
a2^k+2\sum_{u<v}2^{e_{uv}}.
\tag{8}
\]
Every such tuple has \(\sum_{u<v}e_{uv}\ge T\), so Jensen gives a lower bound \(2C\,2^{T/C}\) on its correction.

For an upper construction, group axes by \(s_i\). In each category use assignments realizing the balanced occupancies. On every full block of \(a!\) such axes use all row permutations of a single assignment; thus each pair of rows has identical agreement count within the block, by symmetry. On its final incomplete block use any minimizers of the same occupancy bound. There are at most \(a-1\) categories and at most \(a!-1\) incomplete positions in each, so all \(e_{uv}\le T/C+K_a\) with \(K_a=(a-1)(a!-1)\). This gives correction at most \(2C\,2^{T/C+K_a}\). Since \(s_i\ge2\) and \(A(a,2)<C\), this upper correction is strictly below \(2^{k-a}\) once \(k\) is large enough depending only on \(a\), uniformly over the alphabets. Explicitly it suffices that
\[
\bigl(1-A(a,2)/C\bigr)k>a+\log_2(2C)+K_a.
\]
By the general rigidity threshold every minimizer is then a positive sum; (8) consequently gives an *exact reduction* to the minimum agreement cost for \(a\) rows. In particular the real minimum, despite allowing signed integer lattice coefficients before minimization, satisfies
\[
\log_2\bigl(m(a)-a2^k\bigr)
=\frac{T}{C}+O_a(1)
\]
with an error bounded between \(\log_2(2C)\) and \(\log_2(2C)+K_a\) in this regime. When every axis is ternary, \(A(a,2)=\binom a2-\lfloor a^2/4\rfloor\), so the exact asymptotic exponent per axis is \(1-\lfloor a^2/4\rfloor/\binom a2\). This use of balanced cuts does not assume that a finite configuration can make all row pairs equally distant; the incomplete blocks account for that issue.

## Prior work and exact replay

[Krotov and Potapov](https://doi.org/10.1134/S0555292319040028) study Latin bitrades in the ternary hypercube, in particular possible small cardinalities. A \(\{0,\pm1\}\) line-zero array in the ternary cube is exactly a signed bipartite unitrade, so those known results concern the unit-amplitude sector. This work deliberately isolates the sector with a specified coefficient two, three, or more; support size alone is no longer the Euclidean energy there. We do not claim priority for the standard tensor-root model or for the known unitrade spectrum, nor exhaustive literature novelty. The earlier [projected cube note](tensor-root-projected-cube.md) treats different Voronoi geometry, not a proof dependency.

Run **node verify-tensor-root-anchored-energies.js**. The executable tests use only generated small root arrays, integer arithmetic and built-in assertions. In particular the exceptional dimension-four tensor count is replayed by exact anchored-slice enumeration; the proofs apply without enumeration to arbitrary tensor sizes.
