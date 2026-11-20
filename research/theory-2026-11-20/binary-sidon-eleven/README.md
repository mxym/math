# The maximum binary Sidon set in dimension eleven is at most 54

**Archival checkpoint.** The assertion is unconditional. A binary Sidon set is a set in which the sums of all unordered pairs of distinct elements are distinct. Equivalently, four distinct elements never sum to zero. The previous published interval was 48–58; this note leaves the exact maximum undetermined. The executable proof generates or certifies all classes used; it does not assume a code-classification count.

## Structural reduction

Let $S\subseteq V_d=\mathbb F_2^d$ be Sidon, with $n=|S|$. For a linear functional $u$ put $w_u=\sum_{x\in S}(-1)^{u(x)}$. The two fibers of a nonzero $u$ have sizes $(n\pm w_u)/2$. Orthogonality gives
$$
 \sum_u w_u^2=2^d n,\qquad \sum_u w_u^4=2^d(3n^2-2n).
$$
Only four equal entries and two equal pairs contribute to the ordered zero-sum quadruples. Write $L=n\bmod 2$ and $Q=2^d$. If all hyperplanes contain at most $k$ points, then for all nonzero $u$ we have $L\le w_u^2\le H=(2k-n)^2$, with $k\ge\lceil n/2\rceil$. Summing $(w_u^2-L)(w_u^2-H)\le0$ away from the zero functional gives
$$
 Q(3n^2-2n)-n^4-(L+H)(Qn-n^2)+LH(Q-1)\le0.
$$
Let $h(d,n)$ be the smallest such $k$ satisfying this inequality. Some affine hyperplane contains at least $h(d,n)$ points. In particular $h(11,55)=33$: the expression at $k=32$ is 387,072.

Fix a hyperplane and write the two layers as $A,B\subseteq V_{d-1}$. Their union with different last coordinates is Sidon exactly when both layers are Sidon and their sets of unordered distinct-pair sums are disjoint. A forbidden quadruple meeting both layers has exactly two points in each. We may translate $B$ while fixing $A$ by an affine shear. After requiring $0\in B$, its other points are chosen from the neighbors of zero in the Cayley graph with $x,y$ adjacent iff $x\ne y$ and $x+y$ is not a pair sum of $A$. They must form a clique together with zero. During extension, additionally exclude $x+y+z$ for every three selected points. At the final 55-point check even the ordinary clique condition suffices.

## Completeness certificate

For fixed $d,n$, the archive supplies candidate affine classes $S$ of size $n$ in $V_d$. For each class $A$ of size $a\ge h(d,n)$ in $V_{d-1}$ and $b=n-a>0$, let $L(A,b)$ count **all labeled** Sidon $b$-subsets $B$ containing zero and satisfying the pair-sum condition. Let $N_a(S)$ count the affine hyperplanes containing exactly $a$ points of $S$; complementary parallel hyperplanes are distinct. Write $G(X)$ for the order of the affine stabilizer of $X$ in its ambient space. Then
$$
 \sum_{[S]} \frac{N_a(S)}{G(S)}
 =\sum_{[A]: |A|=a} \frac{L(A,b)}{b\,G(A)}.
$$
For the left side, count labeled pairs consisting of a cap and a marked hyperplane and divide by $|\mathrm{AGL}(d,2)|$. For the right side, fix a hyperplane, choose a labeled affine image of an anchor representative, and place its other layer. If $D=2^{d-1}$, the total number of labeled admissible $B$'s is $D\,L(A,b)/b$, by counting distinguished points and using translation invariance. The stabilizer of a fixed hyperplane has order $D|\mathrm{AGL}(d-1,2)|$. Cancellation gives the formula without any assumption on translation stabilizers.

The representatives are checked Sidon, spanning and pairwise affine-inequivalent. Consequently their left sides are lower bounds for the true masses. Equality for all admissible size $a$ gives completeness: an omitted class contributes positively for at least one such (a). The same test with an empty candidate list proves nonexistence. By heredity, excluding size $n$ excludes all larger sizes. Each retained set in the induction exceeds the maximum in one dimension less, so cannot be nonspanning.

The base uses no external classification. In dimension 5 the pair count prohibits a ten-point Sidon set. An affine-spanning ten-point set in dimension 6 can be normalized to contain the ordered standard affine frame; direct extension of that frame yields none. Hence every candidate of size at least 10 in dimension 7 spans dimension 7. For the standard 8-point affine frame, the numbers of labeled Sidon extensions to sizes 10, 11, 12, 13 are **1400, 10920, 21840, 0**. These counts equal $\sum_{[S]}8!\,b(S)/G(S)$, where $b(S)$ counts unordered affine bases in $S$; this follows because the affine group acts sharply transitively on ordered frames. Hence the supplied two 10-point classes, one 11-point class, and one 12-point class suffice.

| Dimension | Sizes screened | Certified class counts in order |
|---|---|---|
| 7 | 10,11,12,13 | 2,1,1,0 |
| 8 | 14,15,16,17,18,19 | 5,5,3,1,1,0 |
| 9 | 21,22,23,24,25 | 738,127,8,1,0 |
| 10 | 33,34,35 | 7,1,0 |

For the seven size-33 classes, the left/right sums for 9-dimensional anchor sizes (21,22,23,24) are respectively (961/6,851/10,0,0); for size 34 they are (0,7,0,0). Finally every hypothetical 55-point set has either 33 points in a hyperplane and 22 opposite, or 34 and 21. For each of the eight possible anchors, the opposite clique count is zero.

## How to replay

Run `./replay.sh` with a C++17 compiler and Python 3.10+ (standard library only). No network, downloaded database, SAT solver, floating-point optimization or proprietary algebra package is needed. Set `JOBS=1` to use one worker, or a small higher value for faster checks. Every element is an unsigned binary-coordinate word printed in decimal; addition is bitwise XOR. The program prints the computed mass in every case and aborts on any failed equality. The two final clique implementations have different recursion: the C++ counter traverses a greedy color-ordered search tree, while Python extracts an explicit union of (t-1) independent sets and branches on all remaining vertices when a (t)-clique would be needed.

`group.cpp` checks stabilizers exactly. With an origin $p$ distinguished, enumerate images of a basis of the translated set $S-p$ inside $S-q$. At every step test the membership indicator on the whole span, so a leaf is precisely a linear isomorphism with the required action. Summing over all $q\in S$ counts every affine automorphism once. Equivariant colors in the code prune this search: repeatedly apply the binary Walsh transform to a weighted function supported on the translated set $S-p$, relabel its values by a fixed function of old and new colors, and transform back. Under a linear change of variables the primal and dual coordinates merely permute. All unsigned arithmetic for these color labels is in the ring modulo $2^{64}$; this is **not** a randomized equivalence test. Equal colors are never evidence of isomorphism. Distinct invariant fingerprints certify inequivalence; a hypothetical collision can only fail the distinctness check or allow extra nodes in the exact isomorphism count. All mass arithmetic is exact rational arithmetic.

## Prior work and scope

- Czerwinski and Pott (online 2023, journal 2024), [Sidon sets, sum-free sets and linear codes](https://www.aimsciences.org/article/doi/10.3934/amc.2023054), and Czerwinski and Pott, [On large Sidon sets](https://doi.org/10.1016/j.jcta.2025.106129) ([author preprint, Table 2](https://arxiv.org/html/2411.12911v3)), give the eleven-dimensional baseline. The existing 48-point lower bound is not new here.
- D. Thornburgh, [A new upper bound for Sidon sets in $\mathbb F_2^{4k+3}$](https://arxiv.org/abs/2609.27731), September 2026, gives a general bound; at dimension 11 it does not improve 58. Results for Sidon subsets of integer intervals are a different problem.
- I. Bouyukliev and Z. Varbanov, [Some results for linear binary codes with minimum distance 5 and 6](https://www.moi.math.bas.bg/moiuser/~iliya/pdf_site/getPDFbvar.pdf), IEEE Trans. Inf. Theory 51 (2005), Theorem 5.4 and Table IV, previously report the unique [34,23,6] and seven [33,22,6] codes. This can shorten the proof, but neither table is required by the replay. An affine-spanning $n$-point cap in dimension 10 corresponds to the even code with homogeneous parity-check columns $(1,x)$, of length $n$, dimension $n-11$, and minimum distance at least six.
- Table entries elsewhere in the 2005 paper must not be transferred without checking. For example its Table III gives 16,062 for [19,10,5]; the later primary enumeration [Optimal Linear Codes and Their Hulls](https://doi.org/10.3390/math13152491) gives 31,237. Also a census of *all* codes with minimum distance six is not necessarily a census of even codes. The orbit-mass proof avoids these pitfalls.

This is a finite-computation upper bound, not a determination of the maximum. No claim of peer review is made.

[Download the exact replay bundle](Sidon11_54_v1.zip) (SHA-256 `c55ab3055766f5a9f134152d01a6f0d5a95df2224ee1697cccf6e0fac7571cc6`) or read the [completed replay transcript](replay.log). Verify `sha256sum -c SHA256SUMS` after extraction before running `./replay.sh`.

**Superseded for dimension eleven:** the [complete exact proof](exact48/README.md) gives maximum 48. This directory preserves the earlier intermediate upper bound 54.
