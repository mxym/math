# Trifferent row supports and exact Schmidt-rank thresholds for simplex-filtered Werner states

**AI-assisted research draft, 18 November 2026.** See [review and reproducibility](REVIEW.md) for the limits of the independent AI check. A rank-two test is made after a specified filter on Alice, not on the unrestricted Werner tensor power. Nothing here proves or disproves NPT bound entanglement.

## Statement and context

Use the sign convention $\rho_d(t)=(I-tF)/(d^2-dt)$, $0\le t\le1$, where $F$ swaps the two input factors. Its partial transpose on Bob is proportional to $W_d(t)=I-t|\Omega_d\rangle\langle\Omega_d|$, with unnormalized $\Omega_d=\sum_i|ii\rangle$. The partial transpose of $n$ copies is proportional to $W_d(t)^{\otimes n}$, with all Alice factors grouped, and all Bob factors grouped. Identify a bipartite test vector with an arbitrary complex coefficient matrix $C$; its Schmidt rank equals $\operatorname{rank} C$. The quadratic form is
$$
 q_{n,t}(C)=\sum_{S\subset[n]}(-t)^{|S|}\|\operatorname{Tr}_S C\|_F^2 .
$$
For each local projector $|\Omega\rangle\langle\Omega|$, the contraction of $\mathrm{vec}(C)$ with $\langle\Omega|$ is $\mathrm{vec}(\operatorname{Tr}_i C)$, proving the identity by expansion. Rank-two positivity is exactly the single-block undistillability test. The long-standing open question asks about all tests, for every number of unfiltered copies. Two-copy and three-copy results have been reported; the full four-copy endpoint $t=1/2$ is not assumed here.

Let $A\subset[d]^n$ be a classical code, with coordinate span $V_A=\operatorname{span}\{|x\rangle:x\in A\}$. Project Alice onto $V_A$ and leave Bob unfiltered. The filter has success probability $|A|/d^n>0$, since Alice's original marginal is maximally mixed. Since the projection is on Alice only, this compresses precisely the above partial transpose on the row index, up to a positive normalization factor. A **trifferent** code (a perfect 3-hash code) separates each triple of distinct words in at least one coordinate: at that coordinate all three letters differ.

**Theorem 1.** Suppose $A$ is trifferent with minimum Hamming distance $D\ge1$. For $0\le t\le1/2$, put $z=t/(1-t)$. For every matrix with range in $V_A$, arbitrary co-range and rank at most $r$,
$$
 (r-1)z^D\le1\quad\Longrightarrow\quad q_{n,t}(C)\ge0.
$$
In particular the endpoint holds for all such rank-two tests, independently of the number of copies or codewords. If $|A|\ge2$, the endpoint is sharp among rank-two tests: any two words provide a negative test for $1/2<t\le1$ (see below).

**Theorem 2.** If, in addition, all pairwise distances equal one **odd** number $D$, then, for every $2\le r\le M:=|A|$, the exact threshold for nonnegativity of the filtered partial transpose on vectors of Schmidt rank at most $r$ is
$$
           t_r=\frac1{1+(r-1)^{1/D}}.
$$
The filtered state is separable precisely for $0\le t\le t_M$, and NPT precisely for $t_M<t\le1$. Thus $t_2$ is the single-block distillability threshold, not a claim about arbitrarily many independent filtered blocks. Rank one is always nonnegative, since a product test of a partial transpose is a product test of the original state with the Bob vector conjugated. No test has rank greater than $M$ after the filter. This hierarchy concerns the Schmidt ranks of **test vectors**, not the Schmidt number of the mixed state.

**Explicit family.** Take the ternary simplex code with $M=3^k$, $n=(3^k-1)/2$, $D=3^{k-1}$, $k\ge1$. Its messages are $a\in\mathbb F_3^k$; a coordinate is $\ell(a)$ with one linear form $\ell$ taken from each projective line of nonzero forms. Of the $3^k-1$ nonzero linear forms, exactly $2\cdot3^{k-1}$ are nonzero on any given nonzero difference; division by two gives the stated odd distance. For distinct messages $a,b,c$, if $b-a,c-a$ are independent choose a form taking values $1,2$ on them. If they are dependent, then $c-a=-(b-a)$, so any form nonzero on the latter separates. Scaling the form does not affect separation. At $k=2$ this gives four qutrit copies, a nine-dimensional Alice filter, and $t_9=1/3$, $t_2=1/2$, with all intermediate ranks specified exactly.

## Proof of Theorem 1: separating collision sectors

Denote Hamming distance by $h(x,x')$. Group every row-column pair $(x,y)$, with $x\in A$, by its mismatch set $T=\{i:x_i\ne y_i\}$ and the two strings $a=x|_T, b=y|_T$. This sector $E=(T,a,b)$ has admissible rows $B_E=\{x\in A:x|_T=a\}$; for each such row $x$, let $y_x$ agree with $x$ outside $T$ and with $b$ on $T$. Its coefficient is $d_x=C_{x,y_x}$. In a single local factor, an off-diagonal basis pair $(u,v), u\ne v$ is an isolated entry of weight one; the equal-letter pairs have matrix entries $1-t$ on the diagonal and $-t$ off the diagonal. Tensoring gives a direct sum of sectors; for $t<1$ the contribution of a sector is exactly
$$
 w_E\sum_{x,x'\in B_E}(-z)^{h(x,x')}\overline{d_x}d_{x'},
 \qquad w_E=(1-t)^{n-|T|}.
$$
All distances here are outside $T$, since rows agree on $T$.

For each sector with $|B_E|\ge2$, make the square submatrix $X_E=(C_{x,y_j})_{x,j\in B_E}$. Its columns are distinct: two different words in $B_E$ differ outside $T$. Thus $\operatorname{rank}X_E\le r$.

Two disjointness facts justify using the off-diagonal entries to compensate the sector.

1. If $x\ne j\in B_E$, the entry $(x,y_j)$ lies alone in its own sector. Its mismatch set is the disjoint union of $T$ and the coordinates where $x,j$ differ. A different row in its sector would have to agree with $x$ on this whole union. The row $j$ cannot do so. A third row $u$ cannot either: a coordinate separating $x,j,u$ lies outside $T$ and has $u\ne x$.
2. This entry cannot be charged to two different sectors and off-diagonal positions. Given $(x,y)=(x,y_j)$ being charged, every coordinate where $x\ne j$ must have $y=j$ there. If two different partner words $j,j'\ne x$ could charge it, a coordinate separating $x,j,j'$ would force $y$ to equal two different letters. For fixed partner $j$, recover the original parent exactly from $T=\{i:j_i\ne y_i\}$, $a=j|_T$, $b=y|_T$.

The singleton's entire weight is $w_E(1-t)^{-h(x,j)}$, and uncharged singletons are nonnegative. For $z\le1$ and $\lambda=z^D$, every off-diagonal entry of the sector kernel has modulus at most $\lambda$. Also $(1-t)^{-h(x,j)}\ge1+\lambda$, since $(1-t)^D+t^D\le1$. Hence the parent sector and its disjoint singleton charges together contribute at least
$$
 w_E\big[(1+\lambda)\|X_E\|_F^2-\lambda(\textstyle\sum_x|X_{E,xx}|)^2\big]
 \ge w_E[1-(r-1)\lambda]\|X_E\|_F^2 .
$$
Indeed, $\sum |X_{xx}|\le\|X\|_*\le\sqrt{\operatorname{rank}X}\,\|X\|_F$, with the first bound following by multiplying by a diagonal unitary so that the diagonal entries have one phase. Summation proves Theorem 1.

For any code with two distinct words, on the diagonal sector restricted to those words the scaled kernel is $\begin{pmatrix}1&(-z)^h\$-z)^h&1\end{pmatrix}$. Its smaller eigenvalue is negative for $1/2<t<1$; its eigenvector is a matrix of rank two. At $t=1$, choose the mismatch set to be *all* coordinates where these two words agree and replace their common column letters there by different letters. The principal two-word submatrix has zero diagonal and nonzero off-diagonal $(-1)^h$. The two corresponding columns are distinct, again giving rank two.

## Exact hierarchy and separability

If $D$ is the common, odd distance then for every sector the kernel equals $(1+\lambda)I-\lambda J$ with $\lambda=z^D$, for any $0\le t<1$. Theorem 1 proves the lower side of the claimed rank thresholds. For the upper side, choose any $r$ words and the diagonal operator $C=\sum_{j=1}^r |x_j\rangle\langle x_j|$. Then
$$
 q_{n,t}(C)=(1-t)^n r[1-(r-1)\lambda],
$$
strictly negative for $t_r<t<1$; at $t=1$ the preceding two-word witness suffices.

There is an exact local-embedding decomposition, not just a scalar inequality. For each multi-entry sector take the independent left and right basis isometries indexed by $B_E$, sending the abstract label $j$ to row $|j\rangle$ and column $|y_j\rangle$, respectively; in the row notation $j$ denotes a codeword. Insert under these isometries
$$
 w_E(1+\lambda) W_{|B_E|}(\tau),\qquad \tau=\lambda/(1+\lambda).
$$
On the matched entries this has exactly the required kernel. On the off-diagonal positions it consumes $w_E(1+\lambda)$ of the singleton weight. Disjointness was proved above, and the residual is nonnegative because $(1-t)^{-D}\ge1+\lambda$, valid for all $0\le t<1$. The entire remaining operator is diagonal in the product basis with nonnegative entries, hence separable. Equivalently the filtered (untransposed) state, up to normalization, decomposes into local embeddings of $I-\tau F$ plus separable residual. The basis isometries are real, so partial transposition commutes with them in these formulas.

For dimension $m\ge2$, $I-F/m$ is separable: the $U\otimes U$ twirl of a product of orthogonal unit vectors lies in $\operatorname{span}\{I,F\}$, has zero swap expectation, and is proportional to that operator. The identity is also separable, so $I-\tau F$ is separable when $\tau\le1/m$. At $t\le t_M$, $\tau\le1/M\le1/|B_E|$, proving separability of the filtered state. The negative test at $r=M$ proves NPT above the threshold.

## Relation to prior work; scope

* [Horodecki–Rudnicki–Życzkowski, Five Open Problems in Quantum Information Theory (2022)](https://doi.org/10.1103/PRXQuantum.3.010101): the unrestricted NPT question is Problem 4; Problem 5 concerned only two copies of one specific Werner state.
* [Costa Rico, New partial trace inequalities and distillability of Werner states (2025)](https://doi.org/10.1007/s11005-025-01935-y) develops the rank-constrained partial-trace criterion. [Bharti–Gajjala–Haug (2026)](https://arxiv.org/abs/2607.24479) and several independent preprints prove the two-copy result; [Tomar (2026)](https://hexagonmath.org/2611.00464v1) reports the unrestricted three-copy endpoint, an unrestricted four-copy bound $t\le79/160$ in all dimensions, and $t\le0.4979$ for four qutrit copies (Theorems 1.1–1.4). These are preprint results, not verified again here. In particular, the qutrit window does not reach $t=1/2$.
* [Tomar, Equality cases and every-copy results (2026)](https://hexagonmath.org/2611.00466v1) also reports the four-copy endpoint when range and co-range lie in a common two-dimensional plane. His paper, particularly §§4.2–4.6, gives the Hamming-sign sector kernel and uses lone off-diagonal entries to protect parts of a special GHZ-with-tails support. We do **not** claim the sector kernel, isolation idea, diagonal-trace bound, or every-copy method itself is new. Here a perfect-hash property guarantees isolation and prevents double-counting for **every** multi-entry sector with unrestricted co-range, yielding an exact rank hierarchy on large equidistant codes.
* [Mishra–Senthilkumar, current collection](https://github.com/anshM123/werner-npt-research), notably the two-sector, repetition, and cyclic graph-state code results, treats different restrictions, including a computer-assisted common-plane result at the four-qutrit endpoint and separate every-copy restrictions. The present nine-row four-qutrit example restricts the row support while allowing arbitrary co-range; the ambient local dimension on each side before filtering is 81. A separate corollary below uses their explicit two-sector theorem.
* The combinatorial codes are classical. [Bishnoi–D'haeseleer–Gijswijt–Potukuchi (2024)](https://doi.org/10.1112/jlms.12938) and [Yuan–Zhu (2026)](https://arxiv.org/abs/2611.11262) study trifferent codes, including positive-rate families. We do not improve a code size or rate. Searches including “Werner”, “trifferent”, “perfect hash”, “simplex code”, sparse rows, partial trace and endpoint did not surface these filtered threshold formulas. This is not a proof of priority.

## A tensor-product consequence (uses recent finite-copy theorems)

Partition the physical copies into up to three blocks. In each block use an odd-equidistant trifferent row code as in Theorem 2, and allow every joint test of Schmidt rank at most two on the product of the code spans, with Bob arbitrary. At the physical endpoint $t=1/2$, $\tau=1/2$ for every block. The product-filtered partial transpose is a sum of local images of tensor products of at most three $W_m(1/2)$'s and product positive operators. Each embedding is a left–right product of linear maps; contracting rank-one terms of the separable operators locally cannot increase Schmidt rank. For possibly different $m$, each $W_m(1/2)$ is the matching local coordinate compression of $W_{\max m}(1/2)$. Nonnegativity follows from the one-, two-, or three-copy theorem in the larger dimension. For two blocks no three-copy result is used. For three this corollary is conditional on the correctness of the recent all-dimension three-copy theorem, not re-proved here. This covers product supports which need not themselves be trifferent. It does not assert unbounded-block tensor-stability.

The companion [coordinate-support note](COORDINATE_SUPPORTS.md) gives the all-rank endpoint classification, its sharp dimension bounds in a ternary alphabet, and the four-row sparsity consequence (which uses an additional two-sector result). In `check.py`, run `python3 -B -O check.py`. This diagnostic checks every matrix coefficient of the 729-dimensional four-qutrit tetra-code compression at four rational parameter values against the cone decomposition, using exact integers/rationals. It checks every diagonal witness rank and the special $t=1$ endpoint. These checks supplement, not replace, the analytic proof.
