# The all-degree Easy Coefficients Conjecture for Cusick's rules matrix

## Statement and conventions

Fix a finite list of generators of monomial rotation-symmetric Boolean functions. Write the offset sets of the nonlinear generators as $D_\alpha=\{0=d_{\alpha,0}<d_{\alpha,1}<\dots<d_{\alpha,r_\alpha-1}=L_\alpha\}$ with $L_\alpha\ge1$, and let $\ell\in\{0,1\}$ record the optional linear generator. Define
\[
g_n(x)=\ell\sum_{t=0}^{n-1}x_t+
       \sum_\alpha\sum_{t=0}^{n-1}\prod_{d\in D_\alpha} x_{(t+d)\bmod n}
       \quad\text{over }\mathbb F_2,\qquad n\ge1.
\]
Put $L=\max_\alpha L_\alpha$ (or zero in the absence of nonlinear terms). Let $R$ be the matrix constructed by [Cusick's general rules algorithm](https://arxiv.org/pdf/1701.06648), §4.1, on this list. Remove exactly one distinguished occurrence of $2$ from the characteristic multiset of $R$ (the occurrence supplied by its last coordinate), and discard zeros. Let $\lambda_1,\dots,\lambda_q$ be the remaining multiset over $\mathbb C$, including algebraic multiplicities. Then
\[
\operatorname{wt}(g_n)=2^{n-1}-\tfrac12\sum_{j=1}^q\lambda_j^n
\quad\text{for every }n\ge1.
\]
This is the weight of the usual monomial orbit-sum convention for $n>2L$. At smaller $n$, $g_n$ counts all indexed translates with multiplicity, so its weight need not equal the convention counting each orbit element only once. In particular, the formula is the unique backward extension to positive $n$ of the eventual weight recurrence specified by the nonzero factor of the minimal polynomial of $R$. Any further occurrence of $2$ is treated with coefficient $-1/2$, just like any other occurrence. No higher-degree nonsingularity, squarefreeness or diagonalizability assertion is needed.

The scope is fixed lists of normalized, positive-degree monomial rotation generators, the input of the published algorithm, not arbitrarily chosen functions separately for each $n$. If a nonlinear generator repeats, it may be kept as a separate block; its translates are added with the usual parity convention. If the linear generator repeats, first replace all its copies by their parity (the raw source's redundant-linear-item deletion loop is not part of this claim). The zero family and the purely linear family are trivial; the source explicitly handles the latter by recurrence polynomial $X-2$.

## 1. Exact recognition of the signed block

Use $L_\alpha$ bits $q_{\alpha,k}$, $0\le k<L_\alpha$, for the block of generator $\alpha$, addressing the least significant bit by 0. The state set $Q$ is the Cartesian product of these blocks. Use the source convention of columns as origins and rows as destinations. Its signed block $A$ has a deterministic transition for each input $\epsilon\in\{0,1\}$:
\[
 q'_{\alpha,0}=\epsilon,\qquad
 q'_{\alpha,k}=q_{\alpha,k-1}\epsilon^{[k\in D_\alpha]}\quad(1\le k<L_\alpha),
 \qquad
 s_\epsilon(q)=(-1)^{\epsilon(\ell+\sum_\alpha q_{\alpha,L_\alpha-1})},
\]
where $\epsilon^0=1$. These transitions describe the actual source columns, as follows.

1. The arXiv algorithm's increasing monomial indices start with 1. Subtracting 1 yields our offsets. In the loop for each generator its variable ik equals $L_\alpha+1$. Its block integer fkb has $L_\alpha$ bits, so the branches testing fkb equal to $2^{L_\alpha}$ are unreachable. The padded binary list fkbits has one extra leading zero, so list entry 2 is the old top bit.
2. The initial lftfk calculation is twice fkb modulo $2^{L_\alpha}$. For internal one-based monomial index $j=1+d$, the algorithm tests padded entry ik minus $j$ plus 2, i.e. the old bit of index $d-1$. If that bit is 1, it subtracts $2^d$ from the shifted integer. Distinct internal offsets clear distinct occupied bits, with no borrowing. This is the transition at $\epsilon=0$, always of weight $+1$.
3. The magnitude of rtfk is twice fkb plus 1, modulo $2^{L_\alpha}$; this is odd and nonzero. The sign is negative exactly when the old top bit is 1. Hence the product of signs is unchanged by adding 0.25 to each signed odd integer, as the original program does in the testcase product. Exactly one linear generator reverses the entire right multiplier, but does not change the target or left multiplier. This gives the $\epsilon=1$ case.
4. The concatenated block results are precisely the Cartesian-product indexing. All blocks read the same input bit. The two targets differ in their least significant bits, as long as some nonlinear block exists, so the program's assignments do not overwrite one another within a column. Reordering different-width blocks simply permutes state coordinates. Identical nonlinear generators can be repeated without changing these transitions, and two copies contribute zero total sign exponent on a compatible periodic path.

The last coordinate augments the signed block to
\[
 \begin{pmatrix} A&0\\c&2\end{pmatrix},
\]
where $c$ records the negative right branches. Any zero row and its matching column may be deleted without changing the nonzero characteristic multiset: expanding the old characteristic determinant along that row supplies a factor $X$ times the new determinant. This applies also to iterative deletion. No other feature of $c$ is needed. In the purely linear case, viewing the two labels as parallel edges on a single state yields signed entry $1-1=0$, consistent with the source's $X-2$ recurrence. For the zero function the two edges instead produce the scalar $2$ and the weight formula vanishes; one need not interpret the source loop on an empty generator list.

## 2. Each marked periodic word has one closed rules walk

Index a binary stream by $t\in\mathbb Z$. The pending monomial values immediately before reading $x_t$ are
\[
 q_{\alpha,k}(t)=\prod_{\substack{d\in D_\alpha\\d\le k}}x_{t-1-k+d}.
\]
Indeed, the newest input starts a term. For $k\ge1$, the old bit $k-1$ moves into bit $k$ and must be multiplied by the newest input if, and only if, $k$ is a required position. After $L$ symbols every initial bit has shifted out. Therefore a suffix of $L$ symbols determines the state regardless of the initial state before that suffix. This includes the all-zero and all-one inputs.

For any indexed periodic word of length $n$, the formula defines a closed labeled walk, including when its least period divides $n$. If two such walks existed for that word, follow enough identical rounds to read at least $L$ symbols: their states at the return to the marked position agree by forgetting, so their initial states agree. There is therefore exactly one based closed walk per indexed word; no division by $n$ is involved. For block $\alpha$, the term completed at time $t$ has product
\[
 x_tq_{\alpha,L_\alpha-1}(t)=\prod_{d\in D_\alpha}x_{t-L_\alpha+d}.
\]
The closed-walk multiplier is exactly $(-1)^{g_n(x)}$, by summing these products over one period separately for each generator, shifting $t$ by $L_\alpha$, and accounting for the linear term. Equal generator blocks cause equal contributions and cancel if they occur an even number of times.

## 3. Trace and the characteristic multiset

The closed-walk expansion and the elementary weight identity now yield
\[
 \operatorname{tr}(A^n)=\sum_{x\in\mathbb F_2^n}(-1)^{g_n(x)}
 =2^n-2\operatorname{wt}(g_n).
\]
Moreover, let $B$ be the signed de Bruijn matrix on $L$ bits whose transitions append the input and whose sign is the same monomial-completion sign evaluated on the history. It has the identical periodic-word trace, again for every positive $n$. Over $\mathbb Q$ or $\mathbb C$, the formal Newton identity
\[
 \det(I-zM)=\exp\!\left(-\sum_{n\ge1}\operatorname{tr}(M^n)z^n/n\right)
\]
follows by triangularization over $\mathbb C$ and scalar logarithm expansions. Hence
\[
 \det(I-zR)=(1-2z)\det(I-zA)=(1-2z)\det(I-zB).
\]
This proves exact matching with the characteristic multiset of the published rules matrix. It ignores only zero roots of the characteristic polynomial in $X$. Independently, a triangular form gives $\operatorname{tr}(A^n)$ as the sum of the $n$-th powers of its eigenvalues, with full algebraic multiplicity. This is the asserted formula.

For $n>2L$ a nonlinear support has a unique largest circular gap, across from its largest offset to its starting point; all internal gaps are at most $L$. Thus it has full cyclic orbit and distinct normalized supports cannot become identical via rotation, unless their lists already coincide. This links the periodic definition to the eventual family even under the convention of distinct orbit monomials. The weights in the formula satisfy the recurrence defined by the minimal polynomial after stripping factors $X$: each contributing exponential has a root of that polynomial as its base. Its nonzero constant term makes the backward extension from the eventual sequence unique.

## 4. Optional strengthening: the nonzero primary subspaces are isomorphic

Send a history-state basis vector linearly to the pending-state basis vector defined by the product formula in §2. This is surjective onto the span of compatible pending states and intertwines the signed actions term by term (both the next state and the sign are identical). The quotient of the full pending-state space by its compatible span is killed by $A^L$, since every word of length $L$ sends all states into that span. The kernel of the map from history states is killed by $B^L$: for each length-$L$ input word, all initial histories lead to the same final history, and histories with the same initial pending state collect the same sign. Thus their coefficients cancel pairwise in the sense of summing within each fiber on any vector in the kernel. Both discarded components affect only eigenvalue zero. It follows that the nonzero primary parts of $A$ and $B$ are isomorphic as modules for the transition operator, not merely isospectral. The signed block here can be taken before zero-row pruning.

The independent small-parameter checks in verify.py are for interpretation and regression only and are not premises of the proof.
