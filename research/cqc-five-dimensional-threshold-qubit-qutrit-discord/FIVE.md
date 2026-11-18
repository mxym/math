# A sufficient five-dimensional triangular-discrimination bound

**Theorem.** Let $Q,R$ be any mutually unbiased orthonormal bases of $\mathbb C^5$ and $\rho,\sigma$ any two density matrices there. Let $p^M,q^M$ be their respective measurement distributions in basis $M$, and put
$$
\Delta(p,q)=\sum_{j:p_j+q_j>0}\frac{(p_j-q_j)^2}{p_j+q_j},
\qquad S=\Delta(p^Q,q^Q)+\Delta(p^R,q^R).
$$
Then $S\le53/14$. In particular this holds for any pair of orthonormal pure states, the case in [Qian, §11(3)](https://arxiv.org/html/2608.14806v2#S11).

### 1. A layer integral

For $0\le t\le1$ set $L_t(p,q)=\sum_j[(1-t)p_j-(1+t)q_j]_+$, where $[x]_+=\max(x,0)$. Integrating the line $[|p_j-q_j|-t(p_j+q_j)]_+$ on its positive interval gives $(p_j-q_j)^2/[2(p_j+q_j)]$ for each nonzero denominator. This line is the sum of the two directed positive parts, so
$$
\Delta(p,q)=2\int_0^1[L_t(p,q)+L_t(q,p)]\,dt.
$$

At fixed $t$, one direction summed over **both** bases equals
$$
\max_{U,V}\operatorname{Tr}\Big( [(1-t)\rho-(1+t)\sigma](P_U+Q_V)\Big),
$$
where $P_U,Q_V$ project onto arbitrary subsets of $Q,R$, respectively. Indeed one includes precisely the positive diagonal entries in each basis. Define
$$
M(t)=\max_{K=P_U+Q_V}\{(1-t)\lambda_{\max}(K)-(1+t)\lambda_{\min}(K)\}.
$$
Unit-trace positivity bounds each directed sum by $M(t)$; the reverse direction obeys the same upper bound. This proves $S\le4\int_0^1 M(t)\,dt$ without any purity assumption.

### 2. Spectra of the subset projections

By Haagerup’s classification of order-five complex Hadamard matrices (see [Tadej–Życzkowski](https://arxiv.org/abs/quant-ph/0512154) or [Qian, Theorem 6.1](https://arxiv.org/html/2608.14806v2#S6)), the normalized overlap matrix is the Fourier matrix $F_{jk}=e^{2\pi i jk/5}/\sqrt5$ up to row/column phases and permutations. These changes preserve the set of attainable submatrix singular values. Set
$$
c=\sqrt{(5+\sqrt5)/10},\qquad C=\sqrt{(7+\sqrt5)/10}.
$$

Write $r=|U|,s=|V|$ and $W=F_{U,V}$. If $B$ concatenates the two lists of basis columns, $K=BB^*$ and $B^*B$ has diagonal identity blocks and off-diagonal blocks $W,W^*$. Its eigenvalues are $1\pm\sigma_i(W)$ for the $\min(r,s)$ singular values and $|r-s|$ extra ones. The two Gram matrices have the same **nonzero** eigenvalues; when $r+s=5$ they have the same full spectrum.

* **$r+s<5$.** There is a kernel. For nonempty lists with one row or one column the norm is $\sqrt{k/5}$ for $k\le3$. The only other rank pair is $(2,2)$. A two-row Gram matrix has diagonal $2/5$ and off-diagonal of magnitude $2|\cos(\pi h/5)|/5$, where $h$ is the product of the nonzero row and column index differences modulo five. Its eigenvalues are therefore $(2\pm2|\cos(\pi h/5)|)/5$. Over $h=1,2,3,4$ the largest is at most $c^2$, and the smallest at least $(3-\sqrt5)/10$. Thus $\lambda_{\max}(K)\le1+c$ and $\lambda_{\min}(K)=0$. Single and zero projections satisfy the same inequalities directly.
* **$r+s>5$.** Complement both subsets. The lower-rank-sum result for $2I-K$ implies $\lambda_{\max}(K)\le2$ and $\lambda_{\min}(K)\ge1-c$. The linear expression in $M(t)$ is at most $(1+c)(1-t)$: the difference between that line and $2(1-t)-(1-c)(1+t)$ is $2(1-c)t\ge0$. This covers full subsets too.
* **$r+s=5$.** Up to interchanging the lists, the nonempty ranks are $(1,4)$ and $(2,3)$, with eigenvalue extremes $1\pm\|W\|$. The first gives $\|W\|^2=4/5$. For the second, complete the two rows of $W$ with the omitted two columns to get $[W\ V]$ with orthonormal rows. Thus $WW^*=I_2-VV^*$ and the lower bound on the least squared singular value of that $2\times2$ submatrix gives $\|W\|^2\le C^2$. At ranks $(0,5)$ or $(5,0)$, $K=I$. In all cases the expression is at most $2C-2t$.

### 3. Integration and scope of the corollary

Set $b_0=1+c$, $a_0=2C$. We have $M(t)\le\max\{b_0(1-t),a_0-2t\}$. For the rational majorants $b=13/7$, $a=27/14$, it suffices to use $\sqrt5<9/4$, $(5+9/4)/10<(6/7)^2$ and $(7+9/4)/10<(27/28)^2$. The two rational lines meet at $t=1/2$. Integrating the upper line on each side, or adding the triangular excess above $b(1-t)$, gives
$$
S\le 2b+\frac{2(a-b)^2}{2-b}=\frac{53}{14}.
$$
With $a_0,b_0$ instead, the same expression is $3.76964420135\ldots$ (here $b_0<a_0<2$). This is a bound, not an equality claim for the optimization of $S$. Qian’s Theorem 6.14 attains $(14+2\sqrt5)/5=3.69442719\ldots$ with an orthonormal pair.

**CQC conclusion (restricted).** Fix Alice’s ordered qubit MUBs $Z,X$ and take one ray $|0\rangle$ from $Z$ and one ray $|+\rangle$ from $X$. For any Bob MUB pair in dimension five and any orthonormal Bob rays $u,v$, apply [Qian, Eq. (18)](https://arxiv.org/html/2608.14806v2#S6.SS3) to the state
$$
\rho_{AB}=\tfrac12 P_0\otimes P_u+\tfrac12 P_+\otimes P_v,
\qquad P_w=|w\rangle\langle w|.
$$
With $h(x)=h_2((1+x)/2)$ and natural-log binary entropy $h_2$, that paper gives
$$
G\ge h(1/\sqrt2)-\tfrac32\log(4/3)+\tfrac{\log2}{4}(2-S/2).
$$
Our rational bound is below Qian’s sufficient threshold $S_\star=3.82655830219\ldots$. In fact the right side exceeds $3/1000$ nats. For a rational check expand $h(1/\sqrt2)=\log2-\sum_{k\ge1}2^{-k}/[(2k)(2k-1)]$; after $N$ terms the omitted sum is at most $2^{-N}/[(2N+2)(2N+1)]$. For $x\ge1$, $y=(x-1)/(x+1)$, the partial sum $2\sum_{j=0}^{N-1}y^{2j+1}/(2j+1)$ is below $\log x$ with error at most $2y^{2N+1}/[(2N+1)(1-y^2)]$. [The exact replay](verify.py) substitutes $N=10$. The broad density-pair quantifier in the spectral theorem does **not** extend this bipartite corollary beyond family (8). For unrestricted $2\times5$, see Qian’s counterexamples (§7).
