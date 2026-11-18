# Four factors already violate Duchi's norm-inside matrix sampling inequality

AI-assisted research draft with independent internal AI review; not externally peer reviewed. De Sa had already disproved the general inequality. The question here is the smallest product length at which a counterexample exists, not whether every population of that length fails. No claim of priority.

## Precise statement

For $n\ge m$ real symmetric positive semidefinite matrices $A_1,\ldots,A_n$, let
$$R=\frac{1}{n^m}\sum_{w\in[n]^m}\|A_{w_1}\cdots A_{w_m}\|_{\rm op},\qquad
S=\frac{1}{(n)_m}\sum_{w\in[n]^m\;\text{injective}}\|A_{w_1}\cdots A_{w_m}\|_{\rm op}.$$
Here $(n)_m=n(n-1)\cdots(n-m+1)$. Duchi asked whether $R\ge S$. For $m=4$ and **every $n\ge5$** there are rational symmetric PSD contractions, in dimension $(n)_4$, for which $R<S$. The maps in the operator norms are products in the displayed order, with no expectation taken inside the norm.

By Israel–Krahmer–Ward the inequality holds for all unitarily invariant norms, all $n\ge m$, when $m\le3$. Consequently **four is the smallest product length at which the universal inequality can fail**. We do not assert that five is the smallest population size; in particular the theorem does not decide $(m,n)=(4,4)$ or optimal ambient dimensions. Perturbations into positive definite contractions are possible by replacing every $A_i$ by $(1-\epsilon)A_i+\epsilon I$ for sufficiently small positive rational $\epsilon$, by strictness and finite-dimensional continuity.

## Four-position template

Fix $c=99/101$, $s=20/101$, write $c+is=e^{i\theta}$, and let
$$u_j=(\cos j\theta,\sin j\theta),\quad B=(0,3,3,0),\quad
P_j=c^{B_j}u_j u_j^T,\qquad j=0,1,2,3.$$
All entries are rational and $0\preceq P_j\preceq I_2$. For each ordered injection $a:\{0,1,2,3\}\hookrightarrow[n]$ put a copy of $\mathbb R^2$ in the direct sum. On this block $A_i$ acts as $P_j$ if $a(j)=i$, and as zero if the label $i$ is missing. We may keep just those $a$ with $a(0)<a(3)$, halving the number of blocks: reflection in the line at angle $3\theta/2$ swaps $P_j$ and $P_{3-j}$ by one orthogonal conjugation. Thus every block excluded by the order constraint is equivalent to its reversal, and $\dim A_i=2(n)_4/2=(n)_4$.

For a sampled word $w$ meeting $k$ labels, let $\pi$ be its *restricted growth string*: replace the first different label by 0, the next previously unseen one by 1, etc. For any injection $f:\{0,\ldots,k-1\}\hookrightarrow\{0,1,2,3\}$ write $z_j=f(\pi_j)$, with the $k$ labels indexed from zero. Its block score is
$$p(z)=c^{\sum_{j=1}^4 B_{z_j}}\prod_{j=1}^3 |\cos((z_j-z_{j+1})\theta)|.$$
Indeed the product of the four projectors is a scalar multiple of $u_{z_1}u_{z_4}^T$, which has norm one. The norm of the direct-sum product is exactly $M_\pi=\max_f p(f\circ\pi)$: all injections of the occurring labels can be extended to blocks because $n\ge4$, omitted labels on a block give score zero, and the reversal reduction preserves the norm. There are $(n)_k$ labeled words with pattern $\pi$. Thus
$$ S=M_{0123},\qquad n^4 R=\sum_{k=1}^4(n)_k T_k,\quad T_k=\sum_{\pi:\,|\pi|=k}M_\pi. $$

## Exact certificate, no optimization oracle

For direct reproduction, the table displays one maximizing four-slot word and the integer $D M_\pi$, where $D=101^{12}$. For each row the allowed candidates are precisely the slot words with the same equality pattern. To check a maximum by hand or with integer arithmetic, use the scalar score above with overlaps $g_0=1$, $g_1=c$, $g_2=2c^2-1$, $g_3=4c^3-3c$ (all nonnegative at this angle), and enumerate the at most 24 admissible assignments. The independent [matrix checker](check.py) instead multiplies the actual scaled integer matrices to obtain their singular norms.

```
pattern  witness   D times maximum
0000     0000      1126825030131969720661201
0001     0001      1040187830828078288020401
0010     0010      1019590051999799510039799
0011     0011      979610048000199490040199
0012     0012      960211829227918312019601
0100     0100      1019590051999799510039799
0101     0101      941197733599642701880599
0102     1012      886384871716129280658801
0110     0110      960211829227918312019601
0111     1000      1040187830828078288020401
0112     0112      904291636801303609560999
0120     0120      884908480205044608498801
0121     0121      886384871716129280658801
0122     1233      960211829227918312019601
0123     0123      941197733599642701880599
```

The supplied standard-library [verify.py](verify.py) evaluates the four rational vectors by recurrence, checks the maxima over at most 24 choices per pattern, and certifies the following degree-at-most-four polynomial by exact evaluation at five distinct integers. This is polynomial verification, not extrapolation from five tested population sizes. Subtracting gives
$$n^4(S-R)=\frac{2n}{D}(a n^2-b n+e),$$
where
```
D=1126825030131969720661201
a=82396441351706403933495
b=453284944698127805248788
e=278074855080257891924992
```
The quadratic at $n=5+x$ has coefficients $a$, $10a-b$, $25a-5b+e$, all strictly positive. This proves the claim for all $n\ge5$. At $n=5$ the 120-dimensional example yields
$$ S=(99/101)^9,\qquad S-R=143122330764557928036854/140853128766496215082650125>0.$$
A second check in the same file enumerates all 625 labeled words over the 60 actual two-dimensional blocks rather than using pattern multiplicities.

Padding each matrix by the same zero direct summand extends the example to larger ambient dimensions. This is **not** a population-padding argument: appending zero matrices to the five-label population would multiply its with-replacement and without-replacement means by $(5/n)^4$ and $(5)_4/(n)_4$, respectively, and already loses the strict violation at $n=6$. The construction instead rebuilds all injection blocks for each new population.

## A small-integer explanation of the effect

Replace the fixed $c,s$ by $\cos\theta,\sin\theta$ and let $\theta\downarrow0$. On a compatible block the score is $1-(\theta^2/2) L(z)+O(\theta^4)$, where
$$ L(z)=\sum_jB_{z_j}+\sum_{j=1}^3(z_j-z_{j+1})^2. $$
There are finitely many patterns and embeddings independent of $n$, so taking a maximum of the scores uses the *minimum* loss. In lexicographic order the complete list of minima is
```
pattern   0000 0001 0010 0011 0012 0100 0101 0102 0110 0111 0112 0120 0121 0122 0123
loss         0    4    5    7    8    5    9   12    8    4   11   12   12    8    9
```
The loss sums grouped by $k=1,2,3,4$ are $0,42,63,9$. For each fixed $n$ the coefficient of $\theta^2/2$ in $S-R$ is therefore
$$[42(n)_2+63(n)_3+9(n)_4]/n^4-9
=3(3n^2-16n+10)/n^3,$$
positive for all $n\ge5$, negative for $n=4$. This limiting calculation alone is not asserted to supply one angle simultaneously for all $n$; that is done by the exact rational certificate above.

## Relationship to earlier work

* [Duchi, COLT 2012, Eqs. (2)–(3)](https://proceedings.mlr.press/v23/duchi12/duchi12.pdf) considers the scalar function obtained by taking the operator norm of each product. The outer norm in Eq. (2) is then immaterial because the averaged scalar is nonnegative. [Israel, Krahmer & Ward, Prop. 3.2 and Thm. 1.4](https://arxiv.org/pdf/1411.0333) establish the result through length three for all unitarily invariant norms. They note the new repeated-index patterns at length four.
* [De Sa, NeurIPS 2020, §2.3](https://proceedings.neurips.cc/paper_files/paper/2020/file/42299f06ee419aa5d9d07798b56779e2-Supplemental.pdf) already disproves this very inequality for $m=n=6$, using a permutation direct sum of the planar tight frame from [Recht–Ré](https://proceedings.mlr.press/v23/recht12.html). The direct-sum maximization device and the rank-one product formula are not new. His §2.1 five-factor result, the [Lai–Lim counterexample](https://proceedings.mlr.press/v119/lai20a.html), and [Zhong’s positive large-population regime](https://arxiv.org/html/2610.04874v1) concern norms *outside* the summation or the corresponding matrix-order inequality.
* [Liu, arXiv:2611.07649v1 (5 Nov 2026), Thm. 4.2, Prop. 6.2 and Cor. 6.3](https://arxiv.org/html/2611.07649v1) uses the norm-inside formulation, permutation direct sums and exact counting by word structure. His path-supported Gram matrix gives equal-weight projections and explicit six-factor violations for $n\ge11$; more generally, Thm. 6.1 covers every fixed $m\ge6$ for sufficiently large $n$. The present four-factor proof changes the local geometry to nonorthogonal planar rays with *unequal* weights and allows absent labels to have zero blocks. Liu’s Prop. 8.2 also treats positive-definite perturbation.
* The two literal earlier templates do not themselves give the present four-factor witness. For De Sa’s regular rays, put $c_0=\cos(\pi/n)$, $n\ge4$. Each all-distinct word has maximum $c_0^3$, and every word on at most two labels achieves at least this much by choosing adjacent rays. Of the six three-label patterns, three with one hold can achieve $c_0^2$ each; the two backtracking patterns $0102,0121$ can achieve $c_0^3$ each; and the triangle $0120$ can achieve $c_0^2\cos(2\pi/n)$ by using three consecutive rays. Their sum is at least $6c_0^3+2c_0^2(1-c_0)^2$, enough because the six patterns have equal multiplicity. For Liu’s path-Gram formula put $q=1/\rho\ge2$. At $m=4$ his Eq. (20) gives $n^4 R/S=(n)_1q^3+(n)_2(3q^2+3q+1)+(n)_3(3q+2)+(n)_4$. It is increasing in $q$ and already exceeds $n^4$ at $q=2$ by $2n^3+6n^2-n>0$. These last two comparisons are deductions from the published templates, not results attributed to their authors.
* [Georgiev et al., Problem 6.47](https://arxiv.org/html/2511.02864v3) pose a quantitative infimum in fixed dimension. The four-factor theorem here gives a strict upper bound below 1 in the stated dimensions, *not* the exact infimum or the low-dimensional cases they tested. Their account of the status of the general question does not supersede De Sa.
* The [repository and literature search scope](SEARCH.md) records the checks performed and the limits of a priority search. An [independent internal AI review](REVIEW.md) and both exact verification programs are included. No external peer review or machine-checked formal proof is represented.
