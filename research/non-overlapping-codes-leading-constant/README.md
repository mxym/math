# The leading constant for non-overlapping codes over a fixed alphabet

**Research draft, 18 November 2026.** Let $S(q,n)$ be the largest number of length-$n$ words on a $q$-letter alphabet such that no nonempty proper prefix of one word equals a suffix of another word **or of the same word**. The proposed result is that for every fixed integer $q\ge2$,
$$
\lim_{n\to\infty}\frac{nS(q,n)}{q^n}=\frac{q-1}{qe}.
$$
In particular, the binary constant is $1/(2e)$. This is an asymptotic statement about unrestricted optimum codes, not a formula for any finite length or for any one prescribed construction.

**中文摘要。** 对每个固定字母表大小 $q\ge2$，本文给出无重叠码最大规模的渐近候选证明：$S(q,n)\sim (q-1)q^n/(qen)$。上界适用于所有码；下界构造覆盖所有充分大的整数码长，而非仅一条子列。本稿经两轮独立的 AI 内部复核，未经外部同行评审，不主张已确认优先权。

**Status.** AI-assisted research and two independent internal AI reviews, not external peer review or formal verification. A literature search did not locate an earlier matching general upper bound; it does not certify priority. The published structural reduction and the known lower-bound constant are not claimed as new.

## What the result adds

- [Blackburn (2026), Introduction and Theorem 1](https://arxiv.org/html/2611.21913v1), asks for the best binary constant $c$ in $S(2,n)\le(c+o(1))2^n/n$. His upper bound is $5/(6e)$, improving Levenshtein's $1/e$. The known binary construction reaches $1/(2e)$ along a subsequence; see [Blackburn, Nasr Esfahani, Kreher and Stinson, Theorem 35 of the preprint](https://arxiv.org/pdf/2211.10309#page=15). Thus the binary *limsup* question already follows from the upper bound below and the existing lower result.
- The proposed upper argument uses the [Stanovnik–Moškon–Mraz convolution optimization, Proposition 10](https://doi.org/10.1007/s10623-023-01344-z) and Blackburn's first-positive-root estimate. Its further steps are to truncate *before* the final length, bound any contribution that takes at least one more step, and control the contribution that reaches the final length directly.
- [Chee, Kiah, Purkayastha and Wang, Theorem 4.2](https://arxiv.org/pdf/1209.0236#page=5), state a matching lower liminf for their particular construction. Their displayed choice of $n$ as a function of run length gives a subsequence; that step alone does not supply a bound for arbitrary $n$. Our lower bound does not depend on interpreting that statement: it uses a different, adjustable set of markers and counts its words for every sufficiently large $n$. We claim neither a new lower-bound constant nor an all-length theorem about their one-run construction. [Blackburn (2015), Construction 2 and Theorem 8](https://arxiv.org/pdf/1303.1026), already uses a family of prefix words to control rounding. [Wang and Wang](https://arxiv.org/abs/2108.06934) use generating functions to enumerate other specified families of non-overlapping codes.

## 1. The convolution for code size

By [Stanovnik–Moškon–Mraz, Proposition 10](https://doi.org/10.1007/s10623-023-01344-z), $S(q,n)$ is the maximum of $\sum_{i+j=n}\ell_i r_j$ over nonnegative integer arrays satisfying $\ell_1,r_1>0$, $\ell_1+r_1=q$, and
$$
\ell_t+r_t=\sum_{i+j=t}\ell_i r_j\qquad(2\le t<n).
$$
All indices in such sums are positive. The underlying decomposition is due to Fimmel, Michel, Pirot, Sereni and Strüngmann; see also [Blackburn (2026), §2](https://arxiv.org/html/2611.21913v1#S2). We invoke this structural theorem, rather than reprove it.

Write $a_i=\ell_i/q^i$, $b_i=r_i/q^i$ and $s_t=\sum_{i+j=t}a_i b_j$ for $2\le t\le n$. Thus $a_1+b_1=1$, $a_t+b_t=s_t$ for $2\le t<n$, and $S(q,n)/q^n$ is the maximum of $s_n$. Define $\gamma=\max(a_1,b_1)\le(q-1)/q$.

## 2. A bound for every coefficient

For $2\le h\le n$ let $A_h(x)=\sum_{i<h}a_ix^i$, $B_h(x)=\sum_{i<h}b_ix^i$. Put
$$
g_t^{(h)}=\sum_{\substack{i+j=t\\i,j<h}}a_i b_j,\qquad G_h(x)=\sum_{t\ge h}g_t^{(h)}x^t .
$$
Coefficient cancellation gives
$$
(1-A_h(x))(1-B_h(x))=1-x+G_h(x). \tag{1}
$$
Every coefficient of $G_h$ is nonnegative, and $g_h^{(h)}=s_h>0$. Indeed $s_2=a_1b_1>0$; for $h\ge3$ at least one term in $a_1b_{h-1}+b_1a_{h-1}$ is positive.

Let $\sigma_h$ be the first positive root of either factor on the left of (1). Each factor decreases from $1$ to a negative value. The other factor is nonnegative at the first root, so the product has nonpositive derivative there, also if the roots coincide. Thus $G_h(\sigma_h)=\sigma_h-1>0$ and $G'_h(\sigma_h)\le1$. Since $G_h$ has support in degrees at least $h$,
$$
h(\sigma_h-1)\le \sigma_hG'_h(\sigma_h)\le\sigma_h.
$$
In particular,
$$
1<\sigma_h\le\frac{h}{h-1},\qquad
s_h\le\max_{x>1}\frac{x-1}{x^h}
=\frac1h\left(1-\frac1h\right)^{h-1}\le\frac1h. \tag{2}
$$
The last step uses $s_h\sigma_h^h\le G_h(\sigma_h)$. This is the first-root argument of [Blackburn, §3.1 and Lemma 8](https://arxiv.org/html/2611.21913v1#S3.SS1), applied at *each* truncation. No truncated array has to be optimal.

## 3. The cost of reaching a later length

At $x=1$ both factors on the left of (1) are positive by (2). Since $B_h(1)\ge b_1$, for $2\le h<n$ we have
$$
a_h\le s_h\le G_h(1)=(1-A_h(1))(1-B_h(1))
\le\gamma(1-A_h(1)). \tag{3}
$$
Here $1-B_h(1)\le 1-b_1=a_1\le\gamma$. The same bound holds for $b_h$ with $B_h$ in place of $A_h$. Both also hold at $h=1$ if previous sums are zero.

Define $E_0=1$ and, for $1\le h<n$,
$$
E_h=\max\left\{\sum_{j=1}^h a_jE_{h-j},\ \sum_{j=1}^h b_jE_{h-j}\right\}.
$$
Then **$E_h\le\gamma$ at every positive lag**. Inductively the first sum is at most $a_h+\gamma A_h(1)\le\gamma$ by (3), and similarly for the second. The coefficient at lag zero remains $1$.

Fix $n/2<N<n$ and write $g_t=g_t^{(N)}$. For $N\le u<n$ put $\theta_u=a_u/s_u$. In the convolution at $t\le n$ both indices cannot be at least $N$. Either neither is, contributing $g_t$, or exactly one is, giving
$$
s_t=g_t+\sum_{N\le u<t}s_u\,[\theta_u b_{t-u}+(1-\theta_u)a_{t-u}]
\qquad(N\le t\le n). \tag{4}
$$
For these fixed splits, define $K_n=1$ and, backwards in $u$,
$$
K_u=\sum_{j=1}^{n-u}[\theta_u b_j+(1-\theta_u)a_j]K_{u+j}.
$$
Substitution in the finite triangular recursion (4) gives $s_n=\sum_{u=N}^n g_u K_u$: $K_u$ sums the weights of the increasing paths from $u$ to $n$. By backward induction, $K_u\le E_{n-u}$, since the convex combination of the two convolutions is at most their maximum. Therefore for $\sigma\ge1$,
$$
s_n\sigma^n\le g_n\sigma^n+
 \gamma\sigma^{n-N}\sum_{u=N}^{n-1}g_u\sigma^u. \tag{5}
$$
The direct contribution $g_n$ has taken zero additional steps and cannot be multiplied by $\gamma$.

## 4. Bounding the direct contribution

Take $k=\lceil n^{2/3}\rceil$, $N=n-k$ and $n$ sufficiently large that $N>n/2+1$. Let $\sigma=\sigma_N$ and $F=G_N(\sigma)=\sigma-1\le1/(N-1)\le3/n$. Write $U_i=a_i\sigma^i$, $V_i=b_i\sigma^i$ for $i<N$. For $2\le i<N$ both are at most $e/i$ by (2), since $\sigma^i\le(1+1/(N-1))^{N-1}\le e$.

Each contribution to $g_n\sigma^n$ has $i+j=n$, $i,j<N$, hence $i,j\ge k+1$. First sum over the subset $I$ of such $i$ with $i\le n/2$. Set $x_i=U_i V_{n-i}$, $X=\sum_{i\in I}x_i$ and $M=2e^2/[n(k+1)]$. We have $X\le F$, and $U_j V_{n-i}\le M$ for all $i,j\in I$. In particular $x_i^2\le M x_i$. If $i>j$, the crossed pair $(i,n-j)$ occurs in $G_N(\sigma)$ at degree $n+i-j>n$. This sends different ordered pairs to different ordered summands, even when degrees coincide. It follows that
$$
\sum_{\substack{i,j\in I\\ i>j}} x_i x_j
=\sum_{i>j}(U_iV_{n-j})(U_jV_{n-i})\le MF,\qquad
X^2\le MX+2MF\le3MF .
$$
For the other half, exchange $U$ and $V$ and use the smaller coordinate $n-i<n/2$; the strict inequality avoids counting the even midpoint twice. Adding the two estimates gives
$$
g_n\sigma^n\le2\sqrt{3MF}=O(1/(n\sqrt{k}))=O(n^{-4/3}). \tag{6}
$$

## 5. Upper bound

Equation (2) gives $\sigma^k\le\exp(k/(N-1))=1+O(n^{-1/3})$. Now (5), (6), and the nonnegativity of the tail give
$$
s_n\le\gamma(1+O(n^{-1/3}))\frac{\sigma-1}{\sigma^n}+O(n^{-4/3}).
$$
Maximizing the fraction as in (2), and using $\gamma\le(q-1)/q$, yields
$$
\frac{nS(q,n)}{q^n}\le\frac{q-1}{qe}+O(n^{-1/3}).
$$
The upper error is absolute, independent of the splits and $q$. A numerical version following the same estimates for $n\ge512$ is recorded in [internal review 1](reviews/review_1.md).

## 6. Matching construction for every sufficiently large length

Fix $q$ and set $k=\lfloor\log_q n\rfloor-2$, $t=\lfloor\sqrt{k}\rfloor$, $L=k+t+2$. For all sufficiently large $n$, $1\le t<k$. The $q^t$ words $0^k1v1$ with $|v|=t$ are mutually non-overlapping: a suffix of length at most $k$ ends in $1$, not $0$; a longer matching proper suffix would start with a second run of $k$ zeros, impossible since $t<k$. Choose any $m=\lfloor q^L/n\rfloor$ of these words for a marker family $P$. This is feasible since $q^{t-1}<q^L/n\le q^t$. Writing $p=m/q^L$, we have $np\to1$ along **all** integer lengths.

Keep a length-$n$ word precisely when it satisfies these conditions:
1. Its first $L$ symbols form a marker and its last symbol is nonzero.
2. No other full marker occurs.
3. No suffix of length $d$ with $k<d<L$ begins with $k$ zeros.

This is a non-overlapping code. A matching proper suffix of length at most $k$ is impossible by the last symbol; one of intermediate length is excluded by condition 3; one of length at least $L$ would start with a forbidden occurrence of a full marker.

Sample the letters independently and uniformly. Condition 1 has probability $p(1-1/q)$, since the two ends are disjoint. Condition on it. A second marker cannot start in positions $2,\ldots,L$. Starts $L+1,\ldots,n-L$ use only independent, unconditioned interior letters. For any fixed $j\ge1$ their $j$-fold intersection sum is
$$
\binom{n-2L-(j-1)(L-1)}{j}p^j\ \longrightarrow\ \frac1{j!}.
$$
Starts at mutual distances at least $L$ use disjoint blocks; any closer pair is impossible. Subtracting $(r-1)(L-1)$ from the $r$-th start in increasing order gives the binomial count. Here $L=O_q(\log n)$, and the binomial top is large for each fixed $j$. The odd and even Bonferroni bounds, first holding the truncation fixed as $n\to\infty$ and then sending it to infinity, squeeze the probability of no interior marker to $e^{-1}$.

The one remaining possible start, $n-L+1$, uses the conditioned final symbol and has conditional probability $p/(1-1/q)=O(1/n)$, since all markers end in $1$. Each suffix test in condition 3 inspects $k$ independent letters disjoint from the prefix block and the final symbol; its failure probability is $q^{-k}$. Their total failure probability is at most $Lq^{-k}=o(1)$ for fixed $q$. No independence from interior avoidance is needed for these two error estimates. The resulting code therefore has
$$
q^n p(1-1/q)(e^{-1}+o(1))
=\left(\frac{q-1}{qe}+o(1)\right)\frac{q^n}{n}
$$
words. Combining this with the upper bound proves the proposed limit.

The lower argument fixes $q$; it does **not** give a uniform rate of convergence for growing alphabets. Neither this result nor the upper bound identifies an exact finite-length optimum or decides whether a specified one-run construction is exactly optimal infinitely often.

## How to check the draft

- [Originating verification script](verify.py): 380 exact coefficient systems and five exhaustively generated toy codes. These are controls, not claimed optimal codes.
- [Internal review 1](reviews/review_1.md) and its [independent controls](reviews/controls_1.py): full binary derivation trees, small conflict-graph optima, and an independently enumerated marker avoidance automaton.
- [Internal review 2](reviews/review_2.md): a second check of the upper and lower arguments, with a separate set of exact finite controls.

Run the Python scripts with Python 3 and its standard library. All check conditions stay active with optimization enabled. No finite run proves an asymptotic theorem.

From this directory:

```sh
python -B -O verify.py
python -B -O reviews/controls_1.py
python -B -O reviews/controls_2.py
```
