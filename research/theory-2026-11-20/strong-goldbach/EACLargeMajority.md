# At least half the labels escape to stretched-exponential size

Let N be even and let C be an exceptional autonomous component of [Bożek's Goldbach factorization graph](https://arxiv.org/abs/1909.09900v1) (orient edges from p to the prime factors of N−p). Write $k=|C|\ge2$ and $L=\log N$. For any fixed k and any $0<\sigma<1/(k+1)$, at all sufficiently large N the component has **at least $\lceil k/2\rceil$ prime labels larger than $\exp(L^\sigma)$**. In particular, fixing any finite alphabet of primes and any t≥1, only finitely many centers have an EAC with at least t+1 labels in this alphabet and at most t outside. The outside labels are unbounded in the hypothesis; the proof gives an effective criterion, not an actual enumeration of those centers. The odd boundary t+1 small, t large is essential; two automatically smooth rows need not be available there.

There is a variable-size version: for every fixed $A>0$ and $0<\epsilon<1$, the conclusion of at least $\lceil k/2\rceil$ labels applies with threshold $(\log N)^A$ uniformly when
$$
 k\le(1-\epsilon)\frac{\log\log N}{\log\log\log N}.
$$
Neither result forces a Goldbach representation. All three-label exceptions with their two smaller labels bounded by 53 were already excluded outright in [the separate exact calculation](EACThreeLabels.md); no such finite computation is claimed here for five or more labels.

### A common quantitative criterion

We prove both statements for a threshold $B\ge3$. Let $J=\max(2,\log B,\log L)$. For a sufficiently large absolute constant $K$, it suffices that, along the sequence in question,
$$
 G=(KJ)^{k+1}(k+2)^{20}(1+\log L)^3=o(L).                            \tag{1}
$$
For fixed k and $B=\exp(L^\sigma)$ this follows from $(k+1)\sigma<1$. For $B=L^A$ one has $\log(KJ)=\log\log L+O_A(1)$; in the specified growing-k range $\log G\le(1-\epsilon+o(1))\log L$. Bounds below hold for sufficiently large L. Condition (1) implies $k\le L$, $\log B=o(L)$ and $B<N/2$.

All row labels are odd and coprime to N and every complement is an odd composite with factors in C. Every label occurs in at least one complement, hence is at most $(N-3)/3$. Set $U(x)=N-x$. Let s denote the number of labels ≤B and t=k−s the number above B. Suppose $s>t$. A large prime cannot divide complements of two small labels, since it would divide their distinct nonzero difference of size <B.

We use the following standard estimate, keeping uniformity in k: for a nonzero real linear combination $X=\sum_{\ell=1}^h n_\ell\log q_\ell$ of h≤k positive prime logarithms of height ≤J and integer coefficients $|n_\ell|\le L^{3(k+2)}$,
$$
 |X|>\exp(-F_h),\qquad F_h=(KJ)^h(k+2)^8(1+\log L).                  \tag{2}
$$
Drop zero coefficients. This follows from the positive-rational [Matveev theorem](https://doi.org/10.1070/IM2000v064n06ABEH000314), in [the explicit formulation of Theorem 2.1](https://doi.org/10.1007/s12188-025-00293-9): for h bases the constant is $1.4\,30^{h+3}h^{4.5}$ times $(1+\log\max(2,|n_\ell|))$ and the product of the log heights (replace a height by 1 if smaller). If $|X|\le1$, then $|e^X-1|\le 3|X|$; if $|X|>1$ the bound is automatic. Equally, for a nonunit product of powers of these primes times at most one extra rational of height H, the negative log of the multiplicative defect is $O(F_h\max(1,H))$, with an absolute implied constant: the factor 30 and the ratio of powers $(h+1)^{4.5}/h^{4.5}$ are bounded absolutely. These estimates remain valid with smaller numbers of present primes.

If two distinct small-row complements are supported on the s small primes, their ratio differs from 1 by at most $B/(N-B)$ and is not 1. Their exponents in absolute value are ≤L; Matveev gives $L-O(\log B)\ll F_s=o(L)$, impossible. Therefore there is at most one such clean small row. But at least $s-t\ge1$ exist. This forces $s=t+1$ and exactly one clean small row, labelled $p_0$. In particular t≥1 (since k≥2). Every other small row $p_i$ ($1\le i\le t$) has a distinct large prime $R_i$, thereby exhausting all t of them, exactly one per such row. Write
$$
 U_0=N-p_0,\qquad N-p_i=v_i R_i^{a_i},\qquad a_i\ge1,\quad
 N-R_j=w_j\prod_{i=1}^t R_i^{m_{ji}}.                                \tag{3}
$$
Here $U_0,v_i,w_j$ involve only the s small primes; $a_i\le L$ and $\sum_i m_{ji}\le L$. The cofactors are positive integers and may initially equal 1.

### A gap for each outside prime

For each i write $\beta_i=(\log U_0-\log v_i)/a_i$. Since $p_0,p_i\le B<N/2$,
$$
 |\log R_i-\beta_i|\le 2B/(Na_i).
$$
Define $T_j=\log w_j+\sum_i m_{ji}\beta_i-\log U_0$. With $d_*=\prod_i a_i\le L^t$, the quantity $d_*T_j$ is an integer linear combination of logs of the s small primes: exponents in each of $v_i,w_j,U_0$ are at most L, so after clearing denominators each coefficient is at most $d_*(2L+2L^2)\le L^{3(k+2)}$. Thus either $T_j=0$ or, by (2), $|T_j|>\exp(-2F_s)$, absorbing $\log d_*\le k\log L$. On the other hand,
$$
 |T_j-\log((N-R_j)/U_0)|\le2BL/N.                                    \tag{4}
$$
If $T_j=0$, the inequality $\log(U_0/(N-R_j))\ge(R_j-p_0)/U_0$ yields $R_j\le3BL$. If $T_j\ne0$, the error in (4) is $o(\exp(-2F_s))$ by (1). Since $R_j>p_0$ and $N-R_j\ge 2N/3$, the log in absolute value is at most $2R_j/N$. Thus
$$
 R_j\le3BL\quad\text{or}\quad R_j>N\exp(-3F_s).                      \tag{5}
$$

The first alternative is impossible: the row $N-p_j=v_jR_j^{a_j}$ and the anchor $U_0$ are two different complements, with a ratio differing from 1 by at most $B/(N-B)$. Only the s small primes and one additional base of log height ≤$\log(3BL)\le4J$ occur. Matveev bounds the negative log defect by $O(JF_s)=o(L)$ from (1), contrary to $L-O(\log B)$. Thus *all* outside primes in (3) exceed $N\exp(-3F_s)$. In particular each exceeds $\sqrt N$, so $a_i=1$ and $v_i<\exp(3F_s)$. Also $v_i\ge2$ since each small-row complement is composite and contains $R_i$ only once. In fact the odd cofactor is at least 3. Likewise any large row can have at most one outside prime factor counting multiplicity.

### Ruling out both types of large row

If $N-R_j=w_j R_i$, then $w_j<\exp(3F_s)$ and $R_l=(N-p_l)/v_l$ for l=i,j. Cross multiplication gives the integer identity
$$
 N((v_j-1)v_i-w_jv_j)=-(p_jv_i+w_jv_jp_i).
$$
The right side is strictly negative and of magnitude at most $2B\exp(6F_s)=o(N)$, impossible for a multiple of N. This step does not assume that the various cofactors are different.

Otherwise $N-R_j=w_j$ is supported entirely on small primes. Then
$$
 \frac{v_j w_j}{(v_j-1)U_0}-1
  =\frac{(v_j-1)p_0+p_j}{(v_j-1)U_0}\in(0,2B/(N-B)].
$$
The product uses the s small primes (aggregate exponents in $v_j w_j/U_0$, of size ≤2L) and one further base $v_j-1$, of height at most $3F_s$. Matveev bounds its negative log by $O(F_s^2)$. Crucially $2s=k+1$ in this sole remaining case, so $F_s^2\le G=o(L)$ by (1). The actual negative log is $L-O(\log B)$, again impossible. Hence the assumed small majority cannot occur.

### What was needed

This argument uses true prime factorizations, the integrality of the short right hand side after clearing cofactors, and a second application of the logarithm bound in the odd case. A fixed small alphabet supplies only finitely many possible s; if one fixes t and bounds s below by t+1, the resulting k's therefore form a finite set and the effective large-height conclusion applies to each. No effective threshold is evaluated here, no general upper bound for k is inferred, and cases with equally many small and large labels are deliberately left open.

This concerns the labels inside individual closed prime components, not the exceptional-set size in e.g. [Bhowmik–Grimmelt's 2026 paper](https://doi.org/10.1007/s10476-026-00191-z). No priority for the logarithm bound or the factorization graph is claimed.
