# Balanced closed components with any fixed small alphabet

Let P be a fixed set of t≥2 odd primes. Suppose that an exceptional autonomous component (EAC) of [Bożek's Goldbach factorization graph](https://arxiv.org/abs/1909.09900v1) at even N has precisely the t labels in P and another t labels larger than $B=\max P$. Then, for all sufficiently large N depending on P, the following is **necessary and sufficient** for this shape: there is a positive even integer h and an integer $W=hN+1$, with prime support exactly P, such that for every $p\in P$,
$$
 v_p=hp+1\mid W,\qquad R_p=\frac{W/v_p-1}{h}
    \text{ is prime and }>B.                                           \tag{1}
$$
The $R_p$ are exactly the outside labels. In particular every $hp+1$ is P-smooth (all of its prime divisors lie in P). Sufficiency in fact holds at every even N satisfying (1). The proof never assumes the two scales at the start: the outside labels *must* all be $>N\exp(-C_P(\log\log N)^2)$, and all out-of-alphabet factors must occur in matched pairs, one per small row. This is a parametrization, **not** a simultaneous primality theorem.

The possible h form an effectively finite set for any P: two distinct $p<q$ give two P-smooth positive integers $q(hp+1),p(hq+1)$ separated by $q-p$. Dividing by their odd gcd produces a rational S-unit equation in the fixed prime alphabet enlarged by the divisors of $q-p$; standard effective S-unit finiteness applies. For the cutoff 53, the final section gives an exact finite check using published complete data, not just this qualitative observation.

## For the cutoff 53

Write $P_0=\{3,5,7,11,13,19,23,47\}$ and $P_1=\{17,31,37\}$. At sufficiently large even centers, **every EAC having at least as many primes ≤53 as primes >53** must have
$$
 h=2,\qquad P=P_0\cup V,\quad V\subseteq P_1,\qquad
 W=2N+1,\quad \mathrm{rad}(W)=\prod_{p\in P}p.
$$
Its primes above 53 must be precisely the $|P|$ distinct primes $(W/(2p+1)-1)/2$. Conversely whenever such a W satisfies the divisibility, parity and primality conditions and these primes exceed 53, the component really exists. In particular the only possible balanced sizes are **16,18,20,22**. For every other size all sufficiently large EACs have strictly more primes above 53 than at or below 53. There is no new explicit cutoff in N, no assertion that all EACs have this balance, and no claim that the eight remaining families are empty, infinite, or supply a Goldbach exception.

## 1. The middle prime and the smooth anchor

Orient every edge from x to the prime factors of $U_x=N-x$. On an EAC all labels are coprime to N and all complements are odd composite; each label is a prime factor of someone else's row and is at most $(N-3)/3$. Let $r$ be the smallest outside prime, and $L=\log N$, $T=1+\log L$. In the proof, "smooth" means solely supported on P, and constants depend only on P. For these fixed bases [Matveev](https://doi.org/10.1070/IM2000v064n06ABEH000314) bounds a nonzero linear form with integer coefficients $\le L^{O_P(1)}$ in absolute value below by $\exp(-CT)$. Allowing one more positive rational of height ≤V gives $\exp(-CT\max(1,V))$. The same lower bounds apply to the absolute multiplicative defect of a product different from 1; conversely a multiplicative lower bound implies the linear one using $|e^u-1|\le3|u|$ when $|u|\le1$. The log-height of a rational is log max of its reduced numerator and denominator. See [the explicit rational formulation, Theorem 2.1](https://doi.org/10.1007/s12188-025-00293-9).

On the t+1 rows labelled by $P\cup\{r\}$, each outside prime occurs in at most one row since it would otherwise divide a positive difference smaller than r. Ignoring r and excluding the t−1 other outside primes leaves at least two rows supported on $P\cup\{r\}$. Their nonunit ratio differs from 1 by at most $r/(N-r)$. Matveev gives $\log r\gg L/T$ when $r\le\sqrt N$, and that estimate is automatic otherwise. Consequently $r$ is larger than every fixed power of L. If at least two of these t+1 rows are smooth, their nonunit ratio and the fixed-alphabet bound yield $r>N\exp(-CT)$; all outside labels are then already near-linear.

Otherwise exactly one of the t+1 rows is smooth and the other t each receive exactly one distinct outside prime $R_i$, exhausting the t possibilities. Write $U_{x_i}=d_i R_i^{a_i}$ for each assigned source, $d_i$ smooth, $a_i\ge1$. All exponents in this proof are ≤L before a bounded number of products/denominator clearings. For a smooth anchor $U_y$ define $\beta_i=(\log U_y-\log d_i)/a_i$. In any row $U_j=e\prod R_i^{m_i}$ using only an indicated subset of assigned primes, the normalized form
$$
 Z=\log e+\sum m_i\beta_i-\log U_y
   =\log(U_j/U_y)-\sum (m_i/a_i)\log(U_{x_i}/U_y)                     \tag{2}
$$
is on P alone. Its rational coefficients clear on multiplication by $\prod_i a_i\le L^t$, after which they are $\le C L^{t+2}$. Thus if $Z\ne0$, $|Z|>\exp(-CT)$, absorbing the log of the denominator. Also $\sum m_i\le L$.

### Anchor $y=r$

All assigned sources $x_i$ are small. For any outside label $j>r$, (2) is strictly negative: $U_j<U_r$ while every $U_{x_i}>U_r$. Its magnitude is at most $C L j/N$ by the mean-value theorem since all labels are <N/3. Hence each $j>r$ exceeds $N\exp(-CT)$. Such primes occur to the first power only, with cofactor $\le\exp(CT)$; the cofactor is smooth because $r\gg L^A$ for all fixed A.

There exists at least one $j>r$. Its row cannot target another outside prime $l>r$: using their distinct small parents $x_j,x_l$ and cofactors $v_j,v_l$, the three equations $v_j j=N-x_j$, $v_l l=N-x_l$, $N-j=w l$ imply
$$ N((v_j-1)v_l-wv_j)=-(x_jv_l+w v_jx_l). $$
Its right side is strictly negative and of magnitude $O(B\exp(CT))<N$. Thus $U_j=e r^b$ with e smooth, b≥0. The small source x of r has $U_x=d r^a$, $a\ge1$. Put $v=v_j$, $z=x_j$ and $\kappa=(v-1)/v$, noting $v\ge3$. Then
$$
 \log(U_j/(\kappa U_r))=\log(1+(r+z/(v-1))/U_r),\quad
 \log(U_x/U_r)=\log(1+(r-x)/U_r).
$$
The ratio of these two positive logs lies strictly between 1 and $(r+z/(v-1))/(r-x)<1+1/L$ for large N, by monotonicity of $\log(1+u)/u$ and $r\gg BL$. As a≤L this interval contains no $b/a$. Their linear combination with coefficients a,−b is therefore nonzero. It cancels $\log r$ and uses only P and $\kappa$, whose height is $O(T)$. Its magnitude is $O(Lr/N)$ and its cleared coefficients (already integers) have size $O(L^2)$. Separation implies $r>N\exp(-CT^2)$.

### Anchor $y\in P$

Here the source r is assigned an outside target $R_*$ different from itself; all other outside primes are assigned to small sources, including r itself. For every outside row j which lacks $R_*$, formula (2) uses only small sources. Its correction sum at the far right has absolute value at most $2BL/N$. The main term has magnitude at least $(j-y)/N$, which dominates the error since $j\ge r\gg BL$. Its magnitude is also $O(j/N+BL/N)$. Thus every such j exceeds $N\exp(-CT)$; in particular $R_*$ does, since it cannot divide its own row. Therefore $U_r=v R_*$ with $3\le v\le\exp(CT)$ smooth. For any $j>r$ whose row *does* contain $R_*$, write $U_j=w R_*$; the positive integer w is <v as $j>r$. The exact identity $j=(1-w/v)N+(w/v)r$ then implies $j\ge N/v$. Consequently all outside primes other than possibly r are near-linear with the same loss $\exp(CT)$.

If $U_{R_*}$ contains some $l>r$, then $l\ne R_*$ and l is directly assigned to a small source x with $v_l l=N-x$. Write $U_{R_*}=wl$. Substitution gives
$$ N((v-1)v_l-wv)=-(v_l r+wvx). $$
Since $wvx=o(N)$ and the right side is negative, $r\ge (N-o(N))/v_l$ already suffices. Otherwise $U_{R_*}=e r^b$ with e smooth. Let $U_x=d r^a$ be the small source of r. From $vU_{R_*}=(v-1)N+r$ and $\kappa=(v-1)/v$,
$$ \log(U_{R_*}/(\kappa U_y))=\log(1+(y+r/(v-1))/U_y)\gg r/(vN),
 \qquad |\log(U_x/U_y)|\le 2B/N. $$
The first magnitude is $O(r/N)$ too. Since $r/v\gg BL$, a times the first minus b times the second is strictly positive. It has magnitude $O(Lr/N)$ and again cancels $\log r$, so separation with $h(\kappa)=O(T)$ gives $r>N\exp(-CT^2)$.

## 2. The cofactor paths are forced to be parallel

In every case, all outside primes exceed $N\exp(-CT^2)>\sqrt N$. Any row using an outside prime targets precisely one such prime (to power 1) with smooth integer cofactor $v\in[3,\exp(CT^2)]$. From a small source $x_0=p\in P$ follow these unique outside targets repeatedly until there is no such edge. All resulting labels are reachable; conversely any outside vertex is reached on one such path, by strong connectivity and considering the last small vertex of any path to it.

In detail, after i steps $x_i=(A_i N+(-1)^i p)/V_i$, with $V_0=1,A_0=0$, $V_i=v_i V_{i-1}$ and $A_i=V_{i-1}-A_{i-1}$, where $v_i x_i=N-x_{i-1}$. Thus $0\le A_i<V_i$. No path can repeat a vertex: a first repeat at i<j≤t+1 would give $N$ times an integer equal up to sign to $p((-1)^i V_j-(-1)^j V_i)$, nonzero since $V_j>V_i$ and of size $O(B\exp(C(t+1)T^2))<N$. This also rules out any reachable outside-only cycle; no disconnected outside cycle can be part of the specified SCC. No disjointness of different paths has been assumed.

If some small $p_0$ has path length zero, then $U_{p_0}$ is smooth. Choose another small p≠$p_0$ (t≥2). Its terminal row at length i, possibly zero, is smooth and satisfies
$$ V_i U_{x_i}=D_i N+(-1)^{i+1}p,\qquad D_i=V_i-A_i\ge1. $$
The ratio to $D_i U_{p_0}$ differs from 1 by $(D_i p_0+(-1)^{i+1}p)/(D_i U_{p_0})$, nonzero since $p_0\nmid p$. Its absolute value is ≤$2B/(N-B)$, but all factors are smooth except $D_i$ of height $O(T^2)$. Matveev bounds its negative log by $O(T^3)=o(L)$. This contradiction rules out all zero-length paths, regardless of whether other paths merge. Therefore each of the t small rows directly targets an outside prime, these targets are distinct by the small-row difference bound, and all t outside primes are used directly. The integer identity for a direct cross-edge in section 1 again rules out *every* outside-to-outside edge (with $\exp(CT^2)$ cofactors still producing $o(N)$ right sides). The resulting paths are all parallel and of length one.

Write $U_p=v_pR_p$. Every $U_{R_p}$ is smooth. For two distinct small primes p,q,
$$
 \frac{v_p U_{R_p}}{v_q U_{R_q}}\frac{v_q-1}{v_p-1}-1
 =\frac{(v_q-1)p-(v_p-1)q}{(v_p-1)((v_q-1)N+q)} .
$$
If nonzero its magnitude is ≤$2B/N$, whereas the only nonsmooth base on the left is $(v_q-1)/(v_p-1)$ of height $O(T^2)$, with the smooth bases having coefficients $O(L)$. Matveev forbids this. Thus the numerator vanishes for *every* pair. The common positive ratio $(v_p-1)/p=h$ is an integer since distinct primes are coprime; h is even by oddness of the cofactors. Put $W=hN+1$. Direct rearrangement gives
$$ hR_p+1=W/v_p,\qquad U_{R_p}=p(W/v_p). $$
In particular W is P-smooth and every $v_p\mid W$. If some $q\in P$ did not divide W, none of the other paired rows could reach $q,R_q$: $q$ divides no $v_p$ and the only occurrence of q in a terminal row could be that of its own paired label. Strong connectivity and t≥2 exclude this. Thus $\mathrm{rad}(W)=\prod_{p\in P}p$, proving necessity of (1).

Conversely under (1), $U_p=v_p R_p$, $U_{R_p}=p W/v_p$, so the graph is factor-closed and all complements are composite. The targets $R_p$ are distinct because the $v_p$ are distinct. From each paired block $p,R_p$ one reaches all prime factors of $v_p$ and $W/v_p$, together precisely all of P, and every member of P reaches its own outside prime. Hence it is an EAC. This assertion is conditional only on the displayed *finite row conditions at W*, not on an unproved theorem about prime values.

## 3. Enumeration of the intercept multipliers for labels ≤53

For a putative P-smooth multiplier system with $p<q\in P$, $v_p=hp+1$, $v_q=hq+1$, the even center $n'=p+qv_p=q+pv_q$ has two 53-smooth complements at labels p,q. The [compact-core theorem and checker](EACCompactSmooth.md) enumerate all such centers from the complete [von Känel–Matschke S-unit table 1](https://bmatschke.github.io/solving-classical-diophantine-equations/), [Memoirs AMS 1419](https://doi.org/10.1090/memo/1419). The normalized gap is $q-p$ divided by an odd common factor g, and the larger normalized complement is c. Thus $h=(gc-q)/(pq)$. Filtering to positive even integers gives 2,534 rows with choice of pair and g and **1,488 distinct h** (maximum 1,861,842,140). For each h, directly peel $hp+1$ at each of the 15 candidate labels p and check all subsets of size ≥2 whose rows are supported wholly on that subset. The results are exactly $(56,\{3,13\})$ and the eight patterns $(2,P_0\cup V)$ in the statement.

For the first pattern, $W=56N+1\equiv1\pmod{16}$ and $W=3^a13^b$. As $13\equiv-3$ and $-1\notin\langle3\rangle\pmod{16}$, b is even and $a+b\equiv0\pmod4$, so W is a square. Both $W/169$ and $W/729$ are then squares. At large height $56R+1=z^2$ is impossible for prime $R>57$: $R\mid z-1$ or $R\mid z+1$, whereas $R=(z-1)(z+1)/56>z+1$ for $z>57$. This eliminates that family. If the number of small labels strictly exceeds the number outside, there can only be finitely many centers by [the large-majority theorem](EACLargeMajority.md) since at most 15 labels are small and $k\le30$. The remaining balanced size-two case is already covered at every height by [Bożek, Theorem 3.7](https://arxiv.org/abs/1909.09900v1). There are finitely many P under the cutoff, so the individual sufficiently-large thresholds can be maximized.

### Replay

Give `check_eac_balanced_patterns.py` the directory containing the original hash-checked `abc53.original.txt` and provide `check_eac_sunits.py` next to it (download instructions and provenance in the compact-core theorem). Run:

    python3 -O check_eac_balanced_patterns.py /path/to/table-directory

The checker reconstructs the multipliers directly from all normalized table rows and exhausts every subset of the eligible primes; it does not hard-code the list of candidate multipliers, does not assume the small rows alone are strongly connected, and does not filter them by coprimality to h. The fact that eight specific h=2 families remain is a restriction on the shape of any such component, not a claim that any large W gives simultaneous primes.
