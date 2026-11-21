# Four-label components cannot have two small primes and two unconstrained ones at large height

Let an exceptional autonomous component in [Bożek's Goldbach factorization graph](https://arxiv.org/abs/1909.09900v1) have exactly four distinct labels $p,q,R,S$, with $p,q<R<S$. Write $L=\log N$, where N is its even center. There exists an absolute constant c>0 such that, for all sufficiently large N,
$$
  (\log p)(\log q)\ \ge\ c\,\frac{L^{1/3}}{1+\log L}.                 \tag{1}
$$
The bound concerns the **two smallest** labels. In particular three of the four labels exceed $\exp(L^\sigma)$ for every fixed $0<\sigma<1/6$ and sufficiently large N. If one prime is fixed, the second smallest grows at least as $\exp(c_p L^{1/3}/(1+\log L))$. Consequently for *each* fixed pair of small labels, only finitely many centers are possible, allowing **two arbitrary and unbounded remaining primes**. The proof is effective in principle; no finite list of centers for the bounded-pair case, nor an exclusion of all four-label components, is asserted.

Use $U_x=N-x$ and arrows $x\to z$ if $z\mid U_x$. On an EAC the labels are odd and coprime to N, all complements are composite, and every label occurs in at least one complement, so $x\le(N-3)/3$. No prime divides its own row. The largest label S divides exactly one row: it occurs, and any two smaller labels have nonzero difference of absolute value <S. The prime R occurs in at most one of the two small rows, possibly also the S-row. Throughout, **smooth** will mean supported exclusively on $p,q$; 1 is permitted for a stripped cofactor.

### 1. Small-alphabet separation and the first gap

Put $B=\max(p,q)$ and $H=(\log p)(\log q)(1+\log L)$. We use positive-rational [Matveev](https://doi.org/10.1070/IM2000v064n06ABEH000314), e.g. [the explicit form, Thm. 2.1](https://doi.org/10.1007/s12188-025-00293-9). In particular, a nonzero linear form in $\log p,\log q$ with integer coefficients of magnitude at most $10L^3$ has absolute value $>\exp(-C H)$ with an absolute C. If a further rational logarithm of height ≤V occurs with an exponent of this size, the lower bound becomes $\exp(-C H\max(1,V))$. The same negative-log bounds apply to nonzero multiplicative defects. To go from a multiplicative lower bound to a linear-form lower bound use $|e^z-1|\le3|z|$ when $|z|\le1$. Omit trivial bases/zero coefficients. Constants C below are absolute and may increase.

At least two among $U_p,U_q,U_R$ omit S and hence use only the three bases $p,q,R$. For any such distinct pair, its nonzero multiplicative ratio minus 1 has absolute value ≤$R/(N-R)$. If $R\le\sqrt N$, Matveev therefore gives $\log R\gg L/H$. If $R>\sqrt N$ the same estimate is immediate. Now suppose for contradiction that $H\le c_0 L^{1/3}$, with a sufficiently small absolute $c_0$ to be chosen in the final comparison. Then
$$
 \log R\gg L/H,\qquad R\gg B L^2\exp(C H)                             \tag{2}
$$
for every fixed absolute C and sufficiently large N: $L/H$ dominates $H+\log B+\log L$. This initial estimate is independent of the allocation of the other factors.

We next show $S>N\exp(-C H)$. If at least two of the four complements are smooth, their nonunit ratio has multiplicative defect at most $S/(N-S)$ and two-base separation gives the result. Otherwise exactly one is smooth: S occupies precisely one row, R no more than two, so at least one is smooth and the three remaining rows must be distinct. R divides some small row $U_x$ and the large row $U_S$, whereas the S-containing row is different. Write $U_x=d R^a$, $U_S=e R^b$ with a,b≥1, d,e smooth. The unique smooth row $U_y$ has label y either the other small prime or R. Then
$$ Z=a\log(U_S/U_y)-b\log(U_x/U_y) $$
is a linear form on the two small primes with coefficients ≤$4L^2$. If y=R, the two ratios are respectively <1 and >1, so Z<0. If y is small, $|\log(U_x/U_y)|\le2B/N$ and $-\log(U_S/U_y)\ge(S-y)/N$; by (2) this dominates even $2LB/N$, so Z<0 again. As $|Z|\le 4L S/N$ by the mean-value theorem and $S<N/3$, separation proves the claimed lower bound for S.

### 2. Forcing the other outside prime to be near-linear

The unique row $U_z$ involving S has the form $U_z=vS$, since $S>\sqrt N$. Here $3\le v<\exp(CH)$ (compositeness and oddness), and v is smooth because $v<R$ by (2). Put $\kappa=(v-1)/v$. The S-row has form $U_S=eR^b$ with e smooth and b≥0. The following argument proves
$$
                   R>N\exp(-CH^2).                                    \tag{3}
$$

If z is a small label, let x be the other small label. Then $U_R$ is smooth and $U_x=dR^a$, d smooth. If $a=0$, the smooth pair $U_R,U_x$ already gives $R>N\exp(-CH)$ by its small relative difference. Otherwise a≥1, and $vU_S=(v-1)N+z$. Consequently
$$
 \log(U_S/(\kappa U_R))=\log(1+(R+z/(v-1))/U_R),\quad
 \log(U_x/U_R)=\log(1+(R-x)/U_R).
$$
The ratio of the first log to the second lies strictly between 1 and $(R+z/(v-1))/(R-x)<1+1/L$ by (2). The first strict upper bound uses that $\log(1+t)/t$ is strictly decreasing for t>0. Since $1\le a\le L$, no rational $b/a$ lies in this open interval. Thus $Z'=a\log(U_S/(\kappa U_R))-b\log(U_x/U_R)\ne0$. The $\log R$ terms cancel; only p,q and $\kappa$ remain, with height $h(\kappa)=\log v\le CH$ and exponents of magnitude ≤$4L^2$. Both displayed logs are $O(R/N)$, so $|Z'|\ll LR/N$. Separation with the extra rational logarithm proves (3).

If z=R, then at most one of the small rows can contain R, and neither contains S. Both being smooth is impossible for large N here, since their relative difference is ≤$B/(N-B)$ and $\log B+CH=o(L)$. Let $U_y$ be the smooth row and $U_x=dR^a$ the other (a≥1). Here $vU_S=(v-1)N+R$, so
$$
 \log(U_S/(\kappa U_y))=\log(1+(y+R/(v-1))/U_y)
       \gg R/(vN),\qquad |\log(U_x/U_y)|\le 2B/N.
$$
Indeed $U_y>2N/3$, the log argument is bounded, and $\log(1+t)\gg t$ on that bounded interval. As $R/v\gg BL$ by (2), the nonzero form $a\log(U_S/(\kappa U_y))-b\log(U_x/U_y)$ is positive. It has magnitude $O(LR/N)$ and again uses only p,q and $\kappa$. This proves (3) in the remaining case.

### 3. Exhaustion of the two possible chain patterns

Both R,S now exceed $Ne^{-CH^2}>\sqrt N$. In any row containing a large prime its multiplicity is one and its cofactor is a smooth integer in $[3,\exp(CH^2)]$. No row can target both large primes. Each large vertex is reachable from a small one by strong connectivity; on a shortest such path, after the last small vertex only R,S occur. Thus if both large vertices are direct targets of small rows, the small rows target distinct primes. Otherwise exactly one is directly targeted and there is a directed two-step path $x\to R_1\to R_2$ from a small x to the other large prime. Here and below $R_1,R_2$ may be either ordering of R,S.

**A two-step path.** The other small label y targets no large prime, since a large prime cannot divide the difference between two small labels. Let
$$ U_x=v_1R_1,\quad U_{R_1}=v_2R_2,\quad D=v_1v_2-v_1+1. $$
Then $U_{R_2}=(DN-x)/(v_1v_2)$. It cannot equal $wR_1$: that would give $N(D-wv_2)=x(1-wv_2)$, a nonzero multiple of N of absolute value <N. Here and below, products of finitely many such cofactors and small labels are $\exp(O(H^2)+O(\log B))=o(N)$. Self-divisibility is excluded, so $U_{R_2}$ and $U_y$ are both smooth. Their comparison gives
$$ \frac{v_1v_2 U_{R_2}}{D U_y}-1 = \frac{Dy-x}{D U_y}. $$
It is nonzero because y is a distinct prime from x and D is an integer. Its magnitude is at most $2B/(N-B)$, but the product uses only p,q and the additional integer D with $\log D=O(H^2)$: the exponents of p,q in the smooth part are $O(L)$ (each cofactor or complement is <N). Matveev bounds the negative log by $CH^3$.

**Two one-step paths.** Write $U_p=v_pR_1, U_q=v_qR_2$. If $U_{R_1}=w R_2$, substitution gives $N((v_p-1)v_q-wv_p)=-(p v_q+wq v_p)$, a strictly negative integer of absolute value <N. The reverse edge is equally impossible. Both terminal complements are therefore smooth. The ratio
$$
 \frac{v_p U_{R_1}}{v_q U_{R_2}}\frac{v_q-1}{v_p-1}-1
 =\frac{(v_q-1)p-(v_p-1)q}{(v_p-1)((v_q-1)N+q)}
$$
has magnitude ≤$2B/N$. If nonzero, its negative log is at most $CH^3$ since the additional rational $(v_q-1)/(v_p-1)$ has height $O(H^2)$.

In both comparisons a nonzero defect gives $L-O(\log B)\le CH^3$, contrary to $H\le c_0 L^{1/3}$ once $c_0>0$ is small enough, independently of the labels. It remains to eliminate exactly zero in the two-one-step case; this case must not be discarded by a generic nonvanishing assertion.

### 4. The unique coincident-intercept case

The zero numerator forces $v_p=1+hp$, $v_q=1+hq$ for an integer $h\ge1$ (the primes p,q are distinct). Because $v_p$ is smooth and $p\nmid hp+1$, we have $hp+1=q^a$; similarly $hq+1=p^b$ for a,b≥1. Hence $q^{a+1}-q=p^{b+1}-p$. The even center $p+q^{a+1}=q+p^{b+1}$ has the two-label closed component {p,q}, with both complements prime powers of exponent at least two. [Bożek, Theorem 3.7, using Scott](https://arxiv.org/abs/1909.09900v1), proves that the only such center is 2200 with labels 3,13. Relabeling, $p=3,q=13$, $v_p=169$, $v_q=729$, $h=56$.

Set $W=56N+1$. The exact terminal formulas give $v_p U_{R_1}=pW$, $v_q U_{R_2}=qW$. The left sides are smooth, so W involves only 3 and 13; write $W=3^i13^j$. Since $N$ is even, $W\equiv1\pmod{16}$. Now $13\equiv-3\pmod{16}$ and $\langle3\rangle=\{1,3,9,11\}$ omits −1. Therefore j is even, $i+j\equiv0\pmod4$, and i is also even. Further, $56R_1+1=W/169$ and $56R_2+1=W/729$, by the direct row formulas. These integers are squares (the denominators are square divisors of W). If $56R_1+1=z^2$ then $R_1$ divides $z-1$ or $z+1$, so $R_1\le z+1$. But $R_1=(z-1)(z+1)/56>z+1$ for $z>57$, as holds for large N by (3). Thus the coincident case too is impossible. This closes the proof of (1), not the four-label existence problem outside its stated size regime.

The known size-two Diophantine theorem is used as a cited input; the resulting growth restriction concerns four labels only. It does not follow from, or imply, the broad analytic exceptional-set bounds in [Althöfer–Chen–Perelli–Pintz, November 2026](https://arxiv.org/abs/2611.09386v1).
