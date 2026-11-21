# A moving threshold for almost half the labels of any closed reflected-prime set

Fix $0<\delta<3$ and $\eta>0$. Put $L=\log N$ and $B=L^{3-\delta}$. For all sufficiently large even N, let C consist of k≥2 distinct primes coprime to N, at most N−2, and suppose all prime divisors of every $N-p$, $p\in C$, belong to C. Writing $s=\#\{p\in C:p\le B\}$ and $t=k-s$, one has
$$
 s\le(1+\eta)t+1,\qquad t\ge(k-1)/(2+\eta).
$$
In particular for fixed k one may choose η sufficiently small to get $t\ge\lfloor k/2\rfloor$. The threshold for N is not specified numerically and may depend on both parameters. There is no claim that half the primes below N are large or that a Goldbach pair exists. This is a label-distribution strengthening of [the cubic-log maximum bound](EACMovingCutoff.md).

**Proof.** Distinct small labels x cannot use the same prime $q>B$ in their complements: q would divide a nonzero difference of absolute value <B. Thus at least $s-t$ small rows use only the s small primes. If $s>(1+\eta)t+1$, use all such rows, say n of them. Then $n\ge s-t\ge2$ and $s/n\le1+1/\eta$ (also when t=0).

Mark one of these n rows for each of the s small primes q, maximizing its exponent, with a dummy mark in an arbitrary row when q never appears. Let $v_i$ be the remaining cofactor on row i after its marked prime powers are removed; $E=\sum_i\log v_i$. For $r(q,a)=\#\{i:q^a\mid N-p_i\}$ one has exactly $E=\sum_{q,a}(r(q,a)-1)_+\log q$. Pairs of these prime rows have differences of size <B. Consequently $\sum_{q,a}\binom{r(q,a)}2\log q\le\binom n2\log B$, and all shared prime powers are <B. Cauchy as in equation (4) of the linked proof bounds the shared residual contribution from a prime set T by $n\sqrt{|T|}\log B$. Set $Q=(B^2/\log B)^{1/3}$. Applying $\pi(Q)\ll Q/\log Q$ to the primes ≤Q, their contribution divided by n is $O(\sqrt{Q\log B})$. The primes >Q have only their first power possibly shared. For $q>B/2$ no two odd rows can share q; for $Q<q\le B/2$, Brun–Titchmarsh on primes ≤B in the reduced class N mod q gives $r(q,1)\ll(B/Q)/\log(B/Q)$ as in the linked proof. There are at most s such primes. Hence
$$ E/n\ll (1+s/n)(B\log B)^{1/3}\ll_\eta(B\log B)^{1/3}. $$
No equality of the number of marks and rows is used.

At least two distinct rows have simultaneously at most $8s/n$ marks and residual log at most $8E/n$: each strict failure removes at most n/8 rows, and when E=0 no residual test fails. At least $3n/4>1$ rows remain even for n=2. Their full row ratio $U_i/U_j$ differs from 1 by at most $B/(N-B)$, and not by zero. Express the ratio using the two lists of marked powers and the single additional rational $v_i/v_j$. There are at most $2\lfloor8(1+1/\eta)\rfloor+1$ bases, every marked prime has height at most log B, and the residual-ratio height is at most $8E/n$. The integer exponents have absolute value at most $2L$. Drop zero exponents and the base 1. [Matveev's rational multiplicative bound](https://doi.org/10.1070/IM2000v064n06ABEH000314) in this fixed dimension gives
$$
 L\ll_\eta (1+E/n)(\log B)^{O_\eta(1)}\log L.
$$
Indeed $\log((N-B)/B)\gg L$. The displayed residual bound makes the right-hand side $O_{\eta,\delta}(L^{1-\delta/3}(\log L)^{O_\eta(1)})=o(L)$, a contradiction. This applies to actual Bożek EACs as a subset of the closed sets specified, not as an exclusion of components with many large labels.
