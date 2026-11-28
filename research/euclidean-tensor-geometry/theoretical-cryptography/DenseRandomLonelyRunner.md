# A sharp loneliness threshold for dense random integer speeds

**Problem #081 (Lonely Runner): typical-case result, not the worst-case conjecture.**

Write $[N]=\{1,\ldots,N\}$ and let $\|x\|$ denote distance to the nearest integer. For a finite nonempty speed set $S$ put
\[
L(S)=\max_{t\in\mathbb R/\mathbb Z}\min_{v\in S}\|vt\|.
\]
We consider an exactly uniform $n$-element subset of $[2n]$, not independent speeds with replacement.

**Theorem.** If $S_n$ has this distribution, then
\[
\frac{nL(S_n)}{\log_2 n}\xrightarrow{\ \mathrm{probability}\ }\frac23.
\]
More precisely, for each fixed $0<c<2/3$ there is a fixed $\eta\in(0,1)$ such that, with probability tending to one, there is a reduced time $a/p$ with $p$ prime in
\[
 \left(\frac{2-\eta}{c}\frac{n}{\log_2 n},
              \frac{2}{c}\frac{n}{\log_2 n}\right)
\]
at which all $n$ distances exceed $c\log_2(n)/n$. For fixed $c>2/3$, with probability tending to one no real time brings all distances even to $c\log_2(n)/n$.

Czerwiński's [Random runners are very lonely](https://arxiv.org/abs/1102.4464), Theorem 1, lets the ambient speed bound grow with the number of speeds held fixed. The random-speed consequence of Beck and Everett's [Lonely Runner Relations](https://arxiv.org/abs/2609.06259v3), Corollary 6, is likewise formulated for fixed dimension; the growing-dimension example in their proof of Theorem 7 samples from an exponentially large speed range. That is not the proportional-size regime here. Tao's [Some remarks on the lonely runner conjecture](https://arxiv.org/abs/1701.02048) treats deterministic results including the setting of bounded speeds. Our conclusion concerns the uniform half-density model only, and gives no new deterministic lower bound for arbitrary speed sets.

## 1. The sampling law

Put $N=2n$, $\ell=\log_2 n$ and $\delta=c\ell/n$. Define the forbidden speed set at time $t$ by
\[
 B(t)=\{v\in[N]:\|vt\|<\delta\}.
\]
Thus $\min_{v\in S_n}\|vt\|\ge\delta$ exactly when $S_n$ avoids $B(t)$. For any $B\subseteq[N]$ of size $m\le n$,
\[
 P(B):=\Pr(S_n\cap B=\varnothing)
 =\frac{\binom{N-m}{n}}{\binom{N}{n}}
 =\prod_{j=0}^{m-1}\frac{n-j}{2n-j}
 \le 2^{-m}.
\]
For $m>n$ the probability is zero. Uniformly over $m=O(\log n)$ the same product gives
$P(B)=2^{-m}(1+O((\log n)^2/n))$:
after taking out $2^{-m}$, each factor is $1-j/(2n-j)$.

## 2. The lower threshold: prime triples

Fix $0<c<2/3$. Choose $\eta\in(0,1)$ so that $\lambda=2c/(2-\eta)<2/3$ and let $\mathcal P$ be the primes between $(2-\eta)/\delta$ and $2/\delta$. The prime number theorem in a fixed relative interval gives $|\mathcal P|=\Theta(n/\ell^2)$; all $p\in\mathcal P$ are of order $n/\ell$ and satisfy $N/p\le\lambda\ell$. For each such $p$, label the nonzero residue pairs $\{\pm j\}$ by $1\le j\le(p-1)/2$. At time $a/p$ with $a j\equiv 1\pmod p$,
\[
 B(t)=B_{p,j}:=\{v\in[N]:v\equiv 0,j,-j\pmod p\}.
\]
Indeed $1<\delta p<2$. Avoiding this triple of residue classes gives distance at least $2/p>\delta$ for every selected speed.

There are $T=\sum_{p\in\mathcal P}(p-1)/2=\Theta(n^2/\ell^3)$ tests. Set
$X=\sum_{p,j}{\boldsymbol 1}_{S_n\cap B_{p,j}=\varnothing}/P(B_{p,j})$. Then $\mathbb E X=T$. Each $B_{p,j}$ has size at most $3\lceil N/p\rceil$, so in the normalized second moment the contribution of an ordered pair of tests with forbidden sets $B,B'$ is
\[
 \frac{P(B\cup B')}{P(B)P(B')}
 = \bigl(1+O(\ell^2/n)\bigr)\,2^{|B\cap B'|}.
\]
The error is uniform, including on the diagonal. We bound the excess above 1 when averaging the powers of 2 over the ordered pairs.

* For $p\ne p'$, eventually $pp'>N$. The Chinese remainder theorem gives $|B\cap B'|\le9$. Over independent uniform choices of the two sign pairs at these fixed primes, a speed divisible by neither is included in the intersection with probability $4/((p-1)(p'-1))$. There are at most $N/p$ speeds divisible by $p$, and each is included with probability $2/(p'-1)$; the analogous bound applies to speeds divisible by $p'$. No speed is divisible by both. Hence the average intersection size is $O(N/(pp'))=O(\ell^2/n)$. For intersection sizes at most 9 this also bounds the average of $2^{|B\cap B'|}-1$, up to an absolute factor.
* At the same prime with distinct sign pairs the intersection contains only the multiples of $p$. Its power of 2 is at most $n^\lambda$. Since each prime contributes $\Theta(n/\ell)$ tests, these pairs form a proportion $O(\ell^2/n)$. Their contribution to the excess tends to zero.
* The diagonal contributes at most $O(n^{3\lambda}/T)=o(1)$.

Consequently $\mathbb E X^2/T^2=1+o(1)$ and $\Pr(X=0)=o(1)$ by the variance inequality. This proves the lower statement.

## 3. An elementary residue average

For $D>0$ and $b\ge 0$ set
\[
 F(D,b)=\int_0^1\#\{r\in\mathbb Z:|r+bu|<D\}\,du.
\]
We use the bound $F(D,b)\ge 3D/2$ provided **$D>1$ or $b>1$**. At $b=0$ the integrand is interpreted literally, with strict inequality.

If $D\ge2$, an open interval of length $2D$ contains at least $2D-1$ integers, which is enough. If $3/2\le D<2$, it contains at least three integers for almost every position of its center. For $b>0$ this suffices; for $b=0$ the center is precisely at an integer, and there are three. For $1<D<3/2$, write $f=D-1\in(0,1/2)$. As a function of $x=bu$, the count is 2 plus the indicator of $\|x\|<f$, up to boundary points of measure zero. The average of that indicator over a prefix $[0,s]$ of one period is at least $f/(1-f)$: it is 1 on the first piece, $f/s$ on the middle piece, and $1-(1-2f)/s$ on the last. The whole-period average is also at least $f/(1-f)$. Thus for $b>0$ the required bound follows from
\[
 2+\frac{f}{1-f}-\frac32(1+f)=
 \frac{1-2f+3f^2}{2(1-f)}>0 .
\]
For $b=0$ the count is again three.

It remains to consider $D\le1$ and $b>1$. Write $b=k+s$ with integer $k\ge1$ and $0\le s<1$. The count has integral $2D$ over every period, and the final prefix contributes at least $\min(D,s)$ from the integer 0 alone. For $s\ge D$,
\[
 2Dk+D-\frac32D(k+s)=D(k/2+1-3s/2)\ge0 .
\]
For $s<D$ the difference is $Dk/2+(1-3D/2)s$. This is nonnegative if $D\le 2/3$; otherwise it is at least $D/2+(1-3D/2)D=3D(1-D)/2$. Dividing by $b$ finishes the proof.

## 4. The upper threshold: every real time

Fix $c>2/3$, and take $n$ sufficiently large that $\delta<1/2$. Put $Q=\lfloor N/\sqrt{\log n}\rfloor$ with natural logarithm here. By Dirichlet approximation, at every time $t$ there is a reduced fraction $a/q$ with $1\le q\le Q$ such that $t=a/q+\epsilon$ and $|\epsilon|\le1/(qQ)$. This bound continues to hold if the initial fraction has to be reduced. Write
\[
 D=q\delta,\qquad b=Nq|\epsilon|.
\]
Both are $O(\sqrt{\log n})$, uniformly in $t$.

If $D\le1$ and $b\le1$, each of the first $J=\lceil N\delta\rceil-1$ positive multiples $jq$ belongs to $B(t)$. In fact $jq\le N$ since $J<N\delta$ and $q\delta\le1$, and
$|jq t-ja|\le j/N<\delta$. The forbidden witness depends only on $q$ and not on $a$ or $\epsilon$. Thus the probability of any successful time in this class is at most
\[
 Q2^{-J}\le n^{1-2c+o(1)}=o(1).
\]

Otherwise use signed integer residues. When $\epsilon\ge0$, membership of $v$ in $B(t)$ is equivalent to existence of an integer $r\equiv av\bmod q$ with $|r+bv/N|<D$. When $\epsilon<0$ replace the residue by its negative, so it is congruent to $-av\bmod q$. For each $r$ the permitted values of $v/N$ lie in an interval
$I_r=\{u\in[0,1]:|r+bu|<D\}$ and in a single residue class modulo $q$ in the variable $v$. Their count differs from $(N/q)|I_r|$ by at most 2, uniformly in open endpoints and in whether $v=0$ is omitted. If the same residue occurs in two of these layers their intervals are disjoint, because $2D<q$. Only $O(D+b+1)$ integer layers can be nonempty, even when $b=0$. Therefore
\[
 |B(t)|=\frac{N}{q}F(D,b)+O(D+b+1)
 \ge \frac32N\delta-O(\sqrt{\log n})
 =(3c-o(1))\ell,
\]
by the residue-average bound.

The forbidden set changes only at times solving $\|vt\|=\delta$ for some $v\in[N]$. There are at most $2\sum_{v=1}^N v$ such times in one period. Counting both the open complementary intervals and the singleton endpoints, there are $O(n^2)$ possible forbidden sets. For the sets from the large-layer case, the union bound and the sampling law give total success probability at most $n^{2-3c+o(1)}=o(1)$. Together the two cases prove the upper statement and complete the theorem.

## 5. Other constant sampling densities

The same estimates give a density-uniform form. Let $m=m(N)$ with $m/N$ bounded away from both 0 and 1, and let $S$ be uniform among the $m$-subsets of $[N]$. Define $w_N=1-m/N$ and $\ell_N=\log N/\log(1/w_N)$. Then
\[
 \frac{N L(S)}{\ell_N}\xrightarrow{\ \mathrm{probability}\ }\frac43.
\]
Indeed, for a forbidden set of size $j=O(\log N)$, the avoidance probability is
$\prod_{i=0}^{j-1}(N-m-i)/(N-i)=w_N^j(1+O(j^2/N))$, and for all $j$ it is at most $w_N^j$. Use $\delta=d\ell_N/N$. In the prime-triple argument $N/p\le d\ell_N/(2-\eta)$, and in the normalized moment replace $2^{|B\cap B'|}$ by $w_N^{-|B\cap B'|}$. The distinct-prime average uses the same size bound 9, with $w_N^{-9}=O(1)$. The diagonal and same-prime terms tend to zero when $d<4/3$ and $\eta$ is chosen so that $3d/(2-\eta)<2$. For $d>4/3$ the two union bounds become $N^{1-d+o(1)}$ and $N^{2-3d/2+o(1)}$. All errors are uniform when $m/N$ stays in a fixed compact subinterval of $(0,1)$.

In particular, if $m/N\to\rho\in(0,1)$, then $N L(S)/\log N$ tends in probability to $4/(3\log(1/(1-\rho)))$; at $N=2n,\ m=n$ this recovers the stated $2/3$ normalization.

## Reproduction and scope

Run `python3 verify_dense_random_lonely_runner.py` next to this note for exact rational checks of the scalar bound, residue-layer counts, the exceptional multiples, CRT intersections, and the fixed-size sampling probabilities on finite control instances. These controls are not used as a substitute for the asymptotic proof. The upper bound controls all real times; restricting both sides to the prime test times would give a weaker result. The theorem is about constant-density random speeds, not all speed sets, and is not a proof of the Lonely Runner Conjecture.
