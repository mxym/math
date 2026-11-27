# Perfect threshold sharing with one-bit overhead from flat imperfect sources

## 1. Model and theorem

Fix $2\le t\le n$, an integer $b\ge1$, and write $q=2^b$, $V=\mathbb{F}_q$, $h=t-1$. The secret space is $V$. We use the one-draw model of Aggarwal v2 Definition 2.1: a deterministic sharing map takes a secret $m$ and a dealer key $k$ from a finite set $\mathcal K$. The dealer receives one sample from an unknown member of a fixed class of distributions on $\mathcal K$, with no auxiliary randomness. For each fixed source in the class, every coalition of fewer than $t$ parties has identical marginal distributions for every pair of secrets. This is perfect privacy. Any $t$ or more parties reconstruct for every secret and every key in $\mathcal K$.

Define the inactive-label family and signed integers
$$
\mathcal D=\{D\subseteq[n]:|D|\le h\},\qquad
c_D=(-1)^{h-|D|}\binom{n-|D|-1}{h-|D|},\qquad
C=\sum_{D\in\mathcal D}|c_D|.
\tag{1}
$$
Let $N=q^h$, $G_+=(C+1)/2$ and $G_-=(C-1)/2$. Provided
$$
q>2^{t-1}\binom{n-1}{t-1},
\tag{2}
$$
there is a perfectly correct, perfectly private $t$-out-of-$n$ scheme with share alphabet $\{0,1\}\times V$ and key set of size $CN$. For every $T\subseteq V^h$ the corresponding source is uniform on a support of size $G_-N+|T|$. Thus the least min-entropy in this family is $(t-1)b+\log_2 G_-$, within $\log_2 3$ of $\log_2|\mathcal K|$. The optimum worst-case one-bit deterministic extraction error is exactly $1/(2C)$; this is also a lower bound when extracting any positive number of bits (no equality claim for multiple bits). A shortest fixed-width binary encoding of a dealer key uses
$$
\left\lceil\log_2|\mathcal K|\right\rceil=(t-1)b+\lceil\log_2 C\rceil.
\tag{3}
$$
The point of the theorem is the direct $(b+1)$-bit shares and the explicit quantitative parameters. Qualitative existence for all thresholds follows already from two earlier papers, as explained in Sec. 6.

All binomial coefficients and counts are integers, not operations in $V$. The sufficient field condition is not asserted necessary. For $t=2$ the earlier sharper condition $q>n$ is sufficient, as checked in Sec. 6.

## 2. Exact tag projections and flat sources

For every $K\subseteq[n]$ of size at most $h$ we have the upper-set identity
$$
\sum_{\substack{D\in\mathcal D\\D\supseteq K}}c_D=1.
\tag{4}
$$
One way to verify this is to define $c_D=\sum_{D\subseteq A\in\mathcal D}(-1)^{|A|-|D|}$. In the sum over $D\supseteq K$, a fixed $A\supseteq K$ has contribution $\sum_{K\subseteq D\subseteq A}(-1)^{|A|-|D|}$, equal to one if $A=K$ and zero otherwise. Grouping by $|A|-|D|$ gives $\sum_{j=0}^{h-|D|}(-1)^j\binom{n-|D|}{j}$, which equals (1) by Pascal cancellation (upper index $h-|D|<n-|D|$).

More precisely, for **every** unauthorized coalition $J\subseteq[n]$, $|J|\le h$, and every observed inactive tag set $R\subseteq J$, the signed projection is
$$
\sum_{\substack{D\in\mathcal D\\D\cap J=R}}c_D
=\sum_{B\subseteq J\setminus R}(-1)^{|B|}
 \sum_{\substack{D\in\mathcal D\\D\supseteq R\cup B}}c_D
=\mathbf1[R=J].
\tag{5}
$$
The first equality is inclusion–exclusion for the forbidden inactive tags in $J\setminus R$, and every inner sum is covered by (4).

To make nonnegative key labels, at each index $u\in V^h$ include $|c_D|$ **distinct copies** of label $D$, say $(u,D,a)$ for $1\le a\le|c_D|$. Separate these labels at that index into $\mathcal K_+(u)$ and $\mathcal K_-(u)$ according to the sign of $c_D$. They are disjoint. By (4) at $K=\varnothing$, their sizes differ by one, with the plus group larger. There are labels of both signs: sets of size $h$ have coefficient $1$, and sets of size $h-1$ have coefficient $-(n-h)<0$. This also shows $C\ge3$ and $C$ is odd. The group sizes are precisely $G_\pm$. For each $T\subseteq V^h$ let
$$
\Omega_T=\left(\bigcup_{u\in T}\mathcal K_+(u)\right)
 \cup\left(\bigcup_{u\notin T}\mathcal K_-(u)\right),\qquad
P_T=\operatorname{Unif}(\Omega_T).
\tag{6}
$$
This defines the class explicitly. Its support sizes and min-entropies follow by counting. Moreover $C/G_-\le3$ because $C\ge3$. There are $q^h$ pad indices, each with $C$ labels. A key encodes the $h$ field coefficients with $hb$ bits and the label with $\lceil\log_2 C\rceil$ bits; if the domain has to be a bit cube, unused codewords have zero source probability and can be assigned any valid key's sharing rule. No bit budget in (3) is a claim about sampling $P_T$ from independent fair bits or learning the unknown $T$.

## 3. Sharing and exact decoding for all tag patterns

Condition (2) implies $q\ge n$: since $1\le h\le n-1$, the binomial coefficient $\binom{n-1}{h}\ge(n-1)/h$ (count incidences of a designated element, or use $\binom{n-1}{h}=\frac{n-1}{h}\binom{n-2}{h-1}$), and $2^h\ge h$. Fix distinct public $x_j\in V$, $j\in[n]$. An index $u=(u_0,\ldots,u_{h-1})$ specifies the polynomial $p_u(X)=\sum_{a=0}^{h-1} u_a X^a$ of degree at most $t-2$. Write $p_j(u)=p_u(x_j)$. For a key $(u,D,a)$ give party $j$ the share
$$
(\mathbf1[j\in D],\,z_j),\qquad
z_j=p_j(u)+\mathbf1[j\notin D]\,\gamma_j m.
\tag{7}
$$
The public coefficients $\gamma_j\in V$ are chosen once, separately from secrets, pad indices and source choices. The duplicate-label index $a$ does not change the shares. There is one tag bit and one $b$-bit symbol for any active or inactive label.

For a set $A$ of exactly $t$ authorized parties define the nonzero Lagrange coefficients
$$
w_{A,j}=\left(\prod_{\ell\in A\setminus\{j\}}(x_j-x_\ell)\right)^{-1}
\quad(j\in A).
$$
They extract the coefficient of $X^{t-1}$ from the degree-$<t$ interpolating polynomial: this follows by comparing the highest-degree term of each Lagrange basis polynomial. In particular $\sum_{j\in A}w_{A,j}p_j(u)=0$. The tags reveal $B=A\setminus D\ne\varnothing$ because $|D|\le t-1$. Require
$$
\sum_{j\in B} w_{A,j}\gamma_j\ne0\qquad
\text{for every }A\in\binom{[n]}t,\ \varnothing\ne B\subseteq A.
\tag{8}
$$
Choose $\gamma_1,\ldots,\gamma_n$ in order. At step $j$, consider all the constraints whose largest active index $\max B$ equals $j$. Once earlier coordinates are chosen, each such constraint forbids exactly one element of $V$, since its coefficient of $\gamma_j$ is nonzero. There are at most $\binom{n-1}{t-1}$ choices of $A$ containing $j$ and at most $2^{t-1}$ choices of $B$ containing $j$ per $A$. By (2) some field element remains at every step. Future constraints depend on future coordinates only when their active sets include them, so each constraint is satisfied when its last active coordinate is assigned. This gives a single simultaneous public choice, not a per-key or per-coalition choice of coefficients.

Now the reconstruction map on an actual view is
$$
m=\frac{\sum_{j\in A}w_{A,j}z_j}
        {\sum_{j\in B}w_{A,j}\gamma_j}.
\tag{9}
$$
If more than $t$ parties are given, use a prescribed $t$ of them. The formula works for all keys in the domain, not just a specific source support. Decoders may give arbitrary outputs on inconsistent input tuples; their behavior there is not part of the claim.

## 4. Perfect privacy for every source and sharp extraction error

Fix $T$, an unauthorized coalition $J$ with $|J|\le h$, and a tag pattern $R\subseteq J$. For each index $u$, let $g_\pm(J,R)$ count the keys in the plus/minus group at that index whose inactive set intersects $J$ in exactly $R$. These are nonnegative integers independent of $u$. Equation (5) says $g_+(J,R)-g_-(J,R)=\mathbf1[R=J]$.

If $R\ne J$, both groups have the same count $g(J,R)$, so that count occurs at **every** index $u$, regardless of $T$. For all such keys the coalition sees the value vector
$$
(p_j(u))_{j\in J} + m\,(\mathbf1[j\in J\setminus R]\gamma_j)_{j\in J}.
$$
The map $u\mapsto(p_j(u))_{j\in J}$ onto $V^J$ has exactly $q^{h-|J|}$ preimages of each value. Indeed, for nonempty $J$ its evaluation matrix has an invertible $|J|\times|J|$ Vandermonde block using the first $|J|$ polynomial coefficients; fixing the rest yields a unique solution. The result is also true for the empty set. Consequently for $R\ne J$ each value vector occurs exactly $g(J,R)q^{h-|J|}$ times in $\Omega_T$, independent of $m$. If $R=J$, all these shares are inactive and the values are just the unshifted $(p_j(u))_{j\in J}$; contributions from each $u$ can depend on $T$ but not on $m$. Dividing counts by $|\Omega_T|$ proves identical joint marginal laws for every $m$, for all unauthorized sizes and tag patterns. No assumption of a uniform source over the whole key set is used.

Let $f:\mathcal K\to\{0,1\}$ be any deterministic extractor and set $v(k)=(-1)^{f(k)}$. For each index $u$, the difference
$$
a_u=\sum_{k\in\mathcal K_+(u)}v(k)-\sum_{k\in\mathcal K_-(u)}v(k)
$$
is odd because it is a sum of $C$ odd integers with signs. Thus $|a_u|\ge1$. Choose $T=\{u:a_u>0\}$ and write $H_T=\sum_{k\in\Omega_T}v(k)$. Then
$$
H_T-H_{T^c}=\sum_u|a_u|\ge N,\qquad
|\Omega_T|+|\Omega_{T^c}|=CN.
$$
The triangle inequality implies at least one of the normalized magnitudes $|H_T|/|\Omega_T|$, $|H_{T^c}|/|\Omega_{T^c}|$ is at least $1/C$. On a flat source half this magnitude is the total variation distance from a fair bit. For an extractor with $\ell\ge1$ bits, projecting to the first bit is contractive for total variation and gives the same lower bound.

For one bit the bound is attained. Since $q$ is even and $h\ge1$, divide the index set into two equal-size parts and output the part bit, ignoring the other labels. Each part contributes between $G_-N/2$ and $G_+N/2$ keys under any $P_T$. Thus the output probability is between $G_-/C$ and $G_+/C$, giving error at most $1/(2C)$. Equality holds when $T$ is exactly one of the two parts. This parity/minimax argument extends the same argument of Aggarwal for the two endpoint thresholds.

## 5. Two limited optimality statements

**Integer share width, and general dealer randomness constraints.** Let any deterministic $t$-threshold sharing map, $t\ge2$, be perfectly correct and private for a class of dealer distributions, with $q=2^b$ equipossible secret values and no other randomness. Fix one admissible dealer distribution and analyze an independent uniform secret $M$. If $i\notin J$ and $|J|=t-1$, the secret remains uniform conditional on every positive-probability view of $J$. Correctness makes each pair (that view, one fixed value of share $i$) compatible with at most one secret; hence every conditional atom of the share of $i$ is at most $1/q$. Averaging over views bounds each marginal atom by $1/q$; singleton privacy identifies this marginal law with the fixed-message law. This is the single-share min-entropy observation in Aggarwal's Sec. 1.2.

Suppose party $i$ uses an alphabet of size $L_i$. Necessarily $L_i\ge q$. Fix an alphabet subset of size $\lfloor L_i/2\rfloor$ and a secret value $m_0$. The bit testing membership of the $i$-th share of $m_0$ in that subset is a deterministic function of the dealer key alone. Its probability is between $\max(0,1-\lceil L_i/2\rceil/q)$ and $\min(1,\lfloor L_i/2\rfloor/q)$ on every allowed source. Thus its worst-case distance from a fair bit is at most
$$
\min\left\{\frac12,\ \frac{\lceil(L_i-q)/2\rceil}{q}\right\}.
$$
If the optimal deterministic one-bit error of the class is $e>0$, this yields $L_i\ge q+2\lceil qe\rceil-1$ for **each** party. In particular it gives $q+2\lceil q/(2C)\rceil-1$ for (6), and $b+1$ is the optimal integer maximum share width for this class. The effective lower bound is not a claim of optimality of the exact alphabet $2q$.

The same conditional atom bound holds when conditioning on any subset of at most $t-1$ other shares: extend it to a $(t-1)$-set not containing party $i$, use the bound just proved there, and average. For a fixed unauthorized coalition of size $h$, multiply the conditional atom bounds along any ordering of its parties. The resulting tuple has each probability at most $q^{-h}$ for the independent uniform secret, and by privacy also for any fixed secret. With the secret fixed, each single dealer key maps deterministically to some such tuple, so every admissible dealer key atom is at most $q^{-h}$. In particular every source has min-entropy at least $hb$, key cardinality at least $q^h$, and key label length at least $hb$ bits in any such perfect scheme. The construction approaches this slope with a fixed $n,t$ overhead; no exact key cardinality optimality outside the following template is claimed.

**Local multiplicity template only.** This statement concerns a pair of branches at a single index, whose keys have inactive sets $D\in\mathcal D$ with nonnegative integer multiplicities $a_D^+,a_D^-$. Assume for every $|J|=h$ and every proper $R\subsetneq J$ that the two branches give identical multiplicities of that observed tag pattern $D\cap J=R$. Let $c_D'=a_D^+-a_D^-$ and $g=\sum_D c_D'$. The difference of the projected multiplicities is then concentrated on $R=J$ with signed mass $g$. For any $K$ of size at most $h$, choose such $J\supseteq K$ and sum over tag patterns containing $K$; this yields $\sum_{D\supseteq K}c_D'=g$. These triangular equations uniquely determine $c_D'$ (descend in $|D|$ starting with $h$), so (4) shows $c_D'=g c_D$. If branch sizes have different parity, $g$ is odd and $|g|\ge1$. Therefore the total number of copies across two branches is at least
$$
\sum_D(a_D^++a_D^-)\ge \sum_D|c_D'|=|g|C\ge C.
$$
The construction uses disjoint copies, $g=1$, and exactly $C$ labels. This minimum proves only a conditional optimality within tag-local cancellation with at most $t-1$ inactive players and an odd branch-size difference. Neither locality nor this template is necessary by definition for general perfect sharing.

## 6. Endpoints and the qualitative prior implication

For $t=2$, (1) gives $c_\varnothing=-(n-1)$ and $c_{\{j\}}=1$. Thus $C=2n-1$, $G_+=n$, $G_-=n-1$. The pads are all the single symbol $u$. In characteristic two, both Lagrange coefficients for an authorized pair coincide, so distinct nonzero $\gamma_j$ suffice for (8), possible for $q>n$. Relabel each active share value by multiplication by $\gamma_j^{-1}$ while leaving the inactive tag values unchanged. This identifies (7) with Aggarwal v2 Eq. (5) and the flat source supports with Eq. (6) up to complementation of $T$. The error agrees with Theorem 4.1, including $1/6$ at $n=2$.

For $t=n$, the coefficients have magnitude one. With active set $S=[n]\setminus D\ne\varnothing$, the plus group is exactly odd $|S|$; $C=2^n-1$. Relabel the value of each party $j$ by multiplying by $w_{[n],j}$, for either tag. The relabeled pads have sum zero and their first $n-1$ values are independent coordinates on the pad space by the evaluation bijection. This is the pad parametrization in Aggarwal v2 Sec. 5. One can choose the scaled coefficients $w_{[n],j}\gamma_j$ linearly independent over $\mathbb F_2$ for $b\ge n$, equivalent to (8) in this case. This recovers the labels, shares, supports and error of Theorem 5.1. For $3\le t<n$ the signed multiplicities are genuinely different; for example $(t,n)=(3,4)$ gives $C=17$ and exact one-bit error $1/34$.

For comparison, put $r=\binom n{t-1}$. The standard distribution design in ACOR Section 4 takes an old $r$-out-of-$r$ scheme, labels its old players by the $(t-1)$-subsets $B$ of $[n]$, and hands new party $j$ the old shares whose label does not contain $j$. A $t$-set receives all old shares; a $(t-1)$-set misses its own label and receives every other one. This does not spend new randomness and preserves privacy, correctness and the source class from the old scheme. Therefore Aggarwal v2 Theorem 5.1 already yields qualitative existence for every threshold. This particular reduction requires $b\ge r$, assigns each new party $\binom{n-1}{t-1}$ old shares, uses an old key set of $(2^r-1)q^{r-1}$ elements, and has optimal one-bit error $1/[2(2^r-1)]$ for that old source class. These are the known construction's costs, not a lower bound on all possible reductions. Our theorem supplies the direct quantitative construction and the resource statements above, not the first all-threshold separation in principle.
