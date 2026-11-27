# Near-maximal streaming memory for recognizing power-free integers

A positive integer is $k$-free if no prime $p$ satisfies $p^k\mid N$; $k=2$ is squarefreeness. This note bounds the memory of recognizing one property of the factorization. It does not bound the unrestricted computation of integer factors.

Fix an integer base $b\ge2$ and a fixed integer $k\ge2$. Put $\gamma_k=k^2/(k-1)$.

**Deterministic theorem.** On canonical $B$-digit base-$b$ inputs, an exact one-pass machine in either natural digit order needs at least
$$
B\log_2 b-\gamma_k\log_2 B-O_{b,k}(1)
$$
bits of state. Even with transitions depending on the position and unbounded local computation, the width at one predetermined cut is $\Omega_{b,k}(b^B/(\log(b^B))^{\gamma_k})$. In particular, the least-significant-first $b$-automaticity of the squarefree characteristic sequence through $Y$ is $\Omega_b(Y/(\log Y)^4)$, improving the $\Omega(Y^{2/5})$ bound in [Shallit, *Automaticity IV*, Theorem 9](https://jtnb.centre-mersenne.org/item/JTNB_1996__8_2_347_0/). The earlier result and this comparison use the same least-significant-first convention; we separately prove the bound for most-significant-first.

**Bounded-error theorem.** In binary, recognizing $k$-freeness on every canonical $B$-bit input with fixed error strictly less than $1/2$ in $r$ full passes, each in a predetermined natural digit order, needs $rs=\Omega_k(B/\log B)$ for state size $s$ in bits (the constant may depend on the error). The orders may differ between passes. Both theorems charge all persistent information, and neither applies to free random access or writable input.

## A short continuation pattern distinguishes almost all prefixes

Set $Y=b^B$ and $A=\lfloor C_0\log Y\rfloor$, with $C_0$ a sufficiently large constant. Let $\mathcal P$ be all primes $\ell\le A$ not dividing $b$. The prime number theorem gives
$$
\prod_{\ell\in\mathcal P}\ell^k>Y
$$
for all sufficiently large $Y$. Fix a large constant $C_1$ depending only on $b,k$. Take $W=b^L$ to be the smallest power of $b$ at least $C_1 A^{\gamma_k}$, and $R=b^{B-L}=Y/W$. For large $B$, $1\le L<B$. The cut is after the first $B-L$ input digits.

In most-significant-first order let $u$ run through the canonical $(B-L)$-digit prefixes. Its row is the Boolean string of $k$-freeness values of $uW+t$ as the continuation $t$ ranges over $[0,W)$. In least-significant-first order take the low prefixes $v$ coprime to $b$ with $0\le v<R$; its row is the string of values of $Rt+v$ for $t\in[W/b,W)$. In either case there are $\asymp_b R$ selected rows, every represented $N$ has $B$ digits, and within each direction each $N$ occurs in at most one row.

For any $\ell\in\mathcal P$, every row has a distinguished continuation residue modulo $\ell^k$ on which all its values are zero, because of divisibility by $\ell^k$. That residue is $-uW$ in the first case and $-v R^{-1}$ in the second. We show that in at least half the selected rows it is the **only** all-zero residue for every $\ell\in\mathcal P$ simultaneously.

Consider a continuation residue other than the distinguished one. In most-significant-first order additionally restrict to $t\equiv1\pmod b$; this can be combined with the residue modulo $\ell^k$, and makes $uW+t$ coprime to $b$. In least-significant-first order all $Rt+v$ are already coprime to $b$. The resulting set of candidate continuations is an interval in one arithmetic progression with $K$ elements, where uniformly
$$
K\ge K_0:=\left\lfloor\frac{W}{2b A^k}\right\rfloor.
$$
Indeed, the step is at most $b\ell^k$, and the respective intervals have lengths $W$ and $W(1-1/b)$; the floor error is absorbed for large $Y$. No $N$ in the candidate set is a multiple of $\ell^k$.

Set $z=\lfloor K_0/16\rfloor$. For each other prime $p\le z$ not dividing $b$, as we run through the candidates, the corresponding integers vary in an arithmetic progression of step coprime to $p$. Thus at most $K/p^k+1$ candidates are multiples of $p^k$. The union over those primes covers at most
$$
K\sum_{j=2}^\infty j^{-k}+z
\le \tfrac34 K+\tfrac1{16}K .
$$
For the displayed elementary constant, use $1/2^2=1/4$ and bound the sum for $j\ge3$ by the telescoping sum of $1/(j(j-1))$. Hence small primes cannot cover the other residue class.

For a row $\mathcal R$, let $G(\mathcal R)$ be the number of its represented integers divisible by $p^k$ for some $p>z$. Across all selected rows in either orientation,
$$
\sum_{\mathcal R}G(\mathcal R)\le
\sum_{p>z}\left\lfloor\frac{Y}{p^k}\right\rfloor
\ll_k Y/z^{k-1}.
$$
This counts globally, not in a short interval or a thin residue class. Call a row good if $G(\mathcal R)\le K_0/16$. The fraction of other rows is
$$
\ll_{b,k}\frac{Y}{R\,K_0\,z^{k-1}}
 \ll_{b,k}\frac{A^{k^2}}{W^{k-1}} .
$$
Since $\gamma_k(k-1)=k^2$, a sufficiently large fixed $C_1$ makes that fraction at most one half. In every good row the *total* number of large-prime bad positions is at most $K_0/16$. Along with the small-prime bound this leaves at least one $k$-free representative in every nondistinguished residue class, for all $\ell\in\mathcal P$. No union bound over residue classes is necessary.

If two good rows have the same Boolean string, their distinguished continuation residues must coincide for every $\ell$. Both $R$ and $W$ are units modulo $\ell^k$, so their prefixes agree modulo the product of the $\ell^k$, which is larger than $Y$. Their prefixes are therefore identical. The distinct good rows force distinct states at the cut: a common continuation separating two rows demands different correct decisions. There are $\Omega_{b,k}(Y/W)$ states, proving the claimed bound.

For $b$-automaticity through an arbitrary cutoff instead of a full digit-length range, choose the largest complete range of base-$b$ words lying below the given cutoff. Its upper limit is within a constant factor of that cutoff. A DFA computing the characteristic sequence there also works at this particular digit length, so the state bound transfers. Shallit's Lemma 8 likewise distinguishes two low residues via a prime square dividing one continuation value but not the other. The new strategy is to count large-prime obstructions globally and distinguish a positive fraction of rows simultaneously, rather than requiring a squarefree witness in every individual long progression.

## Reduction from randomized disjointness

Use a binary split into a high block of length $h=\lfloor B/4\rfloor$ and low block of length $J=B-h$. Let $\ell_1,\ldots,\ell_t$ be the first $t$ odd primes, where $t$ is the largest integer such that
$$
D_{\mathrm{odd}}=\prod_{i\le t}\ell_i^k \ \le 2^{B/8}.
$$
By the prime number theorem $t=\Theta_k(B/\log B)$. Given the two parties' bit vectors $x,y\in\{0,1\}^t$, the high-block party can pick $a\in[2^{h-1},2^h)$ with
$$
2^J a\equiv 1-x_i\pmod{\ell_i^k}\qquad(1\le i\le t).
$$
The factor $2^J$ is invertible modulo these odd prime powers and the high-block interval is longer than $D_{\mathrm{odd}}$. Independently the low-block party draws $v$ uniformly from the class in $[0,2^J)$ defined by
$$
v\equiv 1-y_i\pmod{\ell_i^k}\quad(1\le i\le t),\qquad
v\equiv1\pmod{2^k}.
$$
This class has $U\asymp 2^J/(2^k D_{\mathrm{odd}})$ elements. The combined word $N=2^J a+v$ always has $B$ bits.

If some coordinate belongs to both sets, its $\ell_i^k$ divides $N$ with certainty. Conversely, if the sets are disjoint, none of the $\ell_i^k$ divides $N$, since the individual allowed sums are $1$ or $2$. The power $2^k$ is excluded as well. For another prime $p$, at most a fraction $p^{-k}+1/U$ of the possible low blocks give $p^k\mid N$, since the sampling progression step is coprime to $p$. A union bound over $p>\ell_t$ with $p^k<2^B$ shows that the error on disjoint inputs is at most
$$
\sum_{p>\ell_t}p^{-k}+\frac{2^{B/k}}{U}=o(1).
$$
Here $U\gg_k 2^{5B/8}$ and $k\ge2$. No equidistribution of primes in these progressions is used.

Now simulate an $r$-pass streaming machine by having the holder of the current block run that part of the pass. The parties send only the persistent state at handoffs. Fixed natural order makes at most $2r-1$ handoffs, with at most one additional bit to communicate the answer. Input randomness for the low block can be drawn by its holder; the machine's own coins can be public. On each communication input, the streaming machine's fixed error increases by at most the $o(1)$ arithmetic error just computed. For any fixed original error $<1/2$ this is still bounded away from $1/2$ from below, and a constant number of repetitions suffices for the usual disjointness error convention. [Razborov's randomized disjointness lower bound](https://doi.org/10.1016/0304-3975%2892%2990260-M) then gives $\Omega(t)=\Omega_k(B/\log B)$ total communicated bits. The streaming tradeoff follows.

## Verification and scope

The [small exact checker](verify_factor_powerfree_streaming.js) tests the residue patterns of good rows, the global obstruction count, and the randomized reduction's residue and sampling logic on predetermined toy inputs. It does not test the asymptotic estimates or process arbitrary integers. These are decision lower bounds in a prescribed streaming interface; no equivalence to unrestricted integer factoring, lower bound on its general running time, or proof about free outside persistent memory is implied.
