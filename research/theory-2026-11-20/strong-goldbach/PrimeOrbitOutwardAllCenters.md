# At every large center: outward prime factorizations and persistent primary-order cycles

Let \(N\) be even. Vertices are odd primes \(p<N-1\) coprime to \(N\). For every exact positive exponent \(e=v_q(N-p)\), there is an actual edge \(p\to q\) with contribution \(q^e\). Every such \(q\) is a vertex for large \(N\) (it is odd, coprime to \(N\), and at most \(N-3\)). Call \(p\) a genuine endpoint when \(N-p\) is itself prime. The signed group is the full finite abelian group \(G_N=(\mathbb Z/N\mathbb Z)^\times/\{1,-1\}\); an order below always refers to its image there. Write \(\operatorname{ord}_\ell\) for the largest power of \(\ell\) dividing the order, not its logarithm. No theorem below excludes all-composite directed cycles.

## I. A fixed menu: high-order escape without any condition on the center

Fix any finite menu \(P\) of distinct odd primes, any finite forbidden prime alphabet \(S\), and any integer \(H\ge1\). For **every sufficiently large even \(N\)**, all but at most one of the unit members of \(P\) admit an edge \(p\to q\) with \(q\notin S\) and
\[
\operatorname{ord}_{G_N}(q^{v_q(N-p)})>H.
\]
The threshold depends on \(P,S,H\) and is not claimed effective. We may enlarge \(S\) to include \(P\) and every prime at most the largest member of \(P\) (a conclusion with this larger taboo implies the original one); the exhibited exterior primes for different seeds are then distinct, since any common prime divisor divides the nonzero difference of the seeds.

**Proof.** It suffices to rule out a sequence \(N\to\infty\) with two fixed distinct failing unit seeds \(p_1,p_2\) (a finite union of such pairs covers the bad centers). Factor \(N-p_i=P_iV_i\) with \(P_i\) its full \(S\)-part and \(V_i\) its part supported outside \(S\). Both are units modulo \(N\), and \(p_i\nmid P_i\) since \(p_i\nmid N\). Put \(k=2\operatorname{lcm}(1,\ldots,H)\). If the two inputs fail, each exterior contribution raised to \(k\) is 1 modulo \(N\), so the fixed-group positive rational \(S\)-units
\[
u_i=(p_i/P_i)^k
\]
are both 1 modulo \(N\). Neither is the rational number 1. Their logarithmic heights are at most \(k\log N\).

Use [Corvaja and Zannier, Proposition 2, (2.8)](https://arxiv.org/pdf/math/0311030), with \(K=\mathbb Q\) and the archimedean place adjoined to \(S\). For all but finitely many pairs of \(S\)-units with
\[
-\sum_v\log^-\max(|u_1-1|_v,|u_2-1|_v)>\varepsilon\max(h(u_1),h(u_2)),
\]
there is a nontrivial exact multiplicative dependence \(u_1^\alpha u_2^\beta=1\). This is the all-places proposition, with exact subgroups, not the later translated-subgroup version. Here \(\log^-z=\min(0,\log z)\), so nothing at infinity, nor at \(S\), can offset the finite-place lower bound. At each \(r^a\parallel N\) the contribution is at least \(a\log r\), giving the required strict inequality with \(\varepsilon=1/(2k)\). None of the finitely many exceptional pairs can recur at arbitrarily large \(N\): the numerator of the fixed nonzero \(u_1-1\) must be divisible by \(N\).

At \(p_1,p_2\), a dependence gives \(\alpha=v_{p_1}(P_2)\beta\) and \(\beta=v_{p_2}(P_1)\alpha\). Thus neither coefficient is zero; both valuations are 1 and \(\alpha=\beta\). At every remaining prime the two valuations in this equation have the same weak sign; both must vanish. Hence \(P_1=p_2,\ P_2=p_1\). The congruence now requires \(N\mid p_1^k-p_2^k\ne0\), impossible along an unbounded sequence. This proves I.

**Actual downstream alternative.** For each fixed integer \(J\ge1\), use I with \(H=\operatorname{lcm}(1,\ldots,J)\). The exhibited contribution has order with some \(\ell\)-primary part \(>J\); otherwise its order divides \(H\). The vertex \(q\) has at least this much \(\ell\)-order. Starting there, stop on encountering a genuine endpoint. Otherwise the product of all actual prime-power contributions in a row at \(x\) equals \(N-x\), which has the same signed class as \(x\). Since the order of a product in an abelian group divides the lcm of the orders of the factors, one may choose an edge \(x\to z\) of exponent \(e\) with
\[
\operatorname{ord}_\ell(x)\le\operatorname{ord}_\ell(z^e)\le\operatorname{ord}_\ell(z).
\]
Finiteness gives either a genuine endpoint or a directed cycle, entirely in nonendpoint vertices, on which every inequality is equality and the common primary order is \(>J\). In particular \(\ell\nmid e\) for every selected cycle edge. The prime \(\ell\) is held fixed down that path, but can depend on the center and seed. A genuine endpoint at the starting seed already meets the endpoint alternative. The cycle need not lie outside the taboo and need not be an entire terminal strongly connected component. The monotone path argument alone can also start with the order of the seed; the gain above is to certify high order on a first edge outside an arbitrary fixed taboo.

## II. Many moving inputs: strict outward matching and a large rough product

Fix \(0<\delta<1/2\), set \(T=\log\log N,\ Y=\exp(\exp(T^{1/2-\delta}))\), and let \(V_x\) be the part of \(N-x\) supported on primes strictly greater than \(Y\), with full multiplicities. Uniformly for every sufficiently large even \(N\), apart from \(O_\delta(\pi(Y)T^{-\delta/2})\) odd unit prime seeds \(x\le Y\),
\[
\log V_x\ \ge\ (\log N)\exp\{-C_\delta(T^{1-3\delta/2}+\log T)\}.
\]
In particular \(\log V_x\ge(\log N)^{1-o(1)}\). Each such seed therefore has an actual edge to a prime \(>Y\), larger than **every** input; distinct seeds have distinct output primes. The bound is on the **product** with multiplicity, not on one prime factor of that size. No order lower bound is inferred for this same matching.

The pointwise support average is
\[
\sum_{x\le Y,\ x\ {\rm prime},\ (x,N)=1}\omega_{\le Y}(N-x)\ll\pi(Y)\log\log Y .
\]
Indeed sum by prime divisor \(r\le Y\); residues \(x=N\bmod r\) are reduced whenever such an input exists. For \(r\le\sqrt Y\) Brun–Titchmarsh gives \(O(Y/((r-1)\log Y))\) per \(r\). For \(\sqrt Y<r\le Y/2\) separate \(Y/2^{j+1}<r\le Y/2^j\), \(j\ge1\), using \(O(2^j/j)\) per \(r\) and \(O(Y/(2^j\log Y))\) primes per shell (with absolute constants for this range). For \(Y/2<r\le Y\) use at most two representatives per \(r\). Summing proves the estimate, the same elementary input as in the large-prime-power-divisor order matching. Thus outside the stated exceptional set each row has at most \(T^{1/2-\delta/2}\) small prime divisors.

Consider any two distinct such good seeds \(x,y\). Their actual nonzero real log difference is
\[
\Lambda=\log\frac{N-x}{N-y}
=\log\frac{V_x}{V_y}+\sum_{r\le Y}(v_r(N-x)-v_r(N-y))\log r .
\]
It has \(|\Lambda|\le2Y/N\). Retain only nonzero summands, omitting the exterior base if its ratio is 1. At most \(s=2T^{1/2-\delta/2}\) small logarithms remain. Set \(H'=\max(1,\log V_x,\log V_y)\). The exterior ratio, if present, is **one** rational base of height at most \(H'\); this avoids multiplying two large unknown heights. For each small base \(r\) use \(A_r=\log r\) and for the exterior use \(A=H'\). These dominate the logarithmic height, absolute real log and 0.16. All coefficients are \(\ll\log N\). [Matveev, Corollary 2.3, (2.4),(2.6)](https://doi.org/10.1070/IM2000v064n06ABEH000314) bounds \(-\log|\Lambda|\) by
\[
\exp(O(n+1))\Big(\prod_j A_j\Big)\log(e B^*),\qquad B^*=\max(1,\max_j|b_j|),
\]
in rational degree one, with \(n\le s+1\), without assuming multiplicative independence. If just one term is present the elementary rational bound \(|b\log(u/v)|\ge 1/\max(u,v)\) for distinct positive integers \(u,v\) and \(b\ne0\) suffices. If none were present we would have \(x=y\); the cases \(V_x=1,V_y=1\) need no different hypothesis. Comparing with the upper bound on \(|\Lambda|\) yields
\[
\tfrac12\log N\le H'\exp\{O_\delta(T^{1-3\delta/2}+\log T)\}
\]
using \(s\log\log Y=2T^{1-3\delta/2}\). Consequently at most **one** good seed has its rough product below the claimed threshold. Absorb it into the exceptional count.

**Comparison.** Classically, linear forms in logarithms bound gaps between integers composed of a prescribed finite set of primes. Here the prime alphabet grows, a distinct moving exterior rational base is present, and the sparsity estimate is applied across prime shifts at each fixed center. [Shorey and Tijdeman](https://pub.math.leidenuniv.nl/~tijdemanr/shoretij.pdf) survey greatest prime factors of products in arithmetic progressions; estimates for smooth numbers in most intervals (e.g. [these authors' results](https://arxiv.org/abs/2502.10530)) have different quantifiers. No priority or improvement over known Goldbach exceptional-set estimates is asserted. I and II are separate results: neither excludes the cycle alternative, produces a pair at every center, or solves binary Goldbach.
