# An exact rare-event law for narrow cyclic interaction graphs

This is a graph/arithmetic note about explicit synthetic interaction graphs. Its main result is a finite count for random shifts, not a new treewidth characterization, a decoding tool, or an algorithm for standard Ring-LWE.

## 1. The finite count

Let \(n\ge2\), let \(s\ge2\) be fixed, and draw \(a=(a_1,\ldots,a_s)\) uniformly among the ordered generating tuples of \(\mathbb Z/n\mathbb Z\): \(\gcd(n,a_1,\ldots,a_s)=1\). Zero and repeated entries are allowed. Define the integer minimum character displacement
\[
 {\cal K}(a)=\min_{1\le r<n}\max_j |r a_j|_n,\qquad
 |x|_n=\min_{z\in\mathbb Z}|x-zn|.
\]
Put \(J_b(m)=m^b\prod_{p\mid m}(1-p^{-b})\) with \(J_b(1)=1\), and let \(P_s(R)\) count nonzero vectors in \(\mathbb Z^s\) of norm \(\|v\|_\infty\le R\) whose coordinates have gcd \(1\), identifying only \(v\) and \(-v\). For every real \(B\ge1\) with \(2B^2<n\) the exact answer is
\[
 \boxed{\displaystyle
 \Pr[{\cal K}\le B]=
 \frac{n}{J_s(n)}
 \sum_{\substack{t\mid n\\t\le B}}
       J_{s-1}(t)\,P_s(B/t)
       \prod_{\substack{p\mid n\\ \nu_p(t)<\nu_p(n)}}(1-p^{-1}).}            \tag{1}
\]
All factors are elementary integers or rational numbers, and the order-\(t\) factor cannot in general be replaced by the \(t=1\) unit-character term.

For prime-power orders \(n=p^e\) this specializes to
\[
 \Pr[{\cal K}\le B]
   =\frac{1-p^{-1}}{(1-p^{-s})\,n^{s-1}}
      \sum_{\substack{[v]\ {\rm primitive}\\\|v\|_\infty\le B}}
           p^{(s-1)\lfloor\log_p(B/\|v\|_\infty)\rfloor}.                 \tag{2}
\]
In particular on dyadic orders, and more generally whenever the number of distinct prime divisors of \(n\) is bounded, along \(B\to\infty\), \(2B^2<n\),
\[
       \Pr[{\cal K}\le B]\sim
             \frac{2^{s-1}}{\zeta(s)}\frac{B^s}{n^{s-1}} .                \tag{3}
\]
No universal positive leading constant is asserted for orders with unrestricted prime support.

## 2. Primitive directions and their disjointness

For a primitive integer vector \(v\), let \(t_v(a)\) be the additive order of the image of \(a\) in
\[
       (\mathbb Z/n\mathbb Z)^s/\big((\mathbb Z/n\mathbb Z)v\big).
\]
This is a divisor of \(n\). Since \(v\) is primitive over the integers, choose \(u\in\mathbb Z^s\) with \(u\cdot v=1\). The transverse vector \(a-(u\cdot a)v\) represents the quotient and has order \(t_v(a)\) independently of that choice. In particular
\[
       t_v(a)=\frac{n}{\gcd\bigl(n,\{a_i v_j-a_j v_i\}_{i<j}\bigr)}.      \tag{4}
\]
Indeed the transverse entries are integer combinations of the wedge entries, by \(u\cdot v=1\), and the wedge entries of \(a\) and \(v\) are unchanged upon replacing \(a\) by its transverse vector.

There is a pointwise equivalence for \(0<B<n/2\):
\[
 {\cal K}(a)\le B
 \quad\Longleftrightarrow\quad
 \text{some primitive \(v\) satisfies }t_v(a)\|v\|_\infty\le B.            \tag{5}
\]
For the forward implication take a witness \(r\), set \(t=\gcd(r,n)\) and \(m=n/t\), and divide the centered residues of \(r a\) by \(t\) to obtain an integer vector \(z\). Modulo \(m\), this vector is a unit multiple of the generating tuple \(a\bmod m\), so \(\gcd(m,z_1,\ldots,z_s)=1\) and \(z\ne0\). Divide \(z\) by the positive gcd of its coordinates to obtain \(v\). That gcd is a unit modulo \(m\); thus \(a\bmod m\) is a unit multiple of \(v\bmod m\), and \(t_v(a)\mid t\). This gives the right side. Conversely, put \(t=t_v(a)\) and \(m=n/t>1\). We have \(a\equiv c v\bmod m\) for an integer \(c\); \(c\) is a unit modulo \(m\) because \(a\bmod m\) generates the cyclic group. Take \(r=t c^{-1}\bmod n\) using the inverse modulo \(m\). This is nonzero and \(ra\equiv t v\bmod n\), so gives the required displacement.

Suppose a single \(a\) satisfies the right side of (5) for \(v,w\), and put \(t=t_v(a),u=t_w(a)\). Reduction modulo \(n/\operatorname{lcm}(t,u)\) gives that \(v,w\) differ by a unit scalar there. Each coordinate of their wedge is thus a multiple of \(n/\operatorname{lcm}(t,u)\); it has absolute value at most \(2B^2/(tu)<n/\operatorname{lcm}(t,u)\). The wedge vanishes as an integer vector. The two integer primitive vectors are parallel and hence equal up to sign. This proves the nonoverlap in the range of (1). It does not require \(\operatorname{lcm}(t,u)=\max(t,u)\).

The leading size of this range cannot be raised uniformly by this disjoint-counting argument. For each integer \(B\ge2\), set \(n=B^2+(B-1)^2\), \(v=(B,B-1)\), \(w=(-(B-1),B)\), and \(a=v\bmod n\). The determinant is \(n\), and both first coordinates are units modulo \(n\), so \(v\) and \(w\) are distinct signed directions in the same unit orbit. Both have \(t_v=t_w=1\) and norm \(B\). The example extends to \(s>2\) by appending zero coordinates. Also, a unit-only count already misses examples well inside the range: for \(n=2^e\ge16\), \(a=(1,n/2+1)\) satisfies \({\cal K}=2\) by \(r=2\), whereas the only odd \(r\) with \(|r|_n\le2\) are \(\pm1\), and neither yields both coordinates at most \(2\).

## 3. Counting and the limit

A unimodular integer change of coordinates takes \(v\) to \(e_1\): one can reduce its coordinate column by the Euclidean algorithm since its gcd is \(1\). Thus the number of generating tuples with \(t_v(a)=t\) is independent of the direction. Once \(v=e_1\), the last \(s-1\) coordinates \(b\) have additive order exactly \(t\) modulo \(n\). They are in bijection with the generating \((s-1)\)-tuples modulo \(t\), by multiplying each coordinate by \(n/t\); hence their number is \(J_{s-1}(t)\). For each such \(b\) and every \(p\mid n\), a coordinate of \(b\) is not divisible by \(p\) iff \(\nu_p(t)=\nu_p(n)\). At the other primes the first coordinate must be a unit modulo \(p\); there are exactly \(n\prod_{p\mid n,\ \nu_p(t)<\nu_p(n)}(1-p^{-1})\) choices for it. Divide by the total \(J_s(n)\) and sum the disjoint directions from Section 2 to obtain (1). For \(n=p^e\), all admissible \(t=p^j\) satisfy \(j<e\). The identity \(\sum_{i=0}^j J_{s-1}(p^i)=p^{(s-1)j}\) yields (2).

For \(R\to\infty\), \(P_s(R)\sim 2^{s-1}R^s/\zeta(s)\). Indeed remove zero from the integer cube, apply Möbius inversion to the gcd, and divide by two:
\[
 P_s(R)=\frac12\sum_{1\le k\le R}\mu(k)\big((2\lfloor R/k\rfloor+1)^s-1\big).
\]
After normalizing by \(R^s\), the summands are dominated by a fixed multiple of \(k^{-s}\), and \(\sum\mu(k)k^{-s}=1/\zeta(s)\). For general \(n\), set
\[
 \omega_n(t)=\frac{J_{s-1}(t)}{t^s}
           \prod_{p\mid n,\ \nu_p(t)<\nu_p(n)}(1-p^{-1})
 \quad(t\mid n).
\]
This is a product over primes. Summing the prime-\(p\) factor at \(n=p^e\) over \(j=\nu_p(t)\) gives
\[
 (1-p^{-1})\left[1+(1-p^{-(s-1)})\sum_{j=1}^{e-1}p^{-j}\right]
             +(1-p^{-(s-1)})p^{-e}=1-p^{-s}.
\]
Consequently \(\omega_n(t)/(J_s(n)/n^s)\) is a probability on divisors of \(n\), with independent prime-power factors. In terms of that probability the ratio of (1) to \(B^s/n^{s-1}\) is
\[
                 \mathbb E \left[\frac{P_s(B/t)}{(B/t)^s}\right].         \tag{6}
\]
For \(x<1\) the quotient here is zero, and the quotients are bounded uniformly in \(x\). If \(n\) has at most \(b\ge1\) distinct prime divisors, these distributions of \(t\) are uniformly tight. Indeed \(t>H\) forces a prime-power factor \(p^j>H^{1/b}\); the local normalized weight at \(j\ge1\) is at most \(p^{-j}/(1-p^{-s})\), giving a local tail \(O_s(H^{-1/b})\) by a geometric sum, uniformly in \(p\) and \(e\). Union over the at most \(b\) factors. Uniform tightness and the limit for \(P_s\) give (3), including when the fixed number of primes are themselves allowed to vary with \(n\).

As a contrast, if all prime factors of \(n\) exceed \(B\), only \(t=1\) contributes and (1) is \(P_s(B)\varphi(n)/J_s(n)\). For each growing \(B\), one can use enough distinct primes greater than \(B\) to make \(\varphi(n)/n\to0\), by divergence of the sum of reciprocals of the primes. Meanwhile \(J_s(n)/n^s\ge1/\zeta(s)\). Thus the ratio in (6) can tend to zero even with \(B\to\infty\) and \(2B^2<n\).

## 4. A graph layout certificate and a limited computational consequence

For the undirected Cayley graph on \(\mathbb Z/n\mathbb Z\) with shifts \(\pm a_j\), the character-displacement parameter of [Biswas, §6 and Proposition 6.1](https://arxiv.org/html/2610.38552v1#S6) is exactly \({\cal K}/n\). His width characterization (Corollary 6.2) already implies \(\operatorname{tw}+1\asymp_s{\cal K}\asymp_s\operatorname{pw}+1\). A direct bandwidth version of the upper bound is useful for explicit tables: \(\operatorname{bw}+1\le3{\cal K}\).

To see it, choose a character attaining the minimum. Its image is a cycle of order \(h\ge2\), its fibres have size \(n/h\), and every edge changes the cycle coordinate by at most \(J=h\,{\cal K}/n\) cyclic steps. Here \(J\) is an integer at least one. Order the cycle residues as \(0,1,h-1,2,h-2,\ldots\), using each residue once. The positions of cycle neighbours differ by at most two, so cycle distance \(k\) costs at most \(2k\) positions. Lay each fibre out contiguously in this order. Every adjacent vertex pair then has separation at most \((2J+1)n/h-1\le3{\cal K}-1\). Taking sliding consecutive bags gives the same width bound. For arbitrary finite abelian groups the same argument works with \(n\) times the minimum nontrivial character displacement in place of \({\cal K}\).

In the explicit graphical-model problem with a fixed alphabet size \(q\) and rational pairwise factor tables on these edges, the normalization sum is therefore computable by bounded-width table contraction in \(\mathrm{poly}(L)\,q^{3{\cal K}}\) bit operations, where \(L\) is the explicit input length. To justify the bit bound, clear the denominators in each factor separately using the product of that table's denominators; the total bit length of all such products is at most the input size apart from elementary encoding overhead. Intermediate exact integers are bounded by a product of factor entry bounds times \(q^n\), so have polynomial bit length. A witness character can be checked by modular arithmetic on the shifts; inspecting all \(n-1\) characters is polynomial for explicit factor tables, not in the bit length of a succinct description of \(n\) alone. This yields a polynomial regime when \({\cal K}=O(\log n)\). If exact input tables live on scopes whose pairwise graph distances in this Cayley graph are at most \(b_0\), the same ordering gives bags of size at most \(3b_0{\cal K}+1\) by following a graph path, and the analogous assertion for fixed \(b_0\).

Artificial cyclic or negacyclic two-tap factor scopes are examples: wrap signs change table entries and not the undirected scope graph. The result concerns the normalization of explicit finite models; it supplies no actual-scheme implementation. In an independent ordered shift toy ensemble on dyadic \(n\), (3) quantifies the log-width certificate at, for example, \(B=C\log n\): its frequency is \(\Theta_s((\log n)^s/n^{s-1})\). Since Biswas's width lower bound is also proportional to \({\cal K}\) for fixed \(s\), the event of logarithmic treewidth obeys the same order, but the exact leading constant is for \({\cal K}\), not for treewidth. No claim is made that a generic dense coefficient design has fixed tap scope, that graph width is a necessary condition for all possible algorithms, or that a sparse-scope toy model represents standard Ring-LWE.

## 5. Scope and sources

[Biswas, Corollary 6.2](https://arxiv.org/html/2610.38552v1#S6) already proves the character/diameter/width comparisons and identifies the character-fibre sweep for pathwidth. [Berend–Korach–Lipets](https://doi.org/10.1016/j.disc.2007.08.083) concerns exact cutwidth and bisection for small generator sets. [Cai–Havas–Mans–Nerurkar–Seifert–Shparlinski](https://doi.org/10.1007/3-540-48686-0_36) connects circulant routing and short lattice vectors, and [Marklof–Strömbergsson](https://arxiv.org/abs/1103.3152) addresses limiting random-circulant diameter distributions in a different scaling. The specific increment here is the exact primitive-direction/Jordan count (1) for a fixed cyclic order (including nonunit frequencies), and its arithmetic-dependent rare tail. The bandwidth observation is an explicit variant of the known graph-width argument. No priority claim beyond this scoped comparison is needed.

**Replay.** The adjacent checker enumerates small integer displacements, primitive transverse ranks, and exact finite counts, and checks the bandwidth layout on synthetic graphs. It does not operate on cryptographic data.
