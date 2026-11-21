# A pointwise, one-root obstruction to rapid merging of mixed-order prime-factor paths

For an even \(N\) use the directed graph on unit odd primes \(3\le z\le N-3\); the arc \(z\to y\) means \(y\mid N-z\) and has actual multiplicity \(e=v_y(N-z)\). All factors of \(N-z\) are again vertices. A genuine Goldbach pair gives a terminal cycle (or a repeated prime; at large \(N\) the repeated prime divides \(N\) and is not in this unit graph). Let \(G_N=(\mathbb Z/N)^\times/\{\pm1\}\). Write \(L=\log N\). For a positive integer \(H\), put \(K=\operatorname{lcm}(1,\ldots,H)\). Retain the edge \(z\to y\) only when \([y]^{Ke}\ne1\) in \(G_N\); thus its actual contribution \([y]^e\) has order \(>H\). We do not require successive orders to be comparable, maximal or supported on the same primary part.

**Pointwise conclusion.** Fix \(\epsilon>0\). At **every** sufficiently large even \(N\) there is one unit prime \(x\le N^\epsilon\) with the following property. Set \(H=\lfloor(\log L)/10\rfloor\), \(d=\lfloor L^{1/8}\rfloor\). Even after forbidding any \(\lfloor\sqrt L\rfloor\) downstream vertices and **all** primes up to \(L^{1/3}\), there are at least \(\lfloor\sqrt L\rfloor\) pairwise vertex-disjoint pieces starting at distinct actual one-step successors of \(x\). Each piece is either a simple directed path of \(d\) edges, or a simple stem leading to a directed cycle, with the closing edge reached within \(d\) steps. Every edge of every piece and its initial edge from \(x\) is retained. The pieces themselves omit \(x\); the paths including their initial edge share that one root. Forbidding vertices applies to the pieces, so if \(x\) itself is forbidden this does not delete the common first departure. Alternatively, if a forbidden set is specified in advance one can choose an admissible root outside it.

The root can depend on \(N\); nothing says these walks start from a preassigned prime such as 3. If the full orbit of this root has no genuine prime complement, every visited complement is composite, including on all reported cycles. Thus a no-pair orbit from this actual root cannot feed all its one-step branches into a small common trap at bounded depth. This does not prove that the orbit reaches a genuine pair, that the pieces lie in one strongly connected component, or that every terminal component is large.

## A single physical root contains an independent fan

It suffices to treat \(0<\epsilon\le1/2\). Use any absolute constants \(C,\lambda\ge1\) from Linnik's least-prime theorem, \(p(b,D)\le C D^\lambda\) for reduced classes; for example the much stronger explicit result of [Xylouris, *On the least prime in an arithmetic progression*, Theorem 1.1](https://www.impan.pl/shop/publication/transaction/download/product/83078) suffices without optimizing \(\lambda\). Let
\[
 m=\left\lfloor {\epsilon L\over100\lambda\log(4L)}\right\rfloor .
\]
Choose any \(m\) distinct primes \(q\in[L,4L]\) not dividing \(N\). They exist since the sum of prime logarithms on this interval is \((3+o(1))L\), while the distinct divisors of \(N\) cost at most \(L\). Write \(\mathcal Q\) for this fan, \(W=\prod_{q\in\mathcal Q}q\). Then \(W\le N^{\epsilon/(100\lambda)}\).

Choose a prime \(b\in[L^2,2L^2]\). For each \(1\le u<b\), independently impose
\[
 x\equiv N-W\bmod W^2,\qquad x\equiv u\bmod b,\qquad x\equiv1\bmod2.
\]
The combined class is reduced (especially \((N-W,W)=1\)). Distinct \(u\) give distinct primes \(x\le C(2bW^2)^\lambda<N^\epsilon\) by Linnik. After removing primes \(\le4L\) and prime divisors of \(N\), still \(\gg L^2\) choices remain. In particular a preannounced forbidden set of size \(O(\sqrt L)\) cannot exhaust the roots. Fix any one. Each edge \(x\to q\) has multiplicity **exactly one**, since \(N-x\equiv W\bmod W^2\). Its complement is composite for large \(N\). The signed order of \([q]\) is at least \(\log(N-1)/\log(4L)\) since \(q^j\equiv\pm1\bmod N\) requires \(q^j\ge N-1\). In particular all the first edges are retained whenever \(K\le m/4\).

## Depth versus the cardinality of a physical separator

For all integers \(d\ge1,\ K\le m/4\), the following quantitative statement applies to the same \(x,\mathcal Q\). If a set \(T\) of vertices meets **every retained walk of \(d\) edges starting anywhere in \(\mathcal Q\)** (meeting by depth \(d\), including at the initial vertex, suffices), then
\[
       |T|\ \ge\ c_1\,{m\over K(d+1)\log L}                     \tag{1}
\]
with an absolute \(c_1>0\). Repeated physical vertices are not counted multiple times in \(T\).

The exact identity
\[
            [z]^K=\prod_{z\to y\ {\rm retained}}([y]^K)^{v_y(N-z)}
                                                                    \tag{2}
\]
follows because \([N-z]=[z]\) in the signed group and the omitted contributions have trivial \(K\)-th powers. Every nontrivial \([z]^K\) has a retained child, and every such child has \([y]^K\ne1\). Unfold (2) down the whole tree from each fan prime, stopping whenever \(T\) is hit. Under the hypothesis all branches stop by depth \(d\), with no other dead end because the fan primes are nontrivial after powering. In expansion, exponents multiply along a path, and add if leaves are the same vertex. At each row the sum of outgoing multiplicities is at most \(A=L/\log3\); hence total leaf weight is at most \(A^d\), also if the root is already in \(T\). In particular \([q]^K\) is a product of the \([z]^K,\ z\in T\), with nonnegative integral total exponent at most \(A^d\). This is not an iteration of the map \(g\mapsto g^K\): \(K\) is paid **once** at any depth.

Set \(t=\lfloor m/(2K)\rfloor\ge m/(4K)\). Products \(V\) of \(t\) distinct fan primes have pairwise distinct \([V]^K\): their positive integer \(K\)-th powers are all \(\le (4L)^{Kt}\le W_{\max}^{1/2}<N/2\), where \(W_{\max}=(4L)^m\le N^{\epsilon/(100\lambda)}\). Therefore signed congruence forces ordinary equality (two such positive integers cannot sum to \(N\)), and unique prime factorization distinguishes the subsets. There are \(\binom mt\ge(m/t)^t\ge2^t\) such residues. On the other hand (2) writes all of them with at most \((1+tA^d)^{|T|}\) exponent vectors. Since \(\log(1+tA^d)\ll(d+1)\log L\), this proves (1).

## Packing and longer simple paths

Put \(h_*=c_1m/(K(d+1)\log L)\). Given a physical forbidden set \(T_0\), start with \(T=T_0\cup\{x\}\). When \(|T|<h_*\), (1) supplies a full retained length-\(d\) walk from a fan prime avoiding \(T\). If there is a repeated vertex, truncate at the **first** repeat, yielding a cycle with a simple disjoint stem (possibly empty). Otherwise keep the whole simple path. Add its at most \(d+1\) distinct labels to \(T\) and repeat. Thus we pack at least \(\lfloor(h_*-|T_0|-1)/(d+1)\rfloor\) disjoint pieces when positive. Their starts are distinct; they and their prefixes \(x\to q\) are in the very same actual forward orbit. If \(x\notin T_0\) these are routes in the graph with \(T_0\) deleted.

Since \(\log K=\psi(H)\le2H\) eventually, for the concrete choices in the theorem we have \(K\le L^{1/5}\le m/4\). Then \(h_*\gg_\epsilon L^{27/40}/(\log L)^2\); after deleting \(\lfloor\sqrt L\rfloor\) arbitrary labels plus all the primes \(\le L^{1/3}\), the packing lower bound is \(\gg_\epsilon L^{11/20}/(\log L)^2>\sqrt L\). This proves the stated pointwise conclusion.

There is also a fixed-packing-number variant with a longer simple path. Fix \(k\ge1\), \(K\le m/4\). By [Reed–Robertson–Seymour–Thomas, *Packing directed circuits*, Theorem (1.3)](https://thomas.math.gatech.edu/PAP/younger.pdf), a finite digraph without \(k\) vertex-disjoint directed cycles has a feedback set of at most \(f(k)\) vertices. Apply this to the retained graph reachable from the surviving fan after deleting \(T_0\cup\{x\}\). Either it contains \(k\) vertex-disjoint directed cycles, or adjoin its feedback set to \(T_0\cup\{x\}\). A walk avoiding that enlarged set is simple, since it stays in the reachable graph minus its feedback set. Thus, whenever the displayed scale tends to infinity, (1) gives a simple retained path from the fan of length
\[
       \gg {m\over K\,(|T_0|+1+f(k))\,\log L}.
\]
In particular with \(T_0=\varnothing\) this is \(\gg_{\epsilon,k} L/(K(\log L)^2)\). The cycles in this variant are mutually disjoint but their access paths need not be. The argument uses varying group elements in the full signed group, not a claim that a prescribed local maximal-order channel has a way out.