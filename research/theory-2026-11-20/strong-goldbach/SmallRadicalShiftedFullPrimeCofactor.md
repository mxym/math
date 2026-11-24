# A whole near-full-prime cofactor chamber with a genuine signed saving

Supersedes the artificial two-range cofactor truncation of [the simpler parity-fiber argument](SmallRadicalShiftedNaturalScaleParityFiber.md). Reuses only the verified prime-centered reflected comparison and actual last-prime BV/upper-sieve computations, not a shifted type-II estimate. This is still one chamber with a fixed **base** packet requirement on the true complement (different from the translated cover).

## 1. Statement and arithmetic range

Let \(P\) be large even with \(\operatorname{rad}(P)\le L^B\), \(L=\log P\), let \(I=PJ\) be an interior interval of fixed positive relative width, and let \(y=e^{L^\delta}\), \(0<\delta<.1\), \(z=e^{L^{.24}}\). Take a fixed full admissible base family \(\mathcal T\) of sufficiently many **even** \(K\) packets as in the prime-centered result. Its reciprocal mass is \(\mathcal V\asymp_K1\), and the set of all base packet primes is denoted \(\mathcal B\). Let
\[
0<\eta<\tfrac12,\qquad \tfrac14<a<b<\tfrac{1-\eta}{2}
\]
be fixed. Use the same fixed-relative rectangular construction with short prime \(p\) in \([P^a,P^b]\) and long prime \(q>p\), products inside \(I\), and \(O(L)\) disjoint short-coordinate boxes with area \(\asymp_J P\) each.

In these boxes consider the genuine rows
\[
n=pq,\qquad P-pq=u v r,\quad u\in\mathcal T,\quad r\text{ true prime},\quad
v\le P^\eta\text{ squarefree},\quad P^-(v)>y,\quad (v,\mathcal B)=1 .
\tag{1}
\]
Here \((v,\mathcal B)=1\) means that no prime of \(v\) belongs to the complete union of the base packet bands. The true \(r\) is \(\gg_J P/(uv)\ge P^{1-\eta-o(1)}\), larger than both \(\sqrt P\) and \(v\) for sufficiently large \(P\); hence it is uniquely identifiable. Consecutive restrictions on \(v\) consist of just one size cutoff, no artificial separated ranges. One may additionally impose \(P^+(v)\le P^c\) for **any fixed** \(c>0\) (include \(v=1\)); this optional cap can be dropped entirely.

The absolute masses of the genuine high-source signs in (1) are each \(\asymp PV_y(P)\), with \(V_y(P)\asymp S(P)/L^\delta\). Their unmarked **net** sum is
\[
O\bigl(PV_y(P)L^{-2+\theta+2\delta}\bigr),\qquad \theta=.35 .
\tag{2}
\]
If restricted to rows actually covered by the translated first selector at any fixed \(M\ge2\) offsets, the signed mass is
\[
O\bigl(PV_y(P)(L^{-2+\theta+2\delta}+L^{-M/200})\bigr).
\tag{3}
\]
In particular this chamber is paid at \(o(PV_y(P)/L)\) when \(M>200\). Parameter \(-2+\theta+2\delta< -1.45\). All constants may depend on the fixed parameters. For any fixed \(\eta<1/2\), real source windows with \(a,b\) as above exist; for example at \(\eta=.1\) the earlier \(.32,.35\) windows qualify.

The source \(pq\) has both primes \(>P^{1/4}\); its exact smooth high coefficient is \(-\log(pq)\). The true \(m=uvr\) is squarefree and rough, and \(\lambda(m)=-\lambda(v)\) since \(K\) is even. The genuine signed high weight is therefore \(\lambda(v)\log(pq)\). No row is counted twice: \(n\) fixes its smaller prime and its box, \(m\) fixes \(r\), its base-band prime factors fix \(u\), and then \(v\) is fixed.

## 2. A uniform signed reciprocal prefix lemma for the entire cofactor

Let \(\mathcal F\) be the finite excluded prime set consisting of all primes \(\le y\) and all of \(\mathcal B\). The latter have logarithms \(\le2L^{.2}\), and total reciprocal mass \(O_K(1)\). Completely \(\mathcal F\)-smooth integers are those with every prime factor in \(\mathcal F\), allowing arbitrary powers and including 1. Let
\[
F_0(X)=\sum_{\substack{v\le X\\p\mid v\Rightarrow p\notin\mathcal F}}\frac{\mu(v)}v .
\]
Since \(\mu(v)\) already enforces squarefreeness, convolution gives the exact formula
\[
F_0(X)=\sum_{\substack{d\le X\\ d\ \mathcal F\text{-smooth}}}\frac1d
       \sum_{e\le X/d}\frac{\mu(e)}e .
\tag{4}
\]
This follows from multiplying the \(\mu\) Euler factor \(1-\ell^{-s}\) by \(1/(1-\ell^{-s})\) at each forbidden prime, or by checking prime powers on both sides. The standard reciprocal Möbius bound \(\sum_{e\le T}\mu(e)/e=O_A((\log (2T))^{-A})\) follows from the classical zero-free-region PNT, using partial summation and the reciprocal Dirichlet series value zero at 1. Hence
\[
|F_0(X)|\ll \prod_{\ell\in\mathcal F}(1-1/\ell)^{-1}\ll_K L^\delta
\quad(X\ge1).
\tag{5}
\]
For \(X\ge e^{L^\theta}\), \(F_0(X)\ll_A L^{-A}\) for any fixed \(A\). Indeed the \(d\le\sqrt X\) terms in (4) use the arbitrary-log reciprocal Möbius bound uniformly at \(T\ge \sqrt X\), absorbing \(L^\delta\). For the tail use Rankin with \(s=L^{-.25}\):
\[
\sum_{d>\sqrt X,\ d\ \mathcal F\text{-smooth}}d^{-1}
 \le X^{-s/2}\prod_{\ell\in\mathcal F}(1-\ell^{s-1})^{-1}
 \ll_K e^{-\tfrac12 L^{\theta-.25}}L^{O(1)} .
\]
Here \(\ell^s=e^{o(1)}\) uniformly on \(\mathcal F\), so the displayed Euler product is a fixed power of \(L\). These estimates apply with full base packets removed, not just the individual chosen tag-primes of \(u\).

If the optional cap is used, let \(F(X)\) denote the prefix with the extra restriction on primes \(>P^c\). Form the disjoint set \(\mathcal H\) of primes \(>P^c\) up to \(P^\eta\) (ignore larger primes on this range). It is disjoint from \(\mathcal F\) for all sufficiently large \(P\). Its convolution identity is
\[
F(X)=\sum_{\substack{d\le X\\d\ \mathcal H\text{-smooth}}}\frac{F_0(X/d)}d
\qquad(1\le X\le P^\eta).
\tag{6}
\]
Such \(d\) has at most \(\lfloor\eta/c\rfloor\) prime factors with multiplicities. Their full reciprocal mass for \(d\le P^\eta\) is \(O_{c,\eta}(1)\), by the ordered-tuples upper bound and \(\sum_{P^c<\ell\le P^\eta}\ell^{-1}=O_{c,\eta}(1)\). Thus (5) holds for \(F\) as well. If \(X\ge e^{2L^\theta}\), terms \(d\le X e^{-L^\theta}\) are arbitrary-log small by \(F_0\). Every term in the remaining shell has \(d>1\). Order the prime factors, fixing all but the last occurrence (this upper bounds reciprocal weights, even with repetitions). For fixed preceding product \(D\), the last prime lies in
\[
(X e^{-L^\theta}/D,\ X/D]\cap(P^c,P^\eta].
\]
Its reciprocal mass is \(O_{c,\eta}(L^{\theta-1})\), from the usual prime reciprocal asymptotic with arbitrary-log error on endpoints of polynomial size: its actual log width is \(\le L^\theta\), and log lower endpoint is \(\ge cL\). Sum the fixed preceding primes by the same \(O_{c,\eta}(1)\) reciprocal mass. Therefore for both cases (no cap, where simply take \(F=F_0\), or with cap),
\[
|F(X)|\ll L^\delta\quad(X\ge1),\qquad
|F(X)|\ll L^{\theta-1+\delta}\quad(e^{2L^\theta}\le X\le P^\eta).
\tag{7}
\]
This is a theorem on the literal cofactor family, unlike separating low and high cofactors and dropping their boundary.

The unsigned squarefree reciprocal mass \(D_v=\sum_vv^{-1}\) in (1) is \(\asymp L^{1-\delta}\). The upper bound follows from the squarefree product over all allowed primes \(\le P^\eta\). For the lower bound, restrict to a sufficiently small fixed upper exponent \(c_0\le\min(c,\eta)\) (ignore \(c\) if no cap). Before the size cutoff the reciprocal product over \((y,P^{c_0}]\setminus\mathcal B\) is \(\asymp L^{1-\delta}\); its normalized expected \(\log v\) is \(O(c_0 L)\) by independent inclusion with probability \(1/(\ell+1)\). Small \(c_0\) and Markov retain at least half its mass below \(P^\eta\).

## 3. Exact arithmetic model for the weighted source coefficient

Reuse the genuine prime-centered comparison from the earlier verified notes. On each rectangle the actual source coefficient \(\log(pq)\) is obtained by summing the two source branches \(w(x)w(q)/\log x\) and \(w(x)w(q)/\log q\), against a bounded residual in \(h=(P-xq)/u\) only. The residual is \(\lambda(v)\) if \(h=v r\) with \(v\) from (1) and true \(r>P^{1-\eta-\varepsilon_0}\), and zero otherwise, where \(\varepsilon_0>0\) is fixed small enough that \(1-\eta-\varepsilon_0>1/2\). For the unsigned version use its absolute value. The decomposition is unique for \(h\le P\), and the physical \(r\)-cut is automatic because \(u=P^{o(1)}\). The projected comparison applies to both \(\alpha=w-\kappa_z^{-1}R_z\) and \(\alpha/\log x\) by the earlier uniform character estimates and partial summation. Consequently it replaces both source factors by their rough main weights at \(O_A(PL^{-A})\) error per rectangle, while \(r\) remains a **true prime**.

Fix \(a_0=uv\) in the resulting exact Type I model. Its actual last-prime endpoint \(P/a_0\ge P^{1-\eta-o(1)}\) and the moduli \(xd\le P^{b+o(1)}\) leave the strictly positive ordinary BV square-root margin by \(b<(1-\eta)/2\). Here \(d\) is the small squarefree Bonferroni modulus for \(q\)-roughness (depth \(O_A(\log L)\)); for fixed \(a_0\) a rough \(x\) and small \(d\) are determined by their product. An actual solution forces \((x,a_0)=1\) because every prime of \(a_0\) is a target unit. Removing rough \(x\)'s sharing a prime \(>z\) of \(a_0\) costs at most \(O(XL/z+L)\) per rectangle at its shortest coordinate scale \(X\), negligible relative to \(\kappa_z X\); all shared primes \(\le z\) were already excluded by roughness. The progression for each \(xd\) is the actual reduced residue \(r\equiv Pa_0^{-1}\bmod xd\) for \(d\) on primes \(\ell\le z,\ \ell\nmid Pa_0\). Primes dividing \(Pa_0\) cannot divide \(q\) by the equation and \(r>z\).

All amplitude and BV errors in the exact weighted computation are as in the parity-fiber proof: use maximal log-prime counting, partial summation by \((1/\log x+1/\log q)/\log r\), and then the pure-integer rough \(x\) count with partial summation. The local factor is uniformly \(S(P)(1+O(L/y+1/z))\) since every prime of \(a_0\) is \(>y\). The signed error over \(v\) is bounded by the entirely unsigned reciprocal mass \(O(L^{1-\delta})\) times the per-\(a_0\) arbitrary-log shifted endpoint error, as justified before. Thus the actual signed source weight per rectangle is
\[
S(P)\sum_{u,v}\frac{\lambda(v)}{uv}
 \iint_{I_1\times I_2}
 \frac{1/\log x+1/\log q}{\log((P-xq)/(uv))}\,dx\,dq
 +O_A(PL^{-A}).
\tag{8}
\]
The unsigned version has exactly the same formula with \(\lambda(v)\) replaced by 1. All errors are arbitrary-log after choosing sufficiently many, fixed, base packets for one fixed sufficiently large \(A\). The unsigned amplitude is \(\asymp L^{-2}\) uniformly, and \(O(L)\) rectangles of area \(\asymp P\) give total unsigned weight \(\asymp PV_y(P)\).

## 4. Stieltjes summation treats the entire size cutoff and exact \(r\)-logarithm

For each fixed \(u,x,q\) in (8), let \(C=\log((P-xq)/u)\) and \(W(V)=1/(C-\log V)\). Throughout \(1\le V\le P^\eta\), \(W(V)=O(L^{-1})\), \(W'(V)=O(1/(VL^2))\). Partial summation and (7) give
\[
\begin{aligned}
\left|\sum_{v\le P^\eta}\frac{\lambda(v)}v W(v)\right|
&\le |F(P^\eta)|\,O(L^{-1})
     +O(L^{-2})\int_1^{P^\eta}|F(V)|\frac{dV}{V}\\
&\ll L^{-2+\theta+\delta}.
\end{aligned}
\]
The low portion \(1\le V\le e^{2L^\theta}\) uses length \(2L^\theta\) in log-coordinate and bound \(L^\delta\); the long portion has length \(O(L)\) and bound \(L^{\theta-1+\delta}\). No replacement of \(\log r\) by \(L\) or ad hoc partition of the cofactor is involved. The extra \(1/\log x+1/\log q\) is \(O(L^{-1})\) and there are \(O(L)\) rectangles, so (8) gives \(O(P S(P)L^{-2+\theta+\delta})\), which is (2). The genuine two sign masses follow by combining signed and unsigned estimates.

## 5. True translated-cover loss in the larger cofactor range

The natural-scale note's fixed-\(p,u,v\) Selberg argument applies literally when \((p,uv)=1\), which every true row forces even if an allowed \(v\) has a factor \(p\). Ignore the other tuples (they have no rows). The real affine equations and forbidden roots are unchanged. In each \(k\)-interval the support and number \(\le M+2\) of forbidden residues per prime are exactly the same; \(r,q\) still exceed every sieve prime \(W=P^{\rho/40}\). All target primes precede \(W\), and packet classes at primes dividing \(uv\) can be dropped at total factor \(\exp(O_M(L/y))\). The main per \(p,u,v\) still gives the relative \(L^{-M/200}\) savings by the fixed finite choice of greedy witnesses. In the floor error \(P^{.15+o(1)}\), sum over \(\#u=P^{o(1)}\), \(\#v\le P^\eta\), \(\#p\le P^b\); the resulting \(P^{.15+\eta+b+o(1)}\) has exponent \(<.9\), by \(b<(1-\eta)/2\), \(\eta<1/2\). Logs and boxes still fit. The actual uncovered absolute high weight is \(O(PV_y(P)L^{-M/200})\), either by summing log triple weights and dividing within uniform \(L^2\) ratios, or by direct use of \(\sum_{p\in I_1}1/p=O(1/L)\). The actual translated selector assigns one unit of weight to every surviving \(n\); it is not presumed independent of the cofactor. Thus (3) follows.

This covers the entire specified rough cofactor with \(v\le P^\eta\) and optional prime cap, not just a special \(v_1v_2\) rectangle; it still neither removes the fixed base-band occupancy requirement nor bounds the balanced source / intermediate final-prime regions outside ordinary BV.
