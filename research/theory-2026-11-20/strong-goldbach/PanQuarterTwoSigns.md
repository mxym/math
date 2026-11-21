# Signed-shell extension of the two divergent masses to every subquarter split

With the notation \(P,L,I,X,Q=P^v,S(P),B(r),a(r)\) of [the deterministic shell theorem](PanSharpCutoffTwoSigns.md), now fix **any \(0<v<1/4\)**. On the true central reflected-prime row \(p+r=P\), \(p\) prime and \(r\) squarefree composite,
\[
 \sum (\log p)[B(r)]_+\ \gg_v XS(P)\log\log P,\qquad
 \sum (\log p)[-B(r)]_+\ \gg_v XS(P)\log\log P .
\]
Both bounds hold at every sufficiently large even target, also restricted to \(P^-(r)\ge \exp(vL^{2/3})\). They bound separate nonnegative masses, not their signed difference or the prime-pair term. Here, unlike the \(v<1/6\) argument, the intermediate shell sums are signed and the labelled profiles need not be disjoint as sets of \(r\). We do **not** infer that particular inputs have \(|B|>.99\log Q\), or assert the sharper counting corollary of the deterministic calculation above its own rail.

## 1. An elementary uniform signed rough-divisor estimate

Let \(z\to\infty\), \(Q\ge z,\ U=\log Q/\log z\). For \(0\le t\le U\), let \(C_z(t)\) be the sum of \(\mu(k)/k\) on \(k\le z^t,\ P^-(k)>z\), including \(k=1\). Then uniformly
\[
 \sup_{0\le t\le U}|C_z(t)-\rho(t)|\ll U(1/\log z+1/z),       \tag{1}
\]
with \(\rho\) Dickman's function. This is only useful where the right side is small. For a proof take the measures
\(\sigma=\sum_{z<l\le Q}\delta_{\log l/\log z}/l\) (primes) and
\(\nu=1_{[1,U]}dx/x\). Both have mass \(\log U+O(1/\log z)\). The uniform Mertens estimate gives \(\sup_a|(\sigma-\nu)((-\infty,a])|\ll1/\log z\). In the convolution algebra of finite signed measures,
\[
 \exp_*(-\sigma)-\exp_*(-\nu)
 =(\nu-\sigma)*\int_0^1\exp_*(-[(1-b)\sigma+b\nu])\,db .
\]
The second factor has total variation \(O(U)\). Convolution against it multiplies the preceding supremum norm for cumulative masses by at most that variation. Replacing \(\exp_*(-\sigma)\) by the squarefree convolution product \(\prod_{z<l\le Q}^{*}(\delta_0-\delta_{\log l/\log z}/l)\) costs \(O(U/z)\) in total variation: telescope the local difference of size \(O(l^{-2})\) and bound every other exponential or two-term factor by \(e^{1/l}\). The product has cumulative masses \(C_z(t)\). Those of \(\exp_*(-\nu)\) through \(t\le U\) are exactly the alternating simplex series for \(\rho(t)\), since every coordinate is at least 1; cf. its explicit differentiation proof in [the global rough transfer, §3](PanGlobalRoughTransfer.md).

We will need \(C_z\) with \(1/\phi(k)\) in place of \(1/k\) and \((k,PM)=1\) for \(M\ll P\). The same telescoping replaces each prime coefficient \(1/l\) by \(1/(l-1)\) at cost \(O(U/z)\), or by zero when \(l\mid PM\) at cost \(O(UL/z)\). These costs are absolute total-variation bounds. For the resulting measure we may therefore use \(\rho(t)\) with uniform cumulative error \(E=O(U/\log z+UL/z)\). In particular a multiplier \(\log k/\log Q\in[0,1]\) introduces at most \(2E\) in integrating on a subinterval \([0,t]\), by parts. The continuous normalized log integral is \(U^{-1}\int_{[0,t]}x\,d\rho(x)\), where the initial unit atom is at zero. Its absolute magnitude is \(O(1/U)\): use \(t\rho(t)-\int_0^t\rho(x)\,dx\), \(\rho(t)\le1/\lfloor t\rfloor!\), and \(\int_0^\infty\rho(x)dx=e^\gamma\).

## 2. The near-wall term versus every proper subset

Fix \(\eta>0\) with \(2v+\eta<1/2\), and choose \(y_0=y_0(v,\eta)>0\) sufficiently small, in particular below .005. For each dyadic \(L^{-1/3}\le y=2^{-j}\le y_0\) use the one-label and two-label products \(M\) of the deterministic shell theorem, so \(1-\log M/\log Q\in[y,2y)\); the two factors, when present, have exponents in \([.40,.43]\) and \((.56,.61)\). Let \(z=Q^{2y}\), \(U=1/(2y)\). The label weight \(W_y^{(i)}(r)\) is the number of such unit products \(M\mid r\) of type \(i\), times \(1_{P^-(r)>z}\). There is **no other sieve on \(r\)**. The harmonic mass \(H_y=\sum_M1/\phi(M)\asymp y\) uniformly for either type, as proved in the deterministic theorem (Mertens error \(O_v(L^{-1})=o(y)\)). We may omit \(p\mid P\) with negligible error.

In \(B(r)\), write \(d=e k\) with \(e\mid M,\ (k,M)=1\), since only squarefree divisors occur. With \(M\mid r\), rough \(r\), only rough \(k\) coprime to \(P\) matter. The unsigned physical count for each fixed \(M,k\) is sandwiched before inserting the Möbius sign, using upper/lower dimension-one fundamental-lemma sieves at level \(D=P^\eta\) for \(r\) at the primes \(\le z\) not dividing \(P\). The sieve product is
\[
 V=(1+o(1))S(P)e^{-\gamma}/\log z
\]
uniformly since \(z\ge \exp(2v L^{2/3})\); the density is \(1/(l-1)\) at the allowed small prime \(l\). The relative error is \(O(s^{-s/2})\) uniformly for sufficiently large \(s=\log D/\log z=(\eta/v)U\), by [the fundamental lemma in Kurlberg–Lester–Rosenzweig, §2.1, Theorem 2.2](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136); take \(y_0\) so that \(s\) is always large. The sieve dimension bound is uniform by the full prime product. All progression moduli \(Mk b\), \(b\le D\) a sieve divisor, lie below \(P^{2v+\eta}\); each gives the unit residue \(P\bmod Mkb\). A modulus has at most \(O(\tau(q)^4)\) choices of the labels and decomposition: choose \(M\), which determines the shell and \(z\), then \(e\mid M\), and the rough/small split of \(q/M\) determines \(k,b\). The \(O(L)\) physical log-divisor weights and all of those multiplicities are harmless in weighted maximal BV, just as in §2 of the deterministic theorem. Consequently all accumulated absolute arithmetic remainders are \(O_A(PL^{-A})\), even on summing over shells and types; the cruder use per shell also suffices. The same strict power margin handles removal of prime powers from the log-prime version. The total harmonic mass \(\sum_{k\le Q,\ k\ {\rm rough}}\mu^2(k)/\phi(k)\ll U\) by Mertens, so for each \(M\) the relative fundamental-lemma error in the bracket below is \(O(U s^{-s/2})\).

More precisely the signed \(B\)-sum with prime log weight in one shell is, up to the preceding BV error,
\[
 X V\log Q \sum_M\frac{1}{\phi(M)}
 \left\{\sum_{e\mid M}\mu(e)\,T_e+O(U s^{-s/2})\right\},\qquad
 T_e=-\sum_{\substack{k\le Q/e,\ (k,PM)=1\\ P^-(k)>z}}
  \frac{\mu(k)}{\phi(k)}\frac{\log(e k)}{\log Q}.
\]
For \(e=M\), \(Q/M\le z\), so **only \(k=1\)** occurs and \(T_M=-\log M/\log Q\). In particular \(|T_M|>.99\). For every proper \(e\mid M\), \(\log e/\log Q\le.61\); the endpoint \(t_e=\log(Q/e)/\log z\ge.39U\). By §1,
\[
 |T_e|\ll U^{-1}+\rho(.39U)+U/\log z+UL/z .
\]
Here \(U/\log z=O_v(L^{-1/3})\) uniformly since \(y\ge L^{-1/3}\). Take \(y_0\) small, then \(P\) large, so that all at most three proper terms and the sieve error together have size \(<.2\) uniformly. Therefore the bracket has absolute value \(\ge.79\), with sign \(-\mu(M)\): positive for a singleton, negative for a pair. Since \(XV\log Q\,H_y\asymp XS(P)\) for both types, each signed shell sum exceeds \(c_v XS(P)\) in the stated direction.

## 3. From labelled sums to actual positive and negative parts

For a given physical \(r\le P\) all possible prime labels exceed \(Q^{.4}\), so their number is \(O_v(1)\). Each product \(M\) can appear in only one half-open shell. Thus \(0\le\sum_y W_y^{(i)}(r)\le C_v\) for a fixed constant, for both types independently; no assumption that different products give different \(r\) is made. Every counted \(r\) is composite since it has a nontrivial divisor below \(Q\) and belongs to \(I\). Removing squareful \(r\) loses at most \(o(P)\) even in the signed sums across all shells: their count is \(O(P e^{-2vL^{2/3}})\), while \(|B(r)|\le L\tau(r)\) and \(\sum_{r\le P}\tau(r)^2\ll P L^3\); apply Cauchy–Schwarz, the bounded label multiplicity and \(\log p\le L\). No maximal-order divisor bound is required. On the remaining inputs \(a(r)=B(r)\) and the asymmetric \(a^*(r)\) agrees as before. Hence the separate signed sums over \(\gg\log L\) shells, divided by \(C_v\), lower-bound the corresponding positive or negative physical mass. This proves the assertions. In particular, discarding one of two divergent unsigned masses cannot establish a main-term-scale one-sided bound. It does not exclude using their **actual signed cancellation**, which is essential.

For background on classical sharp-cutoff or isolated-divisor phenomena and the precise distinctions see the comparison in [the deterministic note](PanSharpCutoffTwoSigns.md), including [Granville–Koukoulopoulos–Maynard §1.1](https://arxiv.org/pdf/1606.06781). The crucial additional rail here is \(Q^2D<P^{1/2}\); extrapolating this calculation even to \(v=1/4\), let alone \(v=1/2\), would leave the invoked BV theorem.

The recent [Pham boundary-correlation study](https://www.preprints.org/manuscript/202610.3061) treats a different absolute-majorant obstruction and a different short-divisor model. This signed shell transfer extends the preceding physical Pan obstruction, not an upper bound for the actual unsigned parts or a proof of how they cancel.
