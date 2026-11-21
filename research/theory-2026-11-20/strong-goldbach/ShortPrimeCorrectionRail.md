# A short prime correction on a prescribed Goldbach rail

Write \(R_2(n)=\#\{(p,p'):p+p'=n\}\) with ordered primes, and
\[
 K=K_Q(N)=\prod_{\ell>2,\ \ell\mid(Q,N)}(\ell-1)/(\ell-2).
\]
Fix \(\epsilon>0\). For every sufficiently large **individual even** \(N=X\), every even \(Q\), and every real \(M\) with
\[
             X^{\alpha+\epsilon}\le M,\qquad H=QM\le X/100,                 \tag{1}
\]
there are \(\gg_\epsilon M/\log M\) distinct primes \(r\in[M,2M]\) for which
\[
                       R_2(N-Qr)\gg_\epsilon K X/\log^2 X.                 \tag{2}
\]
Here \(\alpha=1/7\) for arbitrary \(Q\), and \(\alpha=2/15\) when \(P^+(Q)\le(\log X)^B\), for any fixed \(B\) (then constants may depend on \(B\)). These ranges use the [OpenAI preprint, Theorem 1.1, September 2026](https://github.com/openai/math/tree/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026) as the stated uniform Dirichlet zero-free half-plane, together with [Chen–Gupta–Li, Theorem 1.2, July 2026 revision](https://arxiv.org/pdf/2507.08296). **The general and large-radical smooth cases are conditional on the September all-Dirichlet zero-free claim, which is not independently audited here.** For even \(Q\) with \(\operatorname{rad}(Q)\le(\log X)^B\), including dyadic \(Q\), \(\alpha=2/15\) follows from the CGL density estimate together with classical zero-free input, without that September claim; a fully classical \(1/6\) range is also given below. All three primes can be taken distinct, and the two summands of \(N-Qr\) can be taken, respectively, in \([.24X,.32X]\) and \([.66X,.77X]\).

For example let \(Q=\mathop{\rm lcm}(1,\ldots,\lfloor\frac12\log X\rfloor)\). The prime number theorem gives \(Q=X^{1/2+o(1)}\). Under the stated September zero-free input, taking \(M=X^{2/15+\epsilon}\) produces \(\gg M/\log M\) richly represented centers *below* \(N\), with distance \(Qr\le X^{19/30+\epsilon+o(1)}\), **each** preserving every test \(j\mid N-x\) for every integer \(x\) and every \(j\le \tfrac12\log X\). More generally one can preserve chosen prime-factor-graph divisibility tests for every modulus dividing \(Q\), for input vertices still below the new center (in particular for all inputs below \(N-2H\)), including an exact valuation \(v_\ell(N-x)=b\) whenever \(\ell^{b+1}\mid Q\). The number and choice of tests do not affect the estimates. Without the September input, take instead \(Q\) to be the product of \(\operatorname{lcm}(1,\dots,\lfloor c\log\log X\rfloor)\) and a suitable power of 2 so that \(Q\asymp X^{1/2}\). Then the classical \(1/6\) version preserves every divisor up to \(c\log\log X\) at distances \(O(X^{2/3+\epsilon})\).

This is a ternary prime theorem with a short, prescribed-coefficient correction, and a limitation on a purely congruential certificate of binary failure. It neither permits \(r=0\) nor proves \(R_2(N)>0\). The primality of the correction quotient and rich representations in (2) are not consequences of *least* Goldbach occupancy in a residue class.

## Smoothed short progression variance

Put \(L=\log X,\ h=H/X\). Fix real \(w\ge0\) smooth, supported in \((-1/20,1/20)\), positive near zero, and set \(w_y(t)=w(h^{-1}\log(t/y))\). For \(|v|\le P=L^{40}\) define
\[
 F_y(a,v)=\sum_{p\equiv a\bmod m}(\log p)w_y(p)e(vp/H),\quad
 I_y(v)=\int_0^\infty w_y(t)e(vt/H)\,dt,\qquad e(z)=e^{2\pi iz}.
\]
For \(m=Qd,\ d\le P\), and every fixed \(A\),
\[
 \int_{X/5}^{4X/5}\sup_{|v|\le P}
   \sum_{a\in U_m}|F_y(a,v)-I_y(v)/\phi(m)|^2\,dy
        \ll_A XH^2\phi(m)^{-1} L^{-A}.                                    \tag{3}
\]
All implied constants hereafter can depend on the fixed margin and on smooth weights. No pointwise prime number theorem in every individual short interval is asserted.

Here are details of (3), in particular of the time averaging. Remove the common phase \(e(vy/H)\), put \(s=vy/X\), and use the fixed-in-\(y\) character kernel \(w(u)e(s(e^{hu}-1)/h)\), where \(u=\log(t/y)/h\). The Mellin transform at \(\rho\) is \(y^\rho b(\rho)\) with
\[
 |b(\beta+i\gamma)|\ll_J h(1+P)^J(1+h|\gamma|)^{-J},\quad 0\le\beta\le1. \tag{4}
\]
The same bound holds after one \(s\)-derivative, since \((e^{hu}-1)/h\) and all needed \(u\)-derivatives are uniformly bounded on the support. It follows by integration by parts in \(u\). Use character orthogonality, first with \(\Lambda\). For the inducing primitive \(L\)-function the smooth explicit formula is its principal main integral (if principal) minus \(\sum_\rho y^\rho b(\rho)\), up to \(O(L^{O(1)})\), also for the differentiated kernel. Indeed Mellin inversion of \(-L'/L\) gives the nontrivial zero residues, the pole and the trivial zero residues \(O(\sum_{j\ge0} h(cX)^{-j})\); the smooth support stays in \(t>1\). The imprimitive discarded prime powers over primes dividing \(m\) cost \(O(L^2)\) per character. In passing from \(\Lambda\) to primes alone, the contribution per character is \(O(L^2(1+H/\sqrt X))\): for each exponent \(e\ge2\) the interval of possible bases has length \(O(H/\sqrt X)\), and \(e=O(L)\). These errors are negligible in the summed variance since \(m\ll QP,\ Q/H^2\le1/(HM)\) and \(Q/X\ll1/M\).

To bound the integrated squared zero sum, majorize the indicator of the \(y\)-interval by a fixed smooth function of \(y/X\), supported in \([1/10,1]\). Its Mellin kernel between zeros at heights \(\gamma,\gamma'\) is \(O(X^{1+\beta+\beta'}(1+|\gamma-\gamma'|)^{-2})\). For each individual character a unit height interval has \(O(\log(2m(|t|+2)))\) zeros. Thus \(2ab\le a^2+b^2\), (4), and summation over heights bound the integral, summed over characters and divided by \(XH^2\), by
\[
 \ll_J (1+P)^{2J}\sum_{\chi\bmod m}\sum_{\rho_{\chi^*}}
    X^{-2(1-\beta)}(1+h|\gamma|)^{-2J}\log(2m(|\gamma|+2)).                \tag{5}
\]
The principal zero set is included. To pass from fixed \(s\) to the supremum use the one-variable Sobolev bound on \([-P,P]\) with the integral of \(|f|^2+|f'|^2\) (extend by one unit, or use the local interval version); after summing this costs at most \(O(P+1)\) on the right, not a power of \(X\). Orthogonality divides the character sum by \(\phi(m)\).

Take \(T=X^\eta/h\) with a sufficiently small fixed \(\eta>0\) depending on \(\epsilon\). Above \(T\), ordinary zero counts and dyadic summation give \(O(mT L^{O_J(1)}X^{-2J\eta})\) in (5) for the tail, with \(J\) fixed sufficiently large. Below \(T\), \(mT=dX^{1+\eta}/M\). Chen–Gupta–Li's fixed-modulus density bound is \((mT)^{C(1-\sigma)+o(1)}\), where \(C=7/3\) in general and \(C=30/13\) if \(m\) is \(T\)-smooth. In the second regime here \(P^+(m)\le\max(L^B,P)<T\). It counts the nontrivial zeros for *all* characters mod \(m\). By (1), \(C\log(mT)\le (2-c_\epsilon)L\); the uniform half-plane gives \(1-\beta\ge1/8\). Partitioning \(\beta\) into intervals of length \(1/L\), for \(\beta\ge1/2\) the sum in (5) is \(O(X^{-c'_\epsilon})\) before logarithmic factors. For \(\beta<1/2\), trivially \(mT X^{-1}L^{O(1)}\ll X^{-c_\epsilon''}\). This proves (3), including all logarithmic factors, after \(\eta,J\) are fixed. The exponent \(2\) multiplying \(1-\beta\) in (5) comes from the squared Möbius-free prime sum *and integration over slab centers*. Bounding the zeros separately before averaging in \(y\) would generally lose a factor \(1/h\).

## The scaled circle integral

Take \(y\in [X/4,3X/10]\), \(z=N-y-\tfrac32H\). Both are in the interval of (3), and \(dy=-dz\). Let \(\psi\ge0\) be smooth supported inside \((1,2)\), equal to 1 on \([1.3,1.7]\). For this slab count \(p+p'+Qr=N\) with the three log weights times \(w_y(p)w_z(p')\psi(r/M)\). Fourier inversion uses \(S_y(\alpha) S_z(\alpha) C(Q\alpha)e(-N\alpha)\), integrated over \([0,1]\), where the first two factors are the prime sums of the windows and \(C(b)=\sum_r(\log r)\psi(r/M)e(rb)\) over primes. Here and below integrals in \(y\) are unnormalized.

The major arcs are in \(b=Q\alpha\bmod 1\), not \(\alpha\): \(b=k/d+v/M,\ (k,d)=1,\ d\le P,\ |v|\le P\). They are disjoint for \(M>2P^3\), interpreting boundary arcs on the circle. Elsewhere the Vinogradov–Vaughan minor-arc bound gives \(|C(b)|\ll M L^{-12}\). In detail Dirichlet approximation with denominator bound \(\lceil M/P\rceil\) has \(P<d'\le 2M/P,\ |b-k'/d'|\le1/(d')^2\) off these arcs. Apply the [exponential sum estimate in Montgomery–Vaughan, §17.2](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf) and partial summation to the smooth prime weight; \(M^{-1/5}\) and prime-power terms are negligible. By Parseval and Cauchy the total error from these arcs for each \(y\) is \(O(MH L^{-10})\): the individual \(\int|S_y|^2,\int|S_z|^2\ll HL^2\). This uses no short-interval prime asymptotic.

The \(Q\) lifts of each \(b\) average exactly to \(1_{p+p'\equiv N\bmod Q}\). On a major arc, the resulting long-prime factor is
\[
e(-Nv/H)
\sum_{\substack{a,a'\in U_{Qd}\\a+a'=N\bmod Q}}
 e\!\left({k(a+a'-N)\over Qd}\right) F_y(a,v)F_z(a',v),                  \tag{6}
\]
where the exponential is well-defined on representatives. There are no omitted nonunit primes: if a prime divisor of \(Qd\) is in a chosen window then it divides \(Q\) or \(d\), whereas \(Q<X/(100M),\,d\le P\), both smaller than the window primes. The coefficient matrix in (6) has \(\ell^2\)-operator norm at most \(d\) (at most \(d\) nonzeros of modulus one in any row or column). Replace \(F_y,F_z\) by the constant vectors \(I_y/\phi(Qd),I_z/\phi(Qd)\). Their \(\ell^2\)-norms are \(O(H/\sqrt{\phi(Qd)})\). By (3), Cauchy in \(y\) (also for the translated \(z\)) gives total integrated absolute error
\[
      \ll_A Xd H^2 L^{-A}/\phi(Qd).
\]
This bound covers the two cross terms and the product of the two errors. Even with the trivial \(M L\) bound on \(C\), summing over \(\le P^2\) arcs of length \(2P/M\), the total is \(o(XHM)\), since \(d/\phi(Qd)\ll L^{O(1)}/Q\) and \(A\) is arbitrary. This is the necessary *post-lift* estimate; multiplying separate additive twist errors by \(Q\) would not suffice.

For the small prime sum the ordinary Siegel–Walfisz theorem up to \(d\le P\) and partial summation give
\[
 C(k/d+v/M)= M\frac{\mu(d)}{\phi(d)} J(v)+O_A(ML^{-A}),\quad
                  J(v)=\int \psi(t)e(vt)\,dt
\]
uniformly on these major arcs. Here \(M\ge X^{\alpha+\epsilon}\). Replacing \(C\) in the already projected main expression costs \(o(XHM)\) by the same polynomial-log accounting. Now \(db=dv/M\).

Put \(B_Q=\#\{a\bmod Q:(a(N-a),Q)=1\}\), positive for even \(Q,N\). The normalized arithmetic coefficient after summing \(k\) at level \(d\) is zero for nonsquarefree \(d\). It is also zero when \((d,Q)>1\): for \(\ell\mid(d,Q)\), shifting \(a\) by \(Qd/\ell\) permutes the allowed pairs in (6) and rotates its phase nontrivially. For squarefree \(d\) coprime to \(Q\), CRT gives the coefficient
\[
              {B_Q\over\phi(Q)^2}\,{\mu(d)^3 c_d(N)\over\phi(d)^3},          \tag{7}
\]
where \(c_d\) denotes the Ramanujan sum. Indeed the \(Q\)-part counts \(B_Q\) choices, while the \(d\)-part separates into two unit sums each equal to \(\mu(d)\), times \(e(-kN\overline Q/d)\); summing over reduced \(k\) produces \(c_d(N)\). Therefore the extended singular series is
\[
 {B_Q\over\phi(Q)^2}\prod_{\ell\nmid Q}
       \left(1-\frac{c_\ell(N)}{(\ell-1)^3}\right)\asymp K/Q.               \tag{8}
\]
The omitted tail after \(d>P\) is \(o(B_Q/\phi(Q)^2)\) uniformly because \(|c_d(N)|\le\phi(d)\) and \(\sum_{d>P}\phi(d)^{-2}=o(1)\). The displayed Euler product is between absolute positive constants since \(2\mid Q\). For the prefactor, \(QB_Q/\phi(Q)^2\) is the product of \(\ell/(\ell-1)\) over \(\ell|(Q,N)\) and \(\ell(\ell-2)/(\ell-1)^2\) over \(\ell|Q,\ell\nmid N\). This is comparable to \(K\), including when \(K\) grows.

The real factor is
\[
 \int_{\mathbb R} I_y(v)I_z(v)e(-Nv/H)J(v)\,dv
     =\iint w_y(t)w_z(t')\psi((N-t-t')/H)\,dt\,dt'\asymp H^2.            \tag{9}
\]
This follows by Fourier inversion and \(y+z=N-\frac32H\); on the supports the argument of \(\psi\) lies in \([1.3,1.7]\). Replacing \(|v|\le P\) by the full line is valid uniformly since \(|I_y|+|I_z|\ll H\) and \(J\) is rapidly decreasing. Summing (7) absolutely makes this error \(o(KH^2/Q)\) per slab. Combining (6)–(9), the minor arcs, and integration over \(y\) gives a positive lower bound \(\gg X K H^2/Q\) for the integrated weighted triple count. Each actual triple contributes its log weights times at most \(O(H)\) to that integral: fixing \(p\) restricts the center \(y\) to an interval of length \(O(H)\). Thus
\[
 \sum_{\substack{M\le r\le2M\\r\ {\rm prime}}}(\log r) R^*_w(N-Qr)
                            \gg K X M,                                    \tag{10}
\]
where \(R^*_w\) counts pairs in the two stated disjoint summand intervals, with weights \(\log p\log p'\). Also \(2M\le X/100\), so the third prime is different from both summands.

## Rich centers rather than just a count of triples

The [dimension-two Selberg upper sieve for binary representations](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/) gives \(R^*_w(n)\ll X\prod_{\ell\mid n,\ \ell>2}(\ell-1)/(\ell-2)\) on the indicated range. Let \(G_r\) denote the product with the primes dividing \(Q\) omitted, so the full product for \(N-Qr\) is exactly \(K G_r\). Uniformly in (1),
\[
                   \sum_{M\le r\le2M,\ r\ {\rm prime}}(\log r)G_r^2\ll M. \tag{11}
\]
Here are the details that keep the estimate valid on **prime** indices. The \(O(\log X/\log M)=O(1)\) primes \(r\mid N\) each have \(G_r\ll L^{O(1)}\) by the Euler product, hence contribute negligibly. Otherwise expand \(G_r^2\) into squarefree \(d\mid N-Qr,\ (d,Q)=1\) with positive multiplicative weights \(g(\ell)=((\ell-1)/(\ell-2))^2-1\ll1/\ell\) on odd primes. For these \(r\), \((d,N)=1\). For \(d\le\sqrt M\) the class \(r=N\overline Q\bmod d\) is reduced and Brun–Titchmarsh bounds its log-weighted prime count by \(O(M/\phi(d))\); \(d=1\) uses Chebyshev. The sum of \(g(d)/\phi(d)\) converges. For \(d>\sqrt M\) the trivial progression count is \(\ll (M/d+1)L\); use \(g(d)\ll d^{-1+o(1)}\) and \(\sum_{d\le X}g(d)\ll L^{O(1)}\). This proves (11). In (10) the \(r\) with \(R^*_w<cKX\) contribute \(O(cKXM)\) by Chebyshev; the second moment bound from (11) and Cauchy give total \(\log r\)-mass \(\gg M\) on the rest. Division by \((\log X)^2\) proves (2).

## Classical fallback and related results

For even \(Q\) with \(\operatorname{rad}(Q)\le L^B\), the same theorem with \(\alpha=1/6\) requires neither 2026 input. For all \(d\le P\), the radical of \(Qd\) is at most \(L^BP\). [Iwaniec's Theorem 2, stated also as Harman–Kátai Lemma 5](https://www.impan.pl/shop/en/publication/transaction/download/product/82101) gives a zero-free margin \(\gg (L\log L)^{-3/4}\) up to the polynomial height \(T\), except for one possible real character and real zero. A primitive real conductor dividing \(Qd\) is at most \(4\operatorname{rad}(Qd)\) by the quadratic-conductor classification; Siegel's theorem \(1-\beta\gg_\nu (4 L^BP)^{-\nu}\), with a sufficiently small fixed \(\nu\), gives the same usable margin. Use the log-free fixed-modulus density estimate in [Thorner–Zaman Theorem 2.1](https://arxiv.org/pdf/2108.10878) with \(C=12/5+\delta\), \(\delta>0\) sufficiently small. Partial summation or the \(1/L\)-bins in (5) now give a saving \(\exp(-cL^{1/4}(\log L)^{-3/4})\), more than every fixed log power. The remainder of the proof is unchanged. Still for these polylogarithmic-radical \(Q\), the exponent can be reduced to \(\alpha=2/15\) using CGL v2 but **without** the September zero-free input. Use CGL's \(T\)-smooth estimate on \(1/2\le\beta\le4/5\); its \((mT)^{o(1)}\) loss is absorbed by the fixed margin since \(1-\beta\ge1/5\). For the remaining bins use [Jutila's fixed-modulus log-free theorem, Theorem 1](https://doi.org/10.7146/math.scand.a-11701), \(\sum_{\chi\bmod m}N(\sigma,T,\chi)\ll_\nu(mT)^{(2+\nu)(1-\sigma)}\) for \(4/5\le\sigma\le1\), explicitly recorded in [Heath-Brown, §6](https://ora.ox.ac.uk/objects/uuid%3Ab63b8b4f-ad21-4de4-a86b-c82fdfc87997/files/m23439806c997d19e6ad333ac00b75a12). With the same classical small-radical zero-free margin, these bins give more than every fixed log saving in (5). Neither small-radical fallback covers all polynomial-size moduli of small largest prime factor, since their radical need not be small.

[Liu–Tsang](https://www.impan.pl/shop/en/publication/transaction/download/product/83231) treat ternary prime equations with general coefficients under different coefficient-size hypotheses. [Jutila's least Goldbach problem and Chen–Gupta–Li Corollary 1.3](https://arxiv.org/pdf/2507.08296) concern least occupancies, not a short prime correction and a positive proportion of rich prime indices for each fixed target. [Anderson's 2-adic restricted Goldbach preprint](https://www.preprints.org/manuscript/202604.0599) studies restrictions on a *summand*. The [post-September least-occupancy corollary](https://zeta.teal-sea.com/read/hunts/qrh_linnik/RESULTS.html) also concerns least occupancy, conditional on the September input. Ordinary exceptional-set bounds alone do not give (2) on these sparse rails. The proof above uses an extra independent prime variable; its minor-arc saving disappears if that variable is fixed to zero. No priority or binary Goldbach resolution is asserted.

[Exact finite CRT control](check_short_prime_correction_rail.py) checks (7) against direct enumeration in 6,080 cases. It checks the local algebra, not a zero-density or circle-method estimate.
