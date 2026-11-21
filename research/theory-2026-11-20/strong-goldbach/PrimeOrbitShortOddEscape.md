# Small shifts with no large odd prime factor, and short escape paths

Write \({\rm core}(n)=\prod_{v_\ell(n)\ {\rm odd}}\ell\) for the squarefree part (not the radical), and \(N_F=\prod_{\ell\in F}\ell^{v_\ell(N)}\). Put \(L=\log\log N\). Call a positive shift \(h\le Z\) exceptional if every prime factor of \({\rm core}(N-h)\) is at most \(Y\); a square complement qualifies. All assertions are for sufficiently large integers.

1. For absolute constants \(c,\eta>0\), at **every** \(N\) at most two shifts \(h\le Z=(\log N)^\eta\) are exceptional at \(Y=cL\). If \(N=d z^2\), \(d\) fixed positive squarefree, at most one is exceptional, with the same constants after reducing them absolutely and a threshold depending on \(d\).
2. Fix a nonempty finite set of primes \(F\) and \(0<\delta\le1\). If \(\log N_F\ge(\log N)^\delta\), there is at most one exceptional shift even up to \(Z=\exp((\log N)^{\delta/2})\), at \(Y=c_\delta L\) with \(c_\delta>0\). There is no fixed-squareclass assumption here. The threshold may depend on \(F,\delta\).

These are assertions about integers, not distributional assumptions on primes. Their graph consequence below is pointwise. Neither large squarefree prime factors nor short paths to them are themselves Goldbach endpoints.

## Proof for three shifts and for square classes

For distinct exceptional shifts \(h_i\) the product \(\prod(N-h_i)=D u^2\) has squarefree \(D\) with \(\log D\le\sum_{\ell\le Y}\log\ell\ll Y\); there is only one copy of each prime in \(D\), regardless of even factors or cancellations. For three shifts apply [Bérczes–Bugeaud–Győry–Mello–Ostafe–Sha, Theorem 2.1(i), equation (2.8)](https://arxiv.org/pdf/2310.09704) to \(f(T)=\prod(T-h_i)\), \(T=N\), over \(\mathbb Q\) with only the infinite place. The polynomial has three simple roots; all three LeVeque indices are two. In the fixed-squareclass case use just two different positive shifts in \(f(T)=\prod(dT^2-h_i)\), \(T=z\), with four simple roots. In these cases (2.8) gives
\[
 \log\log T\le80r^4\log(16r^3)+50r^4\log H(f)+16r^3\log D
\]
for \(r=3,4\) respectively. Here \(\log H(f)\le3\log(1+Z)\) or \(2\log(d+Z)\). For fixed \(d\), \(\log\log z=L+O(1)\). Choosing \(c,\eta\) sufficiently small proves 1.

## Two shifts when the center has a large fixed-prime part

In fact two exceptional shifts \(1\le a<b\le Z\le N/2\) give, when \(D={\rm core}((N-a)(N-b))>1\),
\[
 \log N_F\ \ll_F (1+L)\exp(CY)(1+\log(2Z))                         \tag{1}
\]
with an absolute \(C\). If \(D=1\), direct difference of squares gives \(N\ll Z^2\), already impossible in either stated window.

Write \((N-a)(N-b)=D u^2\). With \(t=2N-a-b\) one has \(t^2-4Du^2=(a-b)^2\), which proves the \(D=1\) assertion by \(t+2u\le(a-b)^2\) (the other positive integer factor is at least one). For \(D>1\), \(\beta=t+2u\sqrt D\) is a positive algebraic integer with conjugate \((a-b)^2/\beta>0\) in \(K=\mathbb Q(\sqrt D)\); \(1<\beta<4N\). Let \(\xi>1\) be the fundamental positive Pell unit in \(\mathbb Z[\sqrt D]\), of norm \(+1\). The standard Hua regulator bound
\[
 \log(2\sqrt D)<R=\log\xi<\sqrt D(\log(4D)+2)
\]
is recorded by [Lenstra, *Solving the Pell Equation*, p. 185](https://e-l.unifi.it/pluginfile.php/881250/mod_resource/content/1/fea-lenstra.pdf). In particular \(R\le\exp(C_1Y)\). Choose \(n=\lfloor\log\beta/R\rfloor\ge0\); \(1\le\beta_0=\beta\xi^{-n}<\xi\), \(n\ll\log N\). As \(\beta_0\) is integral and its conjugate is \((a-b)^2/\beta_0\), its absolute logarithmic height is \(O(R+\log(2Z))\).

In \(K'=\mathbb Q(\sqrt D,\sqrt{ab})\), use \(\gamma_\pm=-a-b\pm2\sqrt{ab}\). Both are strictly negative in the indicated real embedding and their product is \((a-b)^2\). This also works if \(ab\) is a square. The exact factorization is
\[
   4\beta N=(\beta-\gamma_+)(\beta-\gamma_-).
\]
At any prime ideal above a fixed \(\ell\in F\), the nonnegative valuations of \(\beta,\gamma_\pm\) are \(O_F(\log(2Z))\): each divides \((a-b)^2\) in the ring of integers, from the displayed conjugate/product identities. Unequal valuations of \(\beta,\gamma\) therefore give \({\rm ord}(\beta-\gamma)=O_F(\log(2Z))\). For equal valuations put \(\alpha=\beta_0/\gamma\); it and \(\xi\) are local units, \(\alpha\xi^n-1\ne0\) by the opposite real signs, and \(h(\alpha)\ll R+\log(2Z)\) since \(h(\gamma)\ll\log(2Z)\). For this place one may adjoin \(\zeta_3\) if \(\ell=2\), or \(i\) if \(\ell\) is odd, so [Yu, *p-adic logarithmic forms and group varieties II*, Theorem 1, (1.2), (1.8)–(1.10)](https://bibliotekanauki.pl/articles/1390501.pdf) applies in degree \(\le8\). Take \(B=\max(n,3)\). The degrees, \(e,f\) and number of bases are bounded, and \(\ell\in F\) is fixed; hence the constant is uniform in \(a,b,D,N\). Multiplicative independence is not required in Theorem 1. We obtain
\[
 {\rm ord}(\beta-\gamma)
 \ \le {\rm ord}(\gamma)+O_F\big((1+R)(1+R+\log(2Z))\log(3+n)\big).
\]
The zero exponent \(n=0\) can be omitted, using the one-base case. Summing the two factors above each \(\ell\) and then over \(F\), and using \(\log(3+n)\ll1+L\), proves (1). Now take \(Z=\exp((\log N)^{\delta/2})\), \(Y=c_\delta L\) with \(Cc_\delta<\delta/4\); (1) contradicts \(\log N_F\ge(\log N)^\delta\). This proves 2.

## A short pointwise path with a precise exceptional configuration

For even \(N\) draw the edge \(x\to y\) on odd unit prime vertices \(x<N-1\) if \(v_y(N-x)\) is odd. A vertex with prime complement is a genuine endpoint and a path may stop there immediately. Let \(\chi\) be a quadratic character of \((\mathbb Z/2N)^\times\) trivial on \(N-1\); retain \(x\) if \(\chi(x)=-1\). From any retained vertex there is a retained odd successor: \(N-x\equiv(N-1)x\bmod 2N\) and multiplicativity give an odd number of retained odd successors. In particular a square-complement row cannot be retained. No vertex has a loop, since it is a unit modulo \(N\). All successors are still odd unit primes less than \(N-1\).

At any sufficiently large even \(N\), from **each** retained \(x\le Y\) either an odd path of at most three edges reaches a genuine endpoint or a vertex \(>Y\), or \(x\) itself belongs to a closed two-vertex odd cycle whose vertices are both retained and whose two complementary rows are composite. Closed here is only for odd valuations: factors of even multiplicity remain unconstrained.

Indeed a small nonexceptional row has a direct edge out of the small range. If the claimed short escape and endpoint both fail, the starting row \(x\) is exceptional. Take any retained successor \(y\); it must be small and exceptional, and \(x\ne y\). They consume the entire two-row budget. Any successor \(z\) of \(x\) or \(y\) outside that pair is either large, an endpoint, or a third small row which exits by one further edge; this would take at most three edges from \(x\). Thus \(x,y\) have only each other as odd successors, and are not endpoints. In the three-edge alternative no character restriction is imposed on the last two vertices; one can take the first internal vertex retained in a path of length three (start with \(x\to y\)). Genuine Pell examples, including an infinite family with the fixed labels \(3,7\) at centers \(2\bmod4\), are given in [the small-dependencies note](PrimeOrbitSmallOddDependencies.md). For that family the mod-4 character is trivial on \(N-1\) and retains both primes.

At the fixed-squareclass centers of 1 and at all the fixed-prime-part centers of 2, there is **always** such a path in at most **two** steps and every vertex before the last is retained. A genuine endpoint may of course terminate it earlier (including time zero). If \(x\) is exceptional, any retained successor is either the desired target already or a distinct small vertex outside the one-exception budget and hence has a direct large odd successor. These conclusions use the respective value of \(Y\) above. For example when \(8\mid N\), the even mod-8 character \((2/\cdot)\) retains the maximal-order signed classes modulo \(2^{v_2(N)}\): in the cyclic signed unit group these are the generators, precisely the classes congruent to \(\pm3\bmod8\). The last large successor need not retain that order, need not have prime complement, and does not prove a representation of \(N\).
