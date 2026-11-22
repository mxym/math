# A single-giant prime-divisor remainder for the literal Goldbach weight

Fix a nondegenerate compact interval \(J\subset(0,1)\) and write \(L=\log N\). Every sufficiently large **individual even integer** \(N\) is allowed; no radical restriction or zero-free hypothesis beyond classical theorems is used. Put
\[
 S=\exp((\log L)^4),\qquad B_*=N/S,\qquad
 U=\frac{\sqrt N}{S L^C}.
\]
For each desired fixed logarithmic accuracy \(A>0\), choose \(C=C(A)>0\) sufficiently large. On each actual prime row \(p\in NJ\), write \(y=N-p\). Let \(\mathfrak S(N)\) be the ordinary binary singular series
\[
 \mathfrak S(N)=
 \prod_{\ell\mid N}(1-\ell^{-1})^{-1}
 \prod_{\ell\nmid N}\left(1-\frac1{(\ell-1)^2}\right),
 \qquad
 R_J(N)=\sum_{\substack{p\in NJ,\ q>0\\p+q=N\\p,q\ {\rm prime}}}
                      (\log p)(\log q).
\]
The exact-weight reduction with arbitrary \(A\) is
\[
\begin{split}
 R_J(N)={}& |J|N\mathfrak S(N)-\mathcal C_{S,U}(N)
                          +O_{A,J}(N L^{-A}),\\
 \mathcal C_{S,U}(N)={}&
 \sum_{p\in NJ\ {\rm prime}}\log p
    \sum_{\substack{U<r\le B_*\\ r\mid y,\ r\ {\rm prime}}}\log r
          \sum_{\substack{n\mid y/r\\ n<y/B_*}}\mu(n).
\end{split} \tag{1}
\]
All three inequalities \(r>U,\ r\le B_*,\ n<y/B_*\) are as written. The inner modulus is subpower, \(n<S<r\); in particular its divisibility predicate can equivalently be \(n\mid y\). The physical cofactor \(y/r\) lies between a fixed positive multiple of \(S\) and \(\sqrt N\,S L^C\). At most two distinct prime marks \(r\) occur on a row, and (1) initially counts **both** when both are in its range.

At scale \(o(N)\), rows with two distinct prime divisors \(>U\) can be deleted from \(\mathcal C_{S,U}\), even if only one appears in the displayed \(r\)-range. Thus the remaining signed term can be taken to have a single actual near-root or larger prime divisor. We do not upper bound this remaining signed term below \(|J|N\mathfrak S(N)\); the result supplies no binary positivity.

The broader prefix statement used below is also useful. For fixed \(\epsilon>0\), one may take any \(\exp((\log L)^4)\le S\le N^{1/2-\epsilon}\) and \(B_*=N/S,\ U=\sqrt N/(S L^C)\). For arbitrary \(|a_d|\le1\) set
\[
 W_U(b)=\sum_{\substack{d\mid b\\d\le U}} a_d\Lambda(d).
\]
Then
\[
 \sum_{p\in NJ\ {\rm prime}}(\log p)
        \sum_{\substack{b\mid y\\ b\le B_*}}\mu(y/b)W_U(b)
       =O_{A,J,\epsilon}(N L^{-A}).                            \tag{2}
\]
The mark \(d\) is a literal **prime power** with its exact von Mangoldt coefficient. For a fixed \(\theta\in(1/2,1)\), setting \(B_*=N^\theta\) pays every mark \(d\le N^\alpha\) with fixed \(\alpha<\theta-1/2\), jointly over the complete prefix. Equation (2) does **not** say that those marks cancel inside any individual central dyad, nor does it require any approximation to an unsigned divisor sum.

## 1. Uniform Möbius harmonics

For any positive integer \(d\), set
\[
 a_{N,d}(n)=\frac{\varphi(d)n}{\varphi(dn)}
                    \mu(n)\,1_{(n,N)=1}.
\]
This is multiplicative in \(n\), by the local cases for the quotient of the two totients. Its Dirichlet series \(A_{N,d}(s)\) factors as \(\zeta(s)^{-1}G_{N,d}(s)\). At a prime \(\ell\mid N\), the local factor of \(G\) is \((1-\ell^{-s})^{-1}\); at \(\ell\mid d,\ \ell\nmid N\) it is \(1\); elsewhere it is
\[
 \frac{1-\frac{\ell}{\ell-1}\ell^{-s}}{1-\ell^{-s}}
           =1-\frac1{\ell-1}\sum_{j\geq1}\ell^{-js}.
\]
Write \(G=\sum_j g(j)j^{-s}\). Set \(\sigma_0=1-1/(10\log L)>.9\) for large \(N\). The absolute Euler product gives, uniformly in \(N,d\),
\[
 \sum_j\frac{|g(j)|}{j^{\sigma_0}}\ll (\log L)^{O(1)}.
 \tag{3}
\]
Indeed the non-\(N\) Euler product is bounded uniformly for \(\sigma_0>.9\). In the \(N\)-part, for \(\ell\le L^2\) use \(\ell^{1-\sigma_0}\le e^{1/5}\) and the ordinary reciprocal-prime bound; the log of that product is \(O(\log\log L)\). There are \(O(L)\) prime factors of \(N\) above \(L^2\), each with \(\ell^{-\sigma_0}\ll L^{-2}\). This is why no small-radical assumption is needed.

Apply the classical Mertens bound \(\sum_{m\le X}\mu(m)\ll X\exp(-c\sqrt{\log X})\), from the ordinary zeta zero-free region, to the convolution \(a_{N,d}=\mu*g\). On \(j\le\sqrt X\) the Mertens length is at least \(\sqrt X\). On \(j>\sqrt X\) the trivial inner bound \(X/j\) and (3) suffice. Hence
\[
  \left|\sum_{n\le X}a_{N,d}(n)\right|
  \ll X(\log L)^{O(1)}
          \left(e^{-c_1\sqrt{\log X}}+X^{-(1-\sigma_0)/2}\right).
 \tag{4}
\]
For \(X\ge c_J\exp((\log L)^4)\), partial summation gives arbitrary fixed logarithmic saving on both the \(1/n\) and the \((\log n)/n\) tails, uniformly in \(d\). To see this for the first term of (4), put \(v=\sqrt{\log t}\) in the integral tail to infinity: any fixed powers of \(\log t\) are paid by \(e^{-c_1v}\), and \(v\gg(\log L)^2\) at the lower endpoint. In the other tail the exponential scale at the lower endpoint is \(e^{-\Omega((\log L)^3)}\); the factors from integrating \(t^{-1-(1-\sigma_0)/2}(1+\log t)\) are only powers of \(\log L\) times a polynomial in \(\log X\). Strict real endpoints and inclusive prefixes obey the same estimates by using the integer count below the real endpoint.

At \(s=1\), the exact identities are \(A_{N,d}(1)=0\) and \(A_{N,1}'(1)=G_{N,1}(1)=\mathfrak S(N)\). The convergent series and its first logarithmic moment at \(1\) agree with these values by (4) and Abel continuity/partial summation. The local factors of \(G_{N,1}(1)\) outside \(N\) are \(\ell(\ell-2)/(\ell-1)^2\), and the factor at \(2\) is harmless because \(N\) is even and \(2\mid N\). Consequently, uniformly at the indicated lengths \(X\),
\[
 \sum_{\substack{n<X\\(n,N)=1}}\frac{\mu(n)}{\varphi(dn)}
       \ll_{A,J}\frac{L^{-A}}{\varphi(d)},\qquad
 -\sum_{\substack{n<X\\(n,N)=1}}\frac{\mu(n)\log n}{\varphi(n)}
       =\mathfrak S(N)+O_{A,J}(L^{-A}).
 \tag{5}
\]

## 2. The complete upper cofactor and its marked subpart

Use \(\Lambda(y)=\sum_{b\mid y}\mu(y/b)\log b\) and split at \(B_*\). All real prime counts below use maximal-prefix [Bombieri–Vinogradov](https://doi.org/10.1112/S0025579300005313). In \(b>B_*\), put \(n=y/b\), so \(n<y/B_*<S\) and \(p\equiv N\bmod n\). Discard the central true primes \(p\) that divide \(N\) explicitly throughout. There are at most \(L/\log2\) of them; for the original and all expanded sums their contribution is \(N^{o(1)}\), since each fixed row has at most \(\tau(y)^2\) divisor/mark occurrences and weights \(O(L^2)\). After this deletion \(y\) and all moduli dividing it are target units. Removing the same finitely many \(p\)'s from a BV replacement contributes at most \(N^{o(1)}\) in the aggregate by the same divisor count. Equivalently in a given reduced class a prime dividing \(N\) is simply an exceptional individual row when it occurs; no claimed exclusion for general \(N\) is used without this removal.

For fixed \(n\), the interval of \(p\)'s is \(NJ\) intersected with \(p<N-B_* n\). The weight \(\log((N-p)/n)\) has supremum \(O(L)\) and bounded total variation on this central interval, so partial summation and the maximal-prefix input keep arbitrary fixed log accuracy. Its main contribution is
\[
 \int_{t\in NJ}
    \sum_{\substack{n<(N-t)/B_*\\(n,N)=1}}
       \frac{\mu(n)}{\varphi(n)}\log\frac{N-t}{n}\,dt
    = |J|N\mathfrak S(N)+O_{A,J}(N L^{-A}),                 \tag{6}
\]
by (5) at \((N-t)/B_*\asymp_J S\). If the BV version is written with \(\Lambda\) rather than actual primes, the difference is negligible in this weighted aggregate: a proper power at the source has at most \(\tau(N-p^j)^2\) relevant decompositions of its divisors, uniformly \(N^{o(1)}\), and there are \(N^{1/2+o(1)}\) proper powers. The same argument applies in the following marked sum.

For \(W_U\), expand the \(b>B_*\) sum into \(d\mid b\) and \(n=y/b\). Its actual modulus is \(q=dn\), **not** \([d,n]\) even when the factors share a prime. Its size is \(q\le US=\sqrt N/L^C\), enough for a weighted BV estimate. For completeness, the number of choices of \(d,n\) for a given \(q\) is at most \(\tau(q)\), with extra weights \(\Lambda(d)\le L\). Split into \(\tau(q)\le L^D\) and its complement. In the first part request BV accuracy increased by \(D+1\) and choose its denominator exponent \(C\) accordingly. In the second the trivial maximal log-prime discrepancy is \(O(NL^2/q)\), and
\[
 \sum_{\substack{q\le N\\\tau(q)>L^D}}\frac{\tau(q)}q
       \ll L^{4-D},
\]
using \(\tau^2\le\tau_4\) and the four-factor harmonic sum. Choose \(D\) large in terms of \(A\). This works for each actual interval endpoint depending on \(n\) by the maximal-prefix formulation. It also pays the proper-power removal and target-dividing row correction noted above. The resulting principal expression is
\[
  \int_{t\in NJ}\sum_{\substack{d\le U\\(d,N)=1}}a_d\Lambda(d)
        \sum_{\substack{n<(N-t)/B_*\\(n,N)=1}}
                     \frac{\mu(n)}{\varphi(dn)}\,dt
        =O_{A,J}(NL^{-A}),
 \tag{7}
\]
by (5), since \(\sum_{d\le U}\Lambda(d)/\varphi(d)\ll L\) by Chebyshev and the prime-power reciprocal geometric sum.

The **complete** exact marked identity is
\[
  \sum_{b\mid y}\mu(y/b)W_U(b)=1_{y\le U} a_y\Lambda(y)=0
 \quad(y=N-p\text{ on the central range}).
\]
It follows by associativity of Dirichlet convolution and \(\mu*1\) equal to the delta at \(1\). Subtracting the evaluated upper part (7) proves (2). This is why a primitive polynomial prime-power log mark can be removed from the complete unresolved prefix even though it is not estimated for each individual dyad.

## 3. The true giant remainder

Take \(S=\exp((\log L)^4)\) and \(U=\sqrt N/(S L^C)=N^{1/2-o(1)}\). Within the raw \(\log b=\sum_{d\mid b}\Lambda(d)\), all marks \(d\le U\) have just been removed from the prefix \(b\le B_*\). For proper powers \(d>U\) (exponent at least two), the absolute weighted sum is
\[
 \ll N^{1+o(1)}\sum_{\substack{U<d\le N\\d\ {\rm proper\ prime\ power}}}d^{-1}
 \ll N^{3/4+o(1)}.
\]
Indeed for fixed \(d\) there are at most \(N/d\) positive multiples \(y\le N\), and each row has only \(\tau(y)\le N^{o(1)}\) choices \(b\) divisible by \(d\); all logs were absorbed into \(N^{o(1)}\). The reciprocal proper-power bound follows by dyadic counting \(O(T^{1/2}\log T)\) up to \(T\). Passing between the full \(\Lambda(y)\) and actual prime \(y\) likewise costs only \(N^{1/2+o(1)}\).

Thus each unpaid \(d\) is an actual prime \(r>U\). In \(b\le B_*\), write \(b=rt\), \(m=y/r\); then \(r\le B_*<y\) and \(m>1\). Its exact residual factor is
\[
 \sum_{\substack{t\mid m\\rt\le B_*}}\mu(m/t)
   =\sum_{\substack{n\mid m\\n\ge y/B_*}}\mu(n)
   =-\sum_{\substack{n\mid m\\n<y/B_*}}\mu(n),
\]
where the final equality uses the **whole** divisor sum at \(m>1\). This gives (1) with (6). Since \(U^3>N\), there are at most two distinct marks, not one in general.

### Negligible two-giant contribution

If \(y=r s h\) with two distinct primes \(r,s>U\), then \(h\le H=N/U^2=S^2L^{2C}\), both \(r,s\) are in \([U,N/U]\), and \(n<S<s\) implies \(n\mid h\) in the \(r\)-marked short sum. Thus its absolute short score is at most \(\tau(h)\). We may count both marked choices and even drop all interval constraints other than central \(p\) and the lower bounds on the two primes.

For each fixed actual \(r,h\), apply the two-form upper sieve to \(s\) and \(p=N-rh\,s\) on a length \(O(N/(rh))=N^{1/2+o(1)}\) interval. If \((rh,N)>1\), no retained central true \(p\) is possible. Otherwise the local root count is one at \(\ell\mid N rh\), two elsewhere, with \(\ell=2\) included in the first case. The bound, uniform here, is
\[
 \ll \frac{N}{r h L^2}\,\mathfrak S(N)\tau(h).
\]
For example use elementary Selberg divisor support \(D=N^{1/100}\), with coefficients bounded by one, so total floor error is \(O(D^2(\log D)^2)\) because root counts on squarefree moduli satisfy \(\nu([a,b])\le\tau(a)\tau(b)\). The Selberg denominator is at least a fixed fraction of the positive local product restricted to primes \(\ell\le D^{1/20}\): in that normalized product the expected \(\log d\) is
\(\sum_{\ell\le D^{1/20}}\nu(\ell)\log\ell/\ell
 \le 2\log(D^{1/20})+O(1)<(\log D)/2\)
for large \(N\), by \(\nu(\ell)\le2\) and prime Mertens. Markov retains a fixed fraction under \(d\le D\). The corresponding dimension-two product gives \(L^{-2}\mathfrak S(N)\) times an extra factor at most \(2\tau(h)\), since a prime dividing \(rh\) but not \(N\) changes its local factor by \((\ell-1)/(\ell-2)\le2\). All genuine \(s,p\) on these rows exceed the sifting cutoff, and the floor error is negligible at the stated interval length.

After the two logs and \(\tau(h)\), sum this bound over \(r,h\):
\[
 \ll N\mathfrak S(N)\sum_{\substack{U<r\le N/U\\r\ {\rm prime}}}\frac1r
                    \sum_{h\le H}\frac{\tau(h)^2}{h}
 \ll \frac{N\mathfrak S(N)}L (1+\log H)^5=o(N).
\]
Use Chebyshev and partial summation for the \(r\)-interval (logarithmic width \(\log H\), and \(\log r\asymp L\)), the four-factor harmonic bound for \(h\), and the usual \(\mathfrak S(N)\ll\log L\), which also follows by splitting the \(N\)-prime Euler factors at \(L^2\). The last equality uses \(\log H=O((\log L)^4)\). Likewise rows with \(r^2\mid y\) for \(r>U\) can be removed at \(N^{1/2+o(1)}\) cost, just by \(\sum_{r>U}\lfloor N/r^2\rfloor\ll N/U\) and at most \(\tau(y)^2\) divisor weights per row. Thus the surviving single giant may be taken to occur to exponent one. The two-distinct-giant deletion has the weaker absolute \(o(N)\) accuracy; the arbitrary-log formula (1) before deletion is unchanged.

The classical truncated divisor completion by prime BV is not new. Compare [Goldston–Yıldırım, *Higher correlations of divisor sums related to primes*](https://math.colgate.edu/~integers/d5/d5.pdf) for truncated divisor models and [Bado, §4](https://doi.org/10.13140/RG.2.2.32710.84803) for a complementary-divisor switching of a different reflected sieve tail. The latter has an explicit small-prime sieve-support restriction; its switched tail keeps a long Möbius argument. Here the full logarithmic Möbius identity, the independent genuine prime-power mark, and its cancellation over the complete prefix instead leave a genuine near-/over-root prime and a **subpower** short-Möbius score. These are scope comparisons, not a priority claim. No estimate for the remaining signed single-giant term is imported.
