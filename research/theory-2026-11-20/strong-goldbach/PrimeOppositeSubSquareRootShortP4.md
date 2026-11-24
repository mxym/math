# Two real P4 windows below the earlier square-root scale

Written research note, 2026-11-24. This is a local squarefree P4 result, not P3; no literature priority claimed. It exploits exact lower linear-sieve functions plus an asymmetric affine switched sieve, with short-interval prime distribution when the actual sources are near \(\sqrt N\). It is independent of the short-cutoff tilted experiment.

## Theorem

Let \(N\) be a sufficiently large even integer and \(L=\log N\). Fix real \(0<a<b\), and consider either of the following actual prime source windows:

1. \(I=(aN^{.49},bN^{.49}]\);
2. \(I=(x,x+N^{.495}]\) for **any** real \(x\in[a\sqrt N,b\sqrt N]\).

Write \(Y=|I|\), \(X=\int_I du/\log u\), and
\[
 S_N=2\prod_{\ell>2}(1-(\ell-1)^{-2})\prod_{\substack{\ell>2\\\ell\mid N}}\frac{\ell-1}{\ell-2},
 \qquad B=2 X S_N/L .
\]
Uniformly in the stated windows there are at least \((.08+o(1))B\) true primes \(p\in I\) such that \(N-p\) is squarefree, \(P^-(N-p)\ge N^{.04}\), and \(\Omega(N-p)\le4\).

Case 1 moves the **size of the prime p** below the square root. Case 2 keeps primes near the square root but supplies the representation in **every** window of the shorter width, rather than in a fixed positive fraction of \(\sqrt N\). In both cases \(B\gg Y/L^2\). No averaging over even \(N\) or over the roots' starting positions occurs.

## 1. Source distribution in both cases

Set \(d_0=.244,\ D=N^{d_0}\). In case 1 classical BV on true prime scale \(N^{.49}\) is more than enough for moduli \(D\): the exponent ceiling is .245 minus logarithms. In case 2 use Perelli–Pintz–Salerno, *Bombieri's theorem in short intervals*, Ann. Scuola Norm. Sup. Pisa 11 (1984), 529–539, p. 530, Theorem and (2)–(3), https://www.numdam.org/article/ASNSP_1984_4_11_4_529_0.pdf . Their estimate for Mangoldt weights is uniform after taking the maximum over reduced classes, starts in \([P/2,P]\), and lengths at most \(y=P^\theta\); it has arbitrary logarithmic saving from error scale \(y\) for fixed \(\theta>3/5\) and moduli at most \(P^{\theta-1/2}/\log^C P\). Here take \(P=x+Y\asymp_{a,b}\sqrt N\), \(\theta=.989\), and \(y=P^{.989}\). All starting points are in \([P/2,P]\) for \(N\) large. Split any subinterval \((x,x+h]\) with \(h\le Y\) into consecutive pieces of length \(\le y\). Each residual is upper-bounded by the same maximal residual, and \((1+Y/y)y=O_{a,b}(Y)\); this yields the desired maximal error on lengths \(\le Y\). The modulus ceiling has exponent .2445 in \(N\), strictly above .244 (with ample room for all fixed logarithms).

If applying the \(\psi\) version, remove all prime powers uniformly **after summing over the used moduli**. The number at the full true prime scale is at most \(O(P^{1/2}\log^C P)\), and the total loss even by bounding a power for every modulus is \(O(DP^{1/2}L^C)\). This is \(N^{.489+o(1)}=o(YL^{-A})\) in case 1, and \(N^{.494+o(1)}=o(YL^{-A})\) in case 2, for every fixed A. Partial summation then converts the \(\log p\) count and its maximal residual to the \(\operatorname{Li}\) main term and the \(\pi\) residual with arbitrary logarithmic saving.

Restrict to primes \(p\) not dividing \(N\). For a squarefree modulus \(m\) coprime to \(N\), \(m\mid N-p\) is exactly the reduced class \(p=N\bmod m\), whose nominal density is \(g(m)=1/\phi(m)\); set the density zero for primes of \(N\). Deleting \(p\mid N\) changes the weighted remainder by \(N^{o(1)}\), since only \(m\mid N-p\) are affected for each of the \(O(L)\) deleted p. As in the [fixed-proportion square-root window proof](PrimeOppositeSquareRootP4.md), fixed divisor-weight powers cost only logarithms: by crude floors \(\lvert R_m\rvert\ll Y\,\tau(m)/m\) for \(m\le D<Y\), giving \(\sum C^{2\omega(m)}|R_m|\ll Y L^{O_C(1)}\), then use Cauchy–Schwarz with the aggregate absolute BV bound. It follows that all linear-sieve remainders below are \(o(B)\), including conditional remainders supported on \(qm\le D\). The max over reduced classes is essential for the true moving \(N\).

## 2. Richert choice, base sieve and small marks

In exponent units choose
\[
 \mu=.04,\quad \beta=.314,\quad T=.216,\quad
 z=N^\mu,\quad y_*=N^\beta,\quad \eta=5-1/\beta=285/157 .
\]
On the rough row \(m=N-p\) use
\[
 w(m)=1-\eta^{-1}\sum_{\substack{z\le q<y_*\\q\mid m\\q\ \mathrm{prime}}}(1-\log q/\log y_*).
\]
For squarefree \(m\le N\), the sum of marks is at least \(\Omega(m)-(\log m)/(\beta L)\), since restoring \(q\ge y_*\) adds nonpositive terms. Thus \(w(m)\le0\) if \(\Omega(m)\ge5\), and always \(w(m)\le1\).

Let \(f,F\) be the standard lower/upper linear sieve functions, and define \(g_*(s)=s f(s)/(2e^{\gamma_E})\), \(h_*(s)=s F(s)/(2e^{\gamma_E})\). These are normalized so that \(g_*=0\) for \(s\le2\), \(h_*=1\) for \(s\le3\) on the relevant positive range, and their derivatives on the ensuing ranges are \(g_*'(s)=h_*(s-1)/(s-1)\), \(h_*'(s)=g_*(s-1)/(s-1)\). This is the usual dimension-one sieve, e.g. Montgomery–Vaughan II §21.3, Theorem 21.9 and following formulae at https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf . The product over eligible primes has \(V(w)=(1+o(1))e^{-\gamma_E}S_N/\log w\) uniformly for cutoff \(w\) above any fixed positive power of \(N\). The dimension-one bound is uniform since deleting primes dividing \(N\) can only help the product ratios.

The base rough count in units \(B\) has lower coefficient \(A=g_*(d_0/\mu)/d_0=g_*(6.1)/.244\). For a true prime mark \(q\) with \(t=\log q/L\in[\mu,T]\), use the upper linear sieve at level \(D/q\) and cutoff \(z'=\min(z,(D/q)^{1/2})\). This is a legitimate weakening for upper bounding the true \(z\)-rough cofactor; the parameter \(s'=\max(2,(d_0-t)/\mu)\) remains bounded away from 1, and \(z'\ge N^{.014}\). In units \(B/q\) the resulting upper coefficient is \(h_*(s')/(d_0-t)\). Here \(q\) is not in the auxiliary sifting product and \(q\mid N\) gives no true mark after the deletion. For weight sum errors, \(qm\le D\) has at most one prime factor \(q\ge z\) because every prime of the auxiliary \(m\) is below \(z'\le z\), so the BV error is aggregated once per actual test modulus. With the harmonic prime measure, the total small-side cost is bounded by \((C_1+o(1))B\), where
\[
 C_1=\int_\mu^T \frac{1-t/\beta}{t(d_0-t)}
                 h_*\!\left(\max(2,(d_0-t)/\mu)\right)\,dt .
\]

## 3. Large mark affine window, keeping physical length and source location separate

For \(T<t\le\beta\), the mark \(q\) is an actual prime and \(q\mid N-p\) is switched to an integer variable \(j=(N-p)/q\) on an interval of length exactly \(Y/q\), with the corresponding half-open endpoints. For an upper bound, sieve \(p=N-qj\) to primes \(\ell\le K\), and \(j\) to primes \(\ell<z\), where
\[
 K=N^{(.49-t)/2-.0005},\qquad v=\log K/\log z=((.49-t)/2-.0005)/\mu.
\]
Here \(z<K<q\), \(p>K\), and \(v\in[2.1875,3.4125]\). The cutoff uses the **weaker physical width** \(N^{.49}\) for both types of windows, not the prime location. For \(\ell<z\), the two affine roots collide precisely if \(\ell\mid N\), and for \(z\le\ell\le K\) only the \(p\) root is used. Prime \(q\mid N\) gives no true marks since \(p=q\) would lie below either window.

For the exact squarefree Selberg denominator \(G_a(K)\), let \(G_0(U)\) be the full two-form denominator. The same Euler convolution and positive one-prime telescoping bound as in the [parent fixed-window P4 proof](PrimeOppositeSquareRootP4.md) give
\[
 G_0(U)=\frac{(\log U)^2}{2S_N}+O((1+\log U)(\log\log N)^C),
\]
uniformly for \(1\le U\le N\), and
\[
 \begin{split}
 G_a(K)&\ge G_0(K)-\sum_{z\le\ell\le K}
   \left(\frac{2}{\ell-2}-\frac{1}{\ell-1}\right)G_0(K/\ell)\\
 &\ge \frac{(\mu L)^2}{S_N}(J(v)+o(1)),\\
 J(v)&=v^2/2-\frac12\int_1^v (v-u)^2\,du/u
       =5v^2/4-(v^2/2)\log v-v+1/4 .
 \end{split}
\]
For primes dividing \(N\) the actual loss is zero, so adding them with the displayed positive majorant is legal. The comparison is **one subtraction of all possible local losses**, justified by telescoping each positive squarefree weight; no assumption that these losses are disjoint is made, and this proof continues to hold throughout the new compact v range. To recall the uniform first formula, divide the Euler product with local \(1+b_\ell\ell^{-s}\), \(b_\ell=\nu(\ell)/(\ell-\nu(\ell))\), by \(\zeta(1+s)^2\); the convolution partner has first absolute log moments \(O((\log\log N)^C)\) since its non-exceptional first coefficients are \(O(\ell^{-2})\) and the exceptional ones are supported at \(\ell\mid N\). Its sum at zero is \(1/S_N\). Convolving with \(\tau(n)/n\), whose first sum is \((\log U)^2/2+O(1+\log U)\), proves the formula. The sum loss follows by Mertens/partial summation using \(2/(\ell-2)-1/(\ell-1)=1/\ell+O(1/\ell^2)\). Positivity and monotonicity of \(J\) on the displayed compact range follow from \(\log v<5/4\), since \(J'\ge .75v-1>0\) and \(J\ge .625v^2-v+.25>0\).

For each true \(q\), expanding the optimal Selberg square gives main upper \(Y/(qG_a(K))\). The remainder is \(O(K^2 L^C)\) by \(O(1)\) integer floors per allowed congruence class and standard divisor-bounded quadratic coefficients; more explicitly, \(|\lambda_d|\le3^{\omega(d)}\) and the number of forbidden residues of the LCM is at most \(2^{\omega([d,e])}\), so the summed absolute errors are \(O(K^2 L^C)\). Since \(K^2=N^{.489}/q\), their aggregate is \(O(N^{.489}L^C)=o(B)\), **even in the weaker actual \(Y\asymp N^{.49}\)**, and a fortiori in the shorter relative window of case 2. No prime distribution on the affine \(j\) progression is used.

In both windows \(X\ge(2+o(1))Y/L\) because the source locations are at most \(O(\sqrt N)\); in the first case \(X\sim Y/(.49L)\) is even slightly larger. Consequently this gives an upper coefficient \(1/(4\mu^2 J(v))\) in units \(B/q\), and the total long-mark cost is at most \((C_2+o(1))B\), with
\[
 C_2=\int_T^\beta\frac{1-t/\beta}{4t\mu^2 J(((.49-t)/2-.0005)/\mu)}\,dt.
\]
Harmonic prime summation here counts marks over real prime \(q\); no substitution of the cofactor roughness by its heuristic density occurs.

## 4. Exact arithmetic for the positive signed margin

The following replay uses only directed integer/rational arithmetic. For \(g_*,h_*\) on a grid of size \(1/M\), both functions are nondecreasing, and a delay by 1 maps grid endpoints to grid endpoints. On the \(i\)-th cell, bound every derivative using its numerator at the left or right endpoint, and the denominator at the opposite endpoint; round each step down or up in units \(10^{-12}\). This propagates endpoint enclosures by induction. For \(C_1\), the weight \((1-t/\beta)/t\) and \(h_*(\max(2,(d_0-t)/\mu))\) decrease; the factor \(1/(d_0-t)\) increases. For \(C_2\), the weight decreases, while \(1/J(v(t))\) increases. Therefore the displayed rational rectangles are upper sums. The bound on \(\log v\) is the expansion in \((v-1)/(v+1)\) with its positive geometric tail bounded explicitly.


```python
from fractions import Fraction as F
M, SCALE = 2000, 10**12
end = 61*M//10
gl = [0]*(end+1); gu = [0]*(end+1)
hl = [SCALE]*(end+1); hu = [SCALE]*(end+1)
def ceil_div(a,b):
    assert a >= 0 and b > 0
    return (a+b-1)//b
for i in range(2*M+1,end+1):
    lo,hi = i-M,i-M-1
    gl[i] = gl[i-1] + hl[i-M-1]//lo
    gu[i] = gu[i-1] + ceil_div(hu[i-M],hi)
    if i > 3*M:
        hl[i] = hl[i-1] + gl[i-M-1]//lo
        hu[i] = hu[i-1] + ceil_div(gu[i-M],hi)
def log_upper(x):
    assert x >= 1
    v = (x-1)/(x+1)
    return 2*sum(v**(2*i+1)/(2*i+1) for i in range(14)) + 2*v**29/(29*(1-v*v))
D, rho, mu, beta, T, eps = F(244,1000),F(49,100),F(1,25),F(157,500),F(27,125),F(1,2000)
eta = 5-1/beta
def bv_cap(a,b):
    s = max(F(2),(D-a)/mu)*M
    h_upper = F(hu[ceil_div(s.numerator,s.denominator)],SCALE)
    return (1-a/beta)*h_upper/(a*(D-b))
def affine_cap(a,b):
    v = ((rho-b)/2-eps)/mu
    J_lower = 5*v*v/4-v*v*log_upper(v)/2-v+F(1,4)
    assert J_lower > 0
    return (1-a/beta)/(4*a*mu*mu*J_lower)
def upper(left,right,cap):
    n, unit = 3000, 10**9
    dx = (right-left)/n
    total = 0
    for k in range(n):
        a = left+k*dx
        w = unit*dx*cap(a,a+dx)
        total += ceil_div(w.numerator,w.denominator)
    return F(total,unit)
assert log_upper(((rho-T)/2-eps)/mu) < F(5,4)
A = F(gl[end],SCALE)/D
C1 = upper(mu,T,bv_cap)
C2 = upper(T,beta,affine_cap)
assert A == F(1712029418637,244000000000)
assert C1 == F(983279773,100000000)
assert C2 == F(2744692571,1000000000)
assert A-(C1+C2)/eta > F(8,100)
```

The equivalent exact BigInt replay returned \(A\ge1712029418637/244000000000=7.0165140108\ldots\), \(C_1\le9.832797730\), \(C_2\le2.744692571\), giving \(A-(C_1+C_2)/\eta>.0878\). No floating point sign decision is needed.

## 5. Squarefree deletion with the actual Y, and conclusion

Among the true rough complements, all square divisors \(r^2\) have \(r\ge z\). For \(r\le N^{1/3}\), sum the elementary bounds \(O(Y/r^2+1)\) over integers r to give \(O(Y/z+N^{1/3})\). For \(r>N^{1/3}\), write \(m=c r^2\), \(c\le N^{1/3}\). The interval cut for r has length \(O(Y/\sqrt{Nc})\) since \(m=N-p\asymp N\); summing it and the unit floor term over \(c\le N^{1/3}\) gives \(O(Y N^{-1/3}+N^{1/3})\). This is \(o(B)\) uniformly even in the smaller \(Y\asymp N^{.49}\) case. The signed weights are uniformly bounded on rough rows because the number of distinct primes of any \(z\)-rough \(m<N\) is at most \(1/\mu\). Thus discarding the squareful part does not consume the margin.

The signed sum on real squarefree rows is at least \((A-(C_1+C_2)/\eta+o(1))B\); only actual \(\Omega\le4\) rows have positive weight and each weighs at most 1. This proves the theorem. It leaves the [P3 middle-mark estimate](PrimeOppositeSquareRootP3Target.md) open.
