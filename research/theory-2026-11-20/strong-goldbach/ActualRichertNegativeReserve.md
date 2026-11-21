# A substantial actual Richert negative reserve on each adjusted quotient profile

Use the actual fixed-target rows \(N=2x,\ n=sq\in(x/2,x],\ m=N-sq,\ (n,N)=1\), the two genuine \(\mathcal Q_i\), and \(w(s,q)=W_s(q)D_B(q)/\log q\) as in [AdjustedFirstTaperAllRank.md](AdjustedFirstTaperAllRank.md). Here \(w\) is bounded and positive, with \(D_B/\log q=i\) exactly, not a modeled probability. Let \(I_i\) denote the actual source densities of [AdjustedTriprimePositiveBudget.md](AdjustedTriprimePositiveBudget.md), so
\[
       A_i(x,N)=\sum_{\mathcal Q_i}w(s,q)
            =(I_i+o(1))x/(2L),\qquad L=\log x .
\]
The PNT evaluation is uniform after the target-unit exclusions, since all source primes are polynomially large, and follows by the source half of that note's product calculation.

Use the **same actual evolved detector**
\[
 E'_j(m)=\Lambda(m)-\log m
        \left\{\frac{A_j(m)}{2j}
                    +(1-\tfrac1{2j})G(m)\right\},\quad
 A_j(m)=\sum_{d\mid m}\mu(d)(1-2\log d/\log m)_+^j
\]
from the first-taper note. Take fixed odd \(j\ge9\) with \(j(1-\sigma)>3\) and a flat \(G\) supported in \(d\le x^\epsilon\) for any fixed \(0<\epsilon<.04\). This is a genuine whole-profile replacement of the original \(C\) to \(o(M_N)\), but no replacement is made in a restricted subrow. We work directly in this new detector.

Consider the actual reflected chamber
\[
 \mathcal C=\{m=p u:\ p\text{ prime},\ x^{.04}<p<x^{.09},\
                  P^-(u)\ge x^{.102},\ \mu^2(u)=1,\ 1\le\Omega(u)\le3\}.
\tag{1}
\]
Every such \(m\) is squarefree composite with \(\Omega(m)\le4\). Its actual marker \(p\) is unique since \(p<x^{.102}\) whereas every prime of \(u\) is at least this lower bound. For all sufficiently large even \(N\),
\[
 \boxed{\qquad
       \sum_{\mathcal Q_i,\ m\in\mathcal C}w(s,q)E'_j(m)
                              \ \le\ -1.19\,I_i M_N,\qquad i=1,2 .
       \qquad}
\tag{2}
\]
The lower bounds for \(I_i\) make these reserves respectively \(>.060M_N\) and \(>.039M_N\) in magnitude. This is an all-target lower occupancy result with a signed use on the same detector, not a dyadic-average debit. No claim is made that the unbounded positive complement is paid by these terms.

## 1. The actual Richert lower sieve, with explicit level and local factors

Keep the numerical exponents
\[
     D_0=.405,\quad z_0=.102,\quad y_0=.360,\quad \eta=1.33,
          \qquad D=x^{D_0},\ z=x^{z_0},\ y=x^{y_0}.
\]
For each marked \(p\) with \((p,N)=1\), put \(u=m/p\) on physical rows with \(p\mid m\). First sift the primes below \(z\) other than those dividing \(Np\), and consider the Richert lower weight
\[
    {\bf1}_{u\ {\rm sifted}}\left\{1-\frac1\eta
             \sum_{\substack{z\le\ell<y\\\ell\mid u,\ \ell\ {\rm prime}}}
                             (1-\log\ell/\log y)\right\}.
\tag{3}
\]
The unit condition already removes \(\ell\mid N\) in the actual rows. The exceptional marked \(p\) removed from the sieve is dealt with by deleting \(p^2\mid m\) at power-small cost. Any further repeat in \(u\) after this deletion has base at least \(z\); their aggregate count is \(O(x^{1-.102})\) by summing \(x/\ell^2\). The label multiplicities of \(s,p\) at a physical row are bounded, and the absolute weight in (3) is at worst \(O(L)\). The deleted cases therefore cost a polynomial saving before log factors, also in the signed sum. On the remaining squarefree sifted \(u\), \(\log_x u\le .960+O(1/L)\) and
\[
 \sum_{\substack{z\le\ell<y\\\ell\mid u}}(1-\log\ell/\log y)
                    \ge \omega(u)-\log u/\log y.
\]
When \(\omega(u)\ge4\), the last expression is \(>\eta\) for sufficiently large \(x\) (the margin is \(4-.96/.36-1.33>0\)). Thus (3) is nonpositive off the desired ranks after the squareful deletion, and everywhere at most \(1\). Since \(u\gg x^{.91}>1\), its positive physical contribution is bounded by the indicator in (1), with unique marker.

For the leading sieve sum the modulus is \(p d\), where \(d\le D\) is the squarefree sieve divisor. For the penalty with \(\ell\mid u\), use upper sieve level \(D/\ell\); the modulus is \(p\ell d\le pD<x^{.495}\). In the second case \(\ell\ge z\) is disjoint from the sieve primes, and \(p\) is removed, so the local factors are exactly multiplicative. For every modulus in the lower and upper sums there are only \(O(1)\) eligible choices of \(p,\ell\): both ranges consist of polynomially large primes and \(d\) is determined after these choices. The Rosser--Iwaniec upper and lower sieve coefficients have magnitude \(\le1\); the extra penalty multiplier is between \(0\) and \(1\). The signed discrepancy is therefore \(O_A(xL^{-A})\) by the full-scale generalized BV on the actual independent \(s\) prime (SW) and the actual \(1\)-bounded \(\mathcal Q_i\) mask. The physical \(w(s,q)\) has the fixed finite smooth separation described in [AdjustedLowRankAbsorption.md](AdjustedLowRankAbsorption.md), with the sharp product paid by its ordinary log-fine meshes. All level room is genuinely at scale \(x=sq\), not the smaller free cofactor.

The ordinary reduced main in these progressions uses \((n,p\ell d)=1\) (omit \(\ell\) in the lower sieve). It can be replaced by its independent total \(A_i\) in the combined main at power-small cost: for each fixed literal \(n=sq\), its at most four prime factors are \(>x^{.010}\). If a source prime is a marker \(p\) or \(\ell\), its harmonic \(\phi\)-factor costs \(O(x^{-.010})\); if it divides \(d\), the sum of the absolute \(1/\phi(d)\) majorant over those \(d\)'s is \(O(x^{-.010}L^C)\). Sum the other marker and sieve factors harmonically. This argument concerns the reduced main, not a claim that \((n,p\ell d)=1\) always holds off the actual congruence. The target-unit \(n\)-mass is already used in \(A_i\), and primes dividing \(N\) are excluded as actual markers. Thus for each \(p,\ell\) the initial masses in the two sieve applications are \(A_i/(p-1)\) and \(A_i/((p-1)(\ell-1))\), respectively, with local density \(g(r)=1/(r-1)\) on the allowed small primes \(r\nmid Np\). There is no \(1/p\) rather than \(1/(p-1)\) factor from the \(p\)-mark. The latter would only enter sifting \(p\mid u\) itself, already deleted at power cost.

The dimension-one local bound is uniform in \(N,p\): excluding primes dividing \(Np\) only improves its inverse-product interval estimate. The actual product at any polynomial \(z'\) used here is
\[
 \prod_{\substack{r<z'\\r\nmid Np}}
                  \left(1-\frac1{r-1}\right)
       =(e^{-\gamma}+o(1))\frac{\mathfrak S(N)}{\log z'} .
\]
This is ordinary Mertens plus the convergent odd-prime factor and the target prime factors. The extra \(p\) contributes \(1+O(x^{-.04})\), and omitted target primes \(r\ge z'\) have negligible reciprocal mass because \(z'\) is polynomial. Since \(N\) is even, \(2\) is absent from all the sieving products.

## 2. Exact lower bracket

Use the classical linear-sieve functions \(f(s)=2e^\gamma\log(s-1)/s\) on \(2\le s\le4\), \(F(s)=2e^\gamma/s\) on \(1\le s\le3\). See, for example, [Montgomery--Vaughan, §21.3](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf) and the actual weighted-sieve integral in [Matomäki, Almost primes in almost all very short intervals](https://doi.org/10.1112/jlms.12592). Only the standard linear-sieve input is used here; the progression theorem is the actual full-scale product BV above.

The lower parameter is \(D_0/z_0=3.9705\ldots<4\). In the upper with \(\ell=x^t\), its formal parameter \((D_0-t)/z_0\le 2.971<3\) can be below \(1\). In that case sieve only up to \(z'=\min(z,D/\ell)\), which majorizes \(z\)-roughness and has parameter \(1\). The resulting upper normalization is the same \(2/(D_0-t)\), from Mertens at the actual \(z'\). All these sieve parameters are in fixed compact intervals, with \(\log z'\ge .045L+O(1)\), and their small sieve-function errors sum to \(o(\mathfrak S(N)A_i/L)\).

Summing the penalty primes by their reciprocal PNT measure \(dt/t\), and taking their nonnegative multiplier in (3), gives lower normalized coefficient
\[
 \begin{split}
 B
 &=\frac{2}{D_0}\log(D_0/z_0-1)
      -\frac2\eta\int_{z_0}^{y_0}
             \frac{1-t/y_0}{t(D_0-t)}\,dt\\
 &=\frac{2}{D_0}\log(D_0/z_0-1)
      -\frac2\eta\left\{\frac1{D_0}\log(y_0/z_0)
         +\left(\frac1{D_0}-\frac1{y_0}\right)
                      \log\frac{D_0-z_0}{D_0-y_0}\right\}
            >1.57.
 \end{split}
\tag{4}
\]
The subtracted signs are those of the **actual** Richert weight. The three log arguments are \(101/34,\ 60/17,\ 101/15\), and the [rational checker](check_actual_richert_reserve.py) certifies the displayed strict bound from a positive atanh series and its explicit tail. The \(p\)-harmonic sum tends to \(\log(.09/.04)=\log(9/4)>.81\), unchanged on \((p,N)=1\) since \(p>x^{.04}\). Consequently the actual \(w\)-weighted count of (1) is at least
\[
           (B\log(9/4)+o(1))\,
                         \frac{\mathfrak S(N)A_i(x,N)}{L}.
\tag{5}
\]

On (1), the genuine composite \(m\) has \(\Lambda(m)=0\), and \(G(m)=1\) because every prime exceeds \(x^\epsilon\). Further \(A_j(m)\ge0\) by the exact signed finite difference of \((1-2t)_+^j\) through order four (or the argument in the polynomial-rank note). Thus \(E'_j(m)\le -(1-1/(2j))\log m\). Combine (5), \(\log m\ge L\) and \(A_i=(I_i+o(1))x/(2L)\). The exact certificate gives \((17/18)(1.57)(.81)>1.19\), so the fixed uniform errors fit (2). The same negative block could be carved out explicitly when the other ranks are compared; this proof does not credit it against an independently unbounded positive remainder.

## Comparison

The weighted sieve input is classical and used in other settings, for example by [Matomäki](https://doi.org/10.1112/jlms.12592) for almost primes in short intervals. [Chan’s November preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) uses marked ranges in a different prime-or-semiprime theorem. The estimate here is a negative block in the actual adjusted quotient ledger, with its corresponding sign and normalization; it is not an estimate of the rest of that ledger and makes no priority claim.
