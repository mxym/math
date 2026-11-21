# An unconditional negative reserve on an actual three-mark chamber

Let $N=2x$ be the fixed even target, $L=\log x$, and let $0<\sigma<1$ be fixed. Take
\[
H=\exp(L^\sigma),\qquad U=\sqrt x/H^4,\qquad V=H,
\qquad Q_0=\sqrt x/H^2.
\]
On the original genuine-prime row $n=sq\in(x/2,x]$, $m=N-sq\in[x,3x/2)$ and $(sq,N)=1$, keep its literal weight
\[
 W_s(q)=(1-t)(1-2t)^2,qquad t=\frac{\log s}{\log(sq)},
 \qquad C(m)=\sum_{\substack{d\ell\mid m\\d>U,\ \ell>V,\ d\ell>Q_0}}\mu(d)\Lambda(\ell).
\]
Thus $C$ is the original reflected high coefficient, before either of the two long-divisor subtractions in [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md). Write $M_N=\mathfrak S(N)x/(2L)$ with $(2 C_2)\prod_{p\mid N,\,p>2}(p-1)/(p-2)=\mathfrak S(N)$ and $C_2=\prod_{p>2}(1-1/(p-1)^2)$.

There are absolute fixed $\eta>0$ and $c_*>0$ with the following property for all sufficiently large even $N$. Consider only the genuine primes $s,q$ and the physical rows $m=N-sq$ for which
\[
      m= p c a b w
      \quad\text{with distinct genuine primes }p,c,a,b,\quad
      P^-(w)>z=x^{1/250}.
\tag{1}
\]
The possible ranges are, in terms of $\log_x$,
\[
\begin{array}{c|l}
s & [0.1009,0.1011]\\
p & [0.218-\eta/100,0.218+\eta/100]\\
c & [0.282-\eta-\eta/100,0.282-\eta+\eta/100]\\
a & [2\eta,2.1\eta]\\
b & [2.2\eta,2.3\eta].
\end{array}
\tag{2}
\]
Count each physical pair $(s,q)$ only once, even if more than one set of labels qualifies. Then
\[
 \boxed{\displaystyle
  \sum_{(s,q)\;\mathrm{in}\;(1)\text{--}(2)} W_s(q) C(N-sq)\le -c_* M_N .}
\tag{3}
\]
This is a signed estimate on a genuine reflected composite chamber. It uses no choice of a cofactor parity, no surrogate $q$-prime, and no global removal of $J$. It is **not** an estimate of the signed complement or a proof of a Goldbach representation. The small constant is not asserted to exceed any previous normalized budget.

## 1. True lower occupation: an ordered factorization above the square root

Take $0<\eta\le 10^{-4}$, fixed before taking $x$ to infinity, and $K=p c a b$. Call a choice of $(s,q,p,c,a,b)$ satisfying (1)–(2) a labelled row. In this section let
\[
 \Sigma(x,N)=
  \sum_{\substack{s,p,c,a,b\;\mathrm{prime\ in}\;(2)\\(s p c a b,N)=1}}
      \frac1{spcab},\qquad
 R_N=\frac{\mathfrak S(N)x}{L^2}\,\Sigma(x,N).
\tag{4}
\]
The prime exponent intervals are disjoint. For fixed sufficiently small $\eta$ and all sufficiently large $x$, the PNT and partial summation give $\Sigma(x,N)\gg \eta^2$, uniformly in $N=2x$, with an absolute implied constant. Indeed the limiting sum in each interval $[x^u,x^v]$ is $\log(v/u)$, the $p,c$ factors are $\gg\eta$ each and the others are bounded positively below. Removing prime divisors of $N$ costs $O_{\eta}(x^{-2\eta})$: each such label is at least $x^{2\eta}$ and there are $O_{\eta}(1)$ of them.

Apply the usual lower Rosser–Iwaniec linear sieve with $D=x^{0.012}$, $z=x^{0.004}$, so $\log D/\log z=3$. Sift $w=m/K$, not $m$, after imposing $K\mid m$, and use only sieving primes not dividing $N$. The lower weight $\lambda_d^-$ is independent of $K$, supported on squarefree $d\le D$ with $P^+(d)\le z,(d,N)=1$ and $|\lambda_d^-|\le1$. The exact condition $d\mid w$ is $s q\equiv N\bmod Kd$ even when $d$ shares a prime with $K$.

In this residue the source consists of the two independent actual prime sequences $s,q$, after the ordinary central product restriction. Use [Lichtman, arXiv:2309.08522v1, Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5) with residue $N=2x$, source scale comparable to $x$, and ordered modulus slots
\[
             (Q_1,Q_2,Q_3)=(ab d,p,c).
\tag{5}
\]
There is no assertion that the entire modulus coefficient is well factorable at every split. For each fixed slot-one integer the number of possible $(a,b,d)$ is $O_\eta(1)$: the two prescribed prime divisors are both at least $x^{2\eta}$ in a polynomially bounded integer, and they determine $d$. Its resulting coefficient is independent of the other two slots and is 1-bounded after division by an $\eta$-dependent constant. The unit mask $(Kd,N)=1$ factors. The short source $s$ is a genuine prime sequence in independent intervals and satisfies the required SW and roughness hypotheses. Removing its finitely many possible polynomial prime divisors of $N$ respects SW, also with the source auxiliary coprimality restriction (at most its number of prime divisors are removed on these actual prime sequences). For all source pairs on the intended size support, $(s q,Kd)=1$ automatically: $s,q$ are above $z$, and both bands differ from $p,c$.

Explicitly, for $v_i=\log_x Q_i, \beta=\log_x S, \theta=7/32$ and $\eta\le10^{-4}$, the upper centers satisfy $v_1\le.01244, v_2\le.218001, v_3\le.282002, \beta\le.1011$, with $\beta\ge.1009$. The four strict rails, before fixed small theorem reserves and vanishing dyadic adjustments, have
\[
\begin{split}
   v_1-\beta&\le -.08846,\\
   2\beta+v_2+2v_3&\le .984205,\\
   \theta+\beta+v_1+5v_2+2v_3&\le 1.986299,\\
   (1+2\theta)\beta+v_1+(5-2\theta)v_2+(2+2\theta)v_3&<1.840.
\end{split}
\tag{6}
\]
The true factor $N^\theta$ in the third condition is paid (its $2^\theta$ costs $o(1)$ in the exponent); $0<N<x^{1+\varepsilon}$ for any fixed allowable positive $\varepsilon$ and sufficiently large $x$. Uniformly smaller $d$-dyads are allowed.

For the sharp central product restriction, first use dyadic and relative $L^{-B}$ Cartesian boxes on $s,q$. Whole interior boxes have independent source sequences. The omitted physical edge is $O(xL^{-B})$ integers $n=s q$ adjacent to the two fixed endpoints. Each has bounded source multiplicity and at most a fixed divisor power of $N-n$ in the modulus slots and sieve labels. Cauchy with the global divisor moments makes this edge log-small to any prescribed order for sufficiently large $B$. In the reduced mean the sum of modulus weights with $1/\phi(Kd)$ is at most a fixed divisor-harmonic log power, so the same edge is log-small there. The product source remains at full scale even though $q\asymp x/S$. Proposition 5.2 thus gives total remainder $O_{A,\eta}(xL^{-A})$, after summing the polylogarithmically many dyads and boxes. One may remove $q\mid N$ from its independent source, which at this size just deletes $O(1)$ primes per dyad.

In the reduced mean for fixed $K$ the local ratio is
\[
 g_K(\ell)=\phi(K)/\phi(K\ell)
   =\begin{cases}
     1/\ell,&\ell\mid K,\\
     1/(\ell-1),&\ell\nmid K .
   \end{cases}
\tag{7}
\]
Only primes $\ell\nmid N$ are sifted. This is uniformly covered by the dimension-one linear sieve: its usual product upper condition follows from the one for $1/(\ell-1)$ at odd primes by omitting primes or decreasing these densities. Its Euler product is $\asymp \mathfrak S(N)/\log z$, uniformly: the local changes at the two small marks are $1+o_\eta(1)$, and removing prime divisors of $N$ above $z$ from the singular product changes it by $1+o(1)$. See, for example, [Iwaniec, Rosser’s sieve, Theorem 1 and §3](https://www.impan.pl/shop/publication/transaction/download/product/102606?download.pdf=), also [Matomäki, Lemma 2](https://users.utu.fi/ksmato/wp-content/uploads/sites/1432/2025/04/Goldbach_k2pl2p1.pdf) for its bounded-remainder coefficient form and [Lichtman, §7](https://arxiv.org/html/2309.08522v1#S7) for the linear dimension formula with positive $f(3)$; the weights used here are the standard lower linear sieve weights in that theorem. For fixed $s$, the PNT gives genuine $q$ mass $\asymp x/(sL)$ in $(x/(2s),x/s]$. Since $1/\phi(K)\ge 1/K$, the labelled-row count is at least
\[
       c_0 R_N+O_{A,\eta}(xL^{-A})
\tag{8}
\]
with an absolute $c_0>0$ independent of sufficiently small fixed $\eta$. The scale in (4), including the true $\mathfrak S(N)$, will also be used for all of the exceptional subsets below.

## 2. Exact parity-independent negative plateau

For now take $m$ squarefree and discard the midpoint seam $m$ having a divisor in $(U,\sqrt m)$, priced in §4. All prime factors of $m$ are at least $x^{2\eta}$ and eventually greater than both $V$ and $Q_0/U=H^2$. Thus the polynomial powers and joint cutoff in $C$ are inactive once $d>U$, and the exact identity $\mathbf1*\Lambda=\log$ gives
\[
   C(m)=\sum_{\substack{d\mid m\\d>\sqrt m}}\mu(d)\log(m/d)
       =\mu(m)\sum_{d\mid m,\,d<\sqrt m}\mu(d)\log d .
\tag{9}
\]
This is an evaluation of $C$ itself on these actual rows; it does not use $J$ or a principal-term substitution.

Put $G=cab w, \Delta=\frac12\log m-\log p$, and define
\[
 S_\Delta(G)=\sum_{u\mid G,\,\log u<\Delta}\mu(u),\qquad
 H_\Delta(G)=\sum_{u\mid G}\mu(u)(\Delta-\log u)_+ .
\]
The full Möbius-log moment is $-\Lambda(G)=0$ because $G$ is squarefree and composite. Split the truncated log moment in (9) according to whether $p$ divides its argument, then complement the first partial sum inside $G$, using $\frac12\log m=\log G-\Delta$. If $Z_\Delta=\sum_{\log u<\Delta}\mu(u)\log u$ over divisors of $G$, the truncated moment before multiplication by $\mu(m)$ is
\[
  -(\mu(G)\log G+\log p)S_\Delta+(\mu(G)-1)Z_\Delta .
\]
Consequently
\[
   C(m)=
   \begin{cases}
     (\log m)S_\Delta(G),&\mu(G)=+1,\\
     2H_\Delta(G),&\mu(G)=-1 .
   \end{cases}
\tag{10}
\]
Strict ties at $\Delta$ cannot occur on this squarefree physical support, since $p u=\sqrt m$ would be an integer divisor.

Let $A=\log a, B=\log b$, and $\delta=\Delta-\log c$. For sufficiently large $x$, (2) implies $.97\eta L<\delta<1.03\eta L<\min(A,B)$, and no nonunit divisor of $w$ is at most $e^\delta$. Expand the $c$, $a$, $b$ bits exactly. Write $D_{A,B}(v)=1_{v>0}-1_{v>A}-1_{v>B}+1_{v>A+B}$ and $E_{A,B}(v)=v_+-(v-A)_+-(v-B)_++(v-A-B)_+$. Both vanish outside the interval between $0$ and $A+B$ (up to strict endpoints), $|D_{A,B}|\le 1$, and $|E_{A,B}|\le\min(A,B)$. Then
\[
\begin{split}
 S_\Delta(G)&=-1+\sum_{d\mid w}\mu(d)D_{A,B}(\Delta-\log d),\\
 H_\Delta(G)&=-\delta+\sum_{d\mid w}\mu(d)E_{A,B}(\Delta-\log d).
\end{split}
\tag{11}
\]
The $c$-bit contributes exactly $-1,-\delta$ because the only available short product on that side is $1$. Use the fixed-for-$p$ interval
\[
 \mathcal I_p=\{d>0:|\log d-(L/2-\log p)|\le5\eta L+1\}
\tag{12}
\]
for all possible supports in (11), and put $j=\#\{d\mid w:d\in\mathcal I_p\}$. For $j=0$, (10) gives $C(m)\le-\eta L$ in **either parity**. For $\mu(G)=-1$ and arbitrary $j$ the positive part is $O(\eta L j)$. For $\mu(G)=+1$, an order-$L$ defect has **no positive part until two distinct neck divisors appear**: $S_\Delta(G)_+\le(j-1)_+\le j(j-1)/2$. The quadratic fact is what makes a strict signed reserve feasible; an absolute estimate of single-neck mass alone does not suffice.

## 3. Actual one- and two-neck upper counts

For either computation fix the genuine marked primes $s,p,c,a,b$ from the lower-sieve normalization. In subsequent divisor openings let $D_0$ be the product of $K$ and the fixed factors from $w$, leaving one unmarked factor $y$ free with $m=D_0y\in[x,3x/2)$. On any actual viable unit row one has $(s,D_0 N)=1$ and $(D_0,N)=1$. Thus
\[
   y=y_0+s v,\quad y_0\equiv N\overline{D_0}\pmod s,qquad
   q=\frac{N-D_0 y_0}{s}-D_0v .
\]
Use an upper Selberg sieve for $y$ with $P^-(y)>z$ and the actual prime $q>x^{.89}$, in the free interval of length $\asymp Y=x/(sD_0)$. Each time below $Y\gg x^{.038}$. Extra interval conditions can only decrease the count. The two affine forms have two distinct roots modulo a prime $\ell\nmid N s D_0$; they have one root modulo every other prime: roots coincide at a prime of $N$, a nonunit coefficient has nonzero constant at a prime of $D_0$ or $s$, and at $2$ this uses even $N$. In particular the local factor at $s$ is accounted for rather than assuming two invertible leading coefficients.

It follows uniformly that the count is
\[
     \ll \mathfrak S(NsD_0)\frac{x}{sD_0 L^2}
      \ll_\gamma \mathfrak S(N)\frac{x}{sD_0 L^2},\qquad \gamma=.004 .
\tag{13}
\]
For a direct usual Selberg normalization use radius $R=x^{.002}<z$, root counts $\omega(\ell)$, and $h(\ell)=\omega(\ell)/(\ell-\omega(\ell))$. The fixed comparison $h_*(2)=1,h_*(\ell)=2/(\ell-2)$ gives $\sum_{d\le R}h_*(d)\gg\log^2 R$ over squarefree $d$. At exceptional odd primes $h_*-h=2/(\ell-2)-1/(\ell-1)$; the multiplicative convolution comparison costs $\prod_{\ell\mid NsD_0,\ell>2}(1+h_*(\ell)-h(\ell))\ll\mathfrak S(NsD_0)$. This is the [standard upper Selberg estimate, Theorem 30](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/#theorem-30), with $O(R^2 L^{O(1)})$ remainder from at most $2^{\omega(d)}$ roots and the exact interval count per root. This error is absorbed in (13). In the last inequality the additional prime factors are the fixed number of marked primes, $s$, and factors of $z$-rough integers dividing a number $\ll x$, hence at most $5+O(1/\gamma)$ primes; their factors $(\ell-1)/(\ell-2)$ are uniformly bounded. No ordinary distribution estimate for the prime $q$ in the moduli of (13) is needed.

Also, uniformly in any interval of logarithmic width $b_0$, the harmonic mass of $z$-rough integers $r>1$ is $O_\gamma((b_0+1)/L)$ when the integers are $\ll x$. Cover by $O(b_0+1)$ dyads; on dyads $r\asymp T$ with $T\ge z/2$ the elementary one-dimensional upper sieve gives $O_\gamma(T/L)$ survivors. One may take radius $\min(z^{1/2},T^{1/8})$, still of positive polynomial size. In an unrestricted interval $[1,O(x)]$ the total harmonic mass including $1$ is $O_\gamma(1)$.

For a single neck divisor $d\mid w,d\in\mathcal I_p$, write $w=d y$. The fixed $d$ uses exponent near $.282$, $y$ has exponent near $.218$, and (13) applies with $D_0=Kd$. Summing the harmonic $d$-mass in (12) yields
\[
                   \sum_{\rm labelled}j
        \ll_\gamma (\eta+1/L) R_N.
\tag{14}
\]
The same upper argument works for a $w$ divisor of exponent near either $.218$ or $.282$ in any prescribed shorter interval (with the other factor on its complementary scale).

For two distinct divisors $d,e\in\mathcal I_p$, write
\[
    w=g u v h,qquad d=g u,\qquad e=g v,\qquad
    g=(d,e),\quad (u,v)=1.
\]
All nonunit factors in this decomposition are $z$-rough. Both $u,v>1$, since otherwise the distinct divisors would have ratio at least $z$, whereas $\mathcal I_p$ has logarithmic width at most $10\eta L+2<\log z$. The exponent bounds give $g/h=de/w>x^{.06}$, so $h<g$, and $\max(g,u,v)>x^{.140}$ since $g u=d\ge x^{.2814}$ for large $x$ in the stated boxes. In what follows choose one of $g,u,v$ that is largest as the free variable. The full central interval then gives $Y\gg x^{.140-.1011}\gg x^{.038}$; when it does not, the selected case is empty. All the complementary divisors $w/d=vh$ and $w/e=uh$ occupy a common interval $\mathcal J_{K,p}$, of logarithmic width $10\eta L+O(1)$, because $\log w=L-\log K+O(1)$; its center is $L-\log K-(L/2-\log p)$. The other roles are:

- If $g$ is free, fix $h$, and impose the two **independent** harmonic restrictions $u h,v h\in\mathcal J_{K,p}$ on $u,v>1$. Sum the unrestricted $h$-mass, including $h=1$.
- If $u$ is free, fix $v$. For $h>1$, impose $g v\in\mathcal I_p$ and $v h\in\mathcal J_{K,p}$, two independent harmonic restrictions on $g,h>1$. Sum the unrestricted $v$-mass. For $h=1$, first restrict $v\in\mathcal J_{K,p}$, then $g v\in\mathcal I_p$. This still supplies two separate restricted harmonic sums.
- If $v$ is free, use the same argument with $u,v$ interchanged.

After this separation all remaining restrictions on the free variable may be discarded for (13), except its roughness and the original equation and central product. Exact possible squarefreeness and coprimality restrictions can only lower this upper count. Each of the three cases thus contributes $O_\gamma((\eta+1/L)^2)$ times the scale in (4). This proves
\[
            \sum_{\rm labelled}j(j-1)
                 \ll_\gamma(\eta+1/L)^2 R_N.
\tag{15}
\]
No independence of the occurrences of the two neck divisors on the physical equation was assumed.

## 4. Seam, square factors, and the physical signed sum

First, all non-squarefree labelled rows have a prime square with prime at least $x^{2\eta}$. The number of physical integers $m$ with such a divisor is $O(x^{1-2\eta}+\sqrt x)$; each has fixed divisor multiplicities and $|C(m)|\le L\tau(m)^2$. Using $\tau(m)=x^{o(1)}$ and fixed $\eta$ makes this $o(R_N)$ in count and $o(L R_N)$ weighted. One can avoid needing any occupancy estimate for prime powers. Actual $W_s(q)$ lies in $[1/2,1]$ on these exponent ranges for large $x$.

For the seam $U<d<\sqrt m$, write $d=e d'$ with $e\mid K,d'\mid w$ after removing squareful rows. The possible affected $\log d$ all lie in $L/2+O(\log H+1)$; the complementary divisor $m/d$ lies in the same type of interval. If $e$ includes both $p,c$, then $e$ itself is separated from $x^{1/2}$ by a gap of at least $.9\eta L$ in the log, whether the two tiny marks are included or not. A nonunit $d'\mid w$ has log at least $\gamma L$, much larger than the gap. Thus neither $d'=1$ nor $d'>1$ can occur in the seam for all sufficiently large $x$. If $e$ includes neither $p,c$, complement the original divisor, reducing to the both-included case. If $e$ includes exactly one of $p,c$, then $d'$ has exponent near $.218$ or $.282$, and its possible logarithmic interval has width $O(\log H+1)$ for fixed $e$. There are at most 16 choices of $e$; the single-neck argument following (14) bounds the labelled seam by
\[
                   O_\gamma\big((\log H+1)R_N/L\big)=o(R_N).
\]
On this squarefree rough-marked support the number of factors is bounded by $4+O(1/\gamma)$. The absolute $C$-mass of the seam is accordingly $o(LR_N)$, with no need to use (9) there.

The count of good labelled rows ($j=0$, squarefree and outside the seam) is at least $c_0R_N-O_\gamma(\eta R_N)-o_\eta(R_N)$. A physical row has at most a bounded number $M_0$ of labelled witnesses, independently of small $\eta$: the tiny marks are unique since their disjoint ranges lie below $z$ and $w$ is $z$-rough; there are at most five choices each of $p,c$ by size. Thus the physical good union has at least a fixed positive multiple of $R_N$ rows for sufficiently small fixed $\eta$. By (10)–(11) and the true weight $W_s$, they supply at most $-c_1\eta L R_N$, $c_1>0$ independent of small $\eta$. This deduction uses a lower bound on the number of negative rows, not division of an already-summed signed expression by multiplicity.

For all positive off-seam rows use any of their labelled witnesses, and bound the positive union by the sum of the positive bounds over all labels. By (11), (14), (15) their contribution is at most
\[
  O_\gamma\!left(L R_N\big[\eta(\eta+1/L)+(\eta+1/L)^2\big]\right).
\]
The exceptional contributions already cost $o_\eta(LR_N)$. Choose $\eta>0$ sufficiently small relative to the absolute positive lower constant and the upper constants at the fixed $\gamma$, then take $x$ sufficiently large. The physical sum is at most $-c_2\eta L R_N$ with $c_2>0$. Finally $L R_N=2\Sigma(x,N)M_N$ and $\Sigma(x,N)\gg\eta^2$, giving (3).

The use of the literal midpoint branch is important. The related $C^\dagger=C+P-J$ has a different parity weight; this proof does not attach (3) to it. Also, the large-$p$ configuration with three comparable small marks can put a single prime of exponent nearly $1/2$ in the modulus. A triply well-factorable prime theorem does not admit that arbitrary modulus weight, and none of the three slots of Lichtman's Proposition 5.2 fits such a single factor on the present actual $s,q$ source. The two independent moderate primes in (5) are what supply a valid strictly supercritical marked lower sieve here.

## Comparison

The repository's [balanced lifted signs](BalancedSemiprimeRaisedSign.md) and
[actual favorable rank-six profiles](FullFavorableRankSixAbsorption.md)
specify the sign on individual factor shapes. The point here is a fixed-target
**net** negative mass for the original coefficient on the larger union
with arbitrary remaining rough cofactor, pricing one and two actual
divisor necks differently. See [Pham, October 2026 v1](https://www.preprints.org/manuscript/202610.3061)
for a different reflected prime/rough-row comparison, and the [November
weighted Chen preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf)
for a different sieve construction with factored modulus supports.
Neither is used for the sign or claimed to be superseded. The only
supercritical dispersion used here is Lichtman's cited ordered-slot
proposition in its stated range.
