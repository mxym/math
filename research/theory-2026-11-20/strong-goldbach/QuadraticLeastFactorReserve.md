# Positive signed mass between two true least-factor ranges

For a prescribed large even $P$, write $L=\log P$, $I=[P/3,2P/3]$,
$X_P=|I|\mathfrak S(P)$, with the usual ordered Goldbach singular series
$2\prod_{p>2}(1-1/(p-1)^2)\prod_{2<p\mid P}(p-1)/(p-2)$.
Set $J=[.025,.065]$, $K=[.00025,.0005]$, $g(s)=(1-2s)_+^2$.
Take **all** squarefree target-unit pairs $x+y=P$, $x\in I$ with
$\log P^-(x)/L\in J$ and $\log P^-(y)/L\in K$, together with their
transposes. This bank is prime-free on both sides. The cofactor ranks
are arbitrary within the implied physical range.

Use the **actual** $R=2$ symmetric score $J_2$ of the
[bounded-rank theorem](https://github.com/mxym/math/commit/74d3b0e858f37c871ca0ba6d7b732d0bebaf06b9),
with its patch up to $P^\theta$, medium cutoff $D=P^{1/2-\theta}$,
physical roughness $P^{\theta^2}$ and ideal own-log quadratic on rank two.
For every sufficiently small fixed $\theta>0$, then sufficiently large $P$,
$$
              \sum_{\rm bank} J_2(x)J_2(y)>.0011X_P.                    \tag{1}
$$
This is a **signed** lower bound with no absolute value on the left.
Choose the global calibration error in the cited result below $.00005X_P$
simultaneously with (1). A lower bound $-1.001X_P$ on the complement
of this bank would now suffice for a genuine central prime pair.
That lower bound is not proved.

There is also an independently counted population of $\gg X_P/L^2$
genuine rank-two by rank-two **or** rank-three pairs in the first
orientation, with both actual scores negative, bounded away from zero
in units of $L$. This does not give separate lower bounds for the two
different partner ranks or assert that the low ranks pay all of (1).

## 1. Arithmetic transfer on the actual source

Write $\ell=P^-(x),\ r=P^-(y),\ x=\ell a,\ y=rm$, and
$t=\log\ell/L,\ w=\log r/L$. Impose $P^-(a)>\ell,\ P^-(m)>r$.
Put $g_\theta(s)=g(s){\bf1}_{s\le1/2-\theta}$ and
$H^\theta_b(s)=g_\theta(s)-g_\theta(s+b)$; write $H_b$ for the same
difference without truncation. For $\theta<.00025$ only the divisor 1
enters the patch. On a rank-two input of the bank, its small prime is
in $J$ or $K$ (in log exponents) and the other exceeds $P^{.9}$, so
no root seam hits. The scores divided by $-L$ can be replaced by
$\sum_{d\mid a}\mu(d)H^\theta_t(\log d/L)$ and its $m,w$ counterpart.
Replacing own-log denominators by $L$ costs $O(1/L)$ per normalized
row: all divisor counts are bounded by a fixed constant on these
polynomially rough inputs; the actual cutoff is $D$, not a moving
square root. There are $O(X_P/L^2)$ rough candidate pairs by the
ordinary dimension-two upper sieve on $x(P-x)$ up to $P^{.0002}$:
the integer CRT errors cost at most $2^{\omega(d)}$ per modulus,
and a prime of $P$ has one forbidden root rather than two, giving
the stated local factor. Thus normalization costs $o(X_P)$.
Squareful rough rows are negligible at cost $P^{1-.00025+o(1)}$:
sum $P/p^2+1$ over $P^{.00025}<p\le\sqrt P$ and allow
divisor-power multiplicities. The same bound holds in expanded
weights on the exceptional $r^2$ and $\ell^2$ rows, by the pointwise
divisor bound. On the source any common prime of $x,P$ exceeds
$P^{.025}$, so all such rows likewise cost $P^{1-.025+o(1)}$.

[Fouvry, *Autour du théorème de Bombieri–Vinogradov II*, Corollaire 1,
pp.617–619](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf)
permits a short prime coefficient in $[N,2N]$, arbitrary long
order-$k$ coefficient in $[M,2M]$, and **arbitrary** order-$k$
coefficient on the reduced moduli. For a common residue $P$ with
$|P|\le X=4MN$, the centered discrepancy subtracts the actual
modulus-coprime source divided by its totient. It has arbitrary fixed
log saving if $N\ge X^\delta$ and
$$ QX^\delta<\min(X^{1/2}N^{1/2},X^{4/7}N^{-6/7}) $$
with a fixed power margin. On $J$ the infimum of the two exponents is
at least $.5125$. Condition (1.3) on the short prime, including its
interval and auxiliary unit mask, follows by prime Siegel–Walfisz at
log-power moduli and the elementary integer bound $O(N/q+1)$ beyond a
chosen log power; auxiliary exclusions remove only their prime factors,
within Fouvry's divisor allowance. Deleting primes dividing $P$ costs
$O(L)$. Split $\ell,a$ into independent fine boxes of relative size
$1+L^{-B}$ with their own lower endpoints for $N,M$, so
$4MN>(4/3-o(1))P$. The number of boxes is polylogarithmic.
Freeze $t$, the comparison $P^-(a)>\ell$, and the central source
endpoint. A roughness disagreement forces two prime factors of $x$ to
lie within a factor $1+O(L^{-B})$. Counting even integer choices costs
$O(PL^{1-B}+P^{1-.025+o(1)}+P^{.14})$ multiples, by summing
$P/(\ell v)+1$ for $|v-\ell|\ll\ell L^{-B}$, including one endpoint.
If a jump of $g_\theta$ is crossed when freezing $t$, a divisor of $x$
of the form $\ell d$ is within $O(DL^{-B})$ of $D$; this costs
$O(PL^{-B}+P/D+D)$ multiples. The endpoint of $I$ costs
$O(PL^{-B}+1)$. These are **global** strips. Cauchy with fixed divisor
moments of $x,P-x$ pays the expanded weights by enlarging $B$;
the corresponding principal harmonic sums cost only fixed log powers.
Away from the seams all other weight freezing costs arbitrary log
savings by Lipschitz continuity. The long source, including its positive
or negative part, is now an order-$k$ weight independent of the short
prime. Choose Fouvry's log accuracy last. In particular this is not a
claim that Lichtman's [Theorem 1.7 and §6.1](https://arxiv.org/html/2309.08522)
for true prime progressions with special modulus weights applies to a
premarked prime times an arbitrary signed half-divisor.

For fixed $r\nmid P$, keep only rough squarefree $q\mid m$ with all
factors $>r$ in its signed divisor weight. This is exact on the desired
rows. Sieve $m$ against primes below $r$, except target primes and $r$
(the extra $r^2\mid y$ exception was just paid). Use upper/lower
dimension-one linear sieve weights at $E=P^{.0096}$. For an upper or
lower bound choose the correct sieve according to the signs of the
long source and $\mu(q)H^\theta_w(\log q/L)$; the latter sign may
depend on $r$. Here $b$ is the sieve modulus, $(r,q)=(b,rq)=1$,
and the physical modulus $rqb\le P^{.5101}$ is strictly inside the
range. Collect all $r,q,b$ with arbitrary independent signs for $r$
when required: the modulus coefficient is bounded by a fixed divisor
power. Thus one uses Fouvry per box and sign split, not once at full
cost per $r$.

In the principal the test requires $(bqr,xP)=1$. Every prime of $x$
exceeds $r$, so the $b$ local density is $1/(p-1)$ for primes
$p<r,\ p\nmid P$. Mertens yields $V_P(r)\sim e^{-\gamma}\mathfrak
S(P)/(wL)$ uniformly: target primes beyond $r$ change the product by
$1+O(L/r)$. On $q$, omitting primes $>r$ dividing $xP$ costs $o(1)$
in its absolute harmonic sum at these fixed exponents. The signed
rough $\mu(q)/\phi(q)$ measure in $v=\log q/\log r$ converges on
compact intervals to $\nu=\delta_0+\rho'(v)dv$, with $\rho$ Dickman's
function. Indeed sum ordered squarefree tuples with their factorial,
apply prime Mertens to the measures $du/u,\ u\ge1$, and discard the
negligible diagonals. The resulting cumulative alternating integral
is 1 up to 1 and satisfies $v\rho'(v)=-\rho(v-1)$ thereafter.
This is uniform for the compact parameter intervals here; moving
boundaries away from the atom at zero are handled by squeezing.
Changing $1/q$ to $1/\phi(q)$ here costs $o(1)$ since all factors
are polynomially large. The unconditional absolute rough-divisor sum
is $\le1/w+o(1)$ by its full reciprocal Euler product.

For each $r$ the resulting multiplier, in units
$\mathfrak S(P)/(L\phi(r))$, is
$$
            D_y(w)=\frac{e^{-\gamma}}w\int H^\theta_w(wv)\,d\nu(v)
$$
up to $o_P(1)$ and a two-sided error of absolute size at most
$5\Delta(19)/w$, charging the **absolute** long source. In fact
$\|H^\theta_w\|_\infty\le4w+8\theta^2\le5w$. The dimension-one
sieve at ratio $.0096/w>19$ has upper/lower gap
$\Delta(s)=2e^\gamma\rho(s-1)/s$, decreasing in $s$; either endpoint
may be charged at the full gap. This follows by subtracting the
linear-sieve delay equations; see the [gap verification](https://github.com/mxym/math/commit/ca6fa82f).
Omitting target primes preserves the uniform upper dimension bound.
Since $\rho(n)\le1/n!$, $\Delta(19)<4/(19\cdot18!)$. This argument
does not equate a fixed-level fundamental lemma with exactness.

Now $-H_b'(s)=8b$ on $[0,1/2-b]$, and $0\le-H_b'\le8b$
thereafter. Integrating by parts and using $\int_0^\infty\rho=e^\gamma$
shows that for the untruncated test the loss from $8b$ is at most
$8b\int_{(1/2-b)/b}^\infty\rho$. Moreover $\|\nu\|_{\rm TV}\le2$,
and $\|H^\theta_b-H_b\|_\infty\le8\theta^2$. Uniformly on $K$,
choosing $\theta$ sufficiently small after the displayed ranges makes
$|D_y(w)-8w|\le10^{-7}w$. Including the preceding sieve gap still
costs at most $10^{-6}w$ on the absolute long source.

## 2. Signed ordinary source, then actual reflected sum

After fixing $\ell$ and opening a rough divisor $d\mid a$, the remaining
rough $k=a/d$ in $I/(\ell d)$ has ordinary density
$\omega((1-t)/t-v)/\log\ell$, $v=\log d/\log\ell$, with $\omega$
Buchstab's function. This interval has fixed endpoint ratio and the
Buchstab argument stays $>(1/2-t)/t\ge6.69$ up to $O(1/L)$.
Hence the usual ordinary rough-number asymptotic is uniform with
additive $o(1/\log\ell)$ in density; the absolute $d$ harmonics
are bounded at these fixed exponents. This is an integer-factor
law, not an assumption about reflected primes. Therefore the
ordinary signed source mass in units $|I|/(\ell L)$ is
$$
 D_x(t)=\frac1t\int H^\theta_t(tv)\,\omega((1-t)/t-v)\,d\nu(v)+o(1).
$$
Its absolute-outside-score analogue is at most $6/t+o(1)$: use
$\omega\le1$, $|H^\theta_t|\le5t$, and the absolute Euler upper
$1/t+o(1)$. Target-unit and squarefree omissions were already paid.

We have $D_x(t)>7.5t$. For $v'\ge6$,
$|\omega(v')-e^{-\gamma}|\le1/(2\cdot6!)$. Indeed the range on
$[1,2]$ has diameter $1/2$. On $[n,n+1]$ and subsequently the
function stays in the preceding range, by averaging in
$u\omega(u)=n\omega(n)+\int_n^u\omega(s-1)ds$. On this next interval
the diameter contracts by $1/n$ via
$u\omega'(u)=\omega(u-1)-\omega(u)$. The limit is $e^{-\gamma}$.
Replacement by the limiting constant therefore costs at most
$8/(2\cdot6!)+O(\theta^2/t)$ using the TV of the **limiting signed
measure**, not the TV of the discrete Möbius harmonics. The remaining
loss from $8t$ is at most $8t\sum_{n\ge6}1/n!+16\theta^2/t$.
Together these are smaller than $.5t$ on $J$ for small $\theta$.

Finally the two label harmonics tend to $dt/t,\ dw/w$. The first
orientation in units of $X_P$ has liminf at least
$$
 \int_J\int_K\big\{(7.5t)(8w)-(6/t)10^{-6}w\big\}
       \frac{dt}{t}\frac{dw}{w}>59|J||K|=.00059 .
$$
The reversed rectangle is disjoint, proving (1).

## 3. A genuine rank-two by rank-two-or-three interior population

Restrict $t$ to $J_0=[.052,.053]$ and require the long cofactor of
$x=\ell p$ to be a genuine prime $p$. Its ordinary count $B_0$ is
$(1+o(1))\,|I|L^{-1}\int_{J_0}dt/[t(1-t)]$ by PNT on the long
prime and Mertens on $\ell$. Keep source target units. For each prime
$r$ from the stated $K$ not dividing $P$, the multiset for the sieve is
the **actual** $m=(P-\ell p)/r$ whenever integral. Its main population
parameter is $B_0/\phi(r)$, its degree at level $Y=P^{.523}$ is
less than $1.914$ since $.523(1.914)>1$. Its local density for a
squarefree divisor $d$ coprime to $P$ is
$\phi(r)/\phi(rd)$, with prime factors $1/(v-1)$ if $v\ne r$,
$1/r$ if $v=r$. If $(d,P)>1$ the density and count are zero.
All the moduli $rd\le P^{.5235}$ fit Fouvry Corollaire 1 on $J_0$,
whose lower level exponent exceeds $.5259$. This includes $r^2$
when $r\mid d$. The sum over $r,d$ of the absolute remainders even
weighted by $3^{\omega(d)}$ has arbitrary fixed log saving by
collecting the signed modulus coefficients; $rd$ has at most $\tau(rd)$
mark choices. The true coprime principal differs from $B_0/\phi(rd)$
only when the prime factors $\ell$ or $p$ divide $rd$; these exceed
$P^{.051}$. In the absolute Euler harmonic over $d$ this costs at
most $O(P^{-.051}L^C)$ per source and unit $r$ after the reciprocal
$r$-factor. This proves the required aggregated remainder, not a
per-mark absolute discrepancy claim.

Use [G. Greaves, *The weighted linear sieve and Selberg's
$\lambda^2$-method*, Theorem 1, (1.5)–(1.9)](https://matwbn.icm.edu.pl/ksiazki/aa/aa47/aa4716.pdf),
with his integer $R=2$, $U=.942$, $V=.030$, $V+2U=1.914$.
In his notation take the nondecreasing least-prime weight
$$
 W(t)=0\quad(t<.08),\qquad
 W(t)=\min\{U-V,t-V,5t^2\}\quad(.08\le t\le1),
$$
extended constantly after 1. Its bounded-variation jump is harmless;
one can instead interpolate monotonically to the displayed weight on
$[.08,.08001]$, costing less than $.001$ in the positive main by the
same upper bound on $h$ below. The bounds (1.8) hold, since
$\max(V,(1-U)/2)=V$ and $5<9(U-1/3)$. His lower counts rows with
$\nu_{Y,U}(m)\le2$, weighted by $W(\log P^-(m)/\log Y)$;
small repeated primes are counted distinctly in $\nu$ before their
physical removal. The lower is $2e^\gamma(B_0/\phi(r))V_r(Y)$
times $\mathcal M(W)+o(1)$, less a remainder with modulus coefficient
bounded by $3^{\omega(d)}$. The local product
$V_r(Y)\sim e^{-\gamma}\mathfrak S(P)/\log Y$ follows by Mertens
and the harmless modification at $r$. Greaves' dimension hypotheses
are uniform on the upper side: all densities are at most $1/2$, and
the excess above the ordinary interval prime Mertens sum is bounded.
The allowed lower dimension loss from deleting primes of $P$ is
$O(1+\log\log P)$: split $\sum_{v\mid P}\log v/(v-1)$ at $\log P$.
His Theorem 1 error is $O(((1+\log\log P)/\log Y)^{1/5})$ and the
constant is uniform in this lower-side loss. The remainders above may
be summed after absolute values even though the weights depend on $r$.

The supplied exact integer checker verifies $\mathcal M(W)>.033$,
independently of the endpoint saturation constants commonly quoted from
Greaves. For clarity, its integral is
$$
 \mathcal M(W)=\int_0^{1/2}\frac{W(s)}{s}
       \left(\frac1{1-s}-h(s,1)\right)\,ds
       -\int_{1/2}^1\frac{W(1)-W(s)}{s(1-s)}\,ds .
$$
Here $h(s,1)=\sum_{i\ge2,\ i\ {\rm even}}h_i(s,1)$ uses the positive
simplex kernels preceding Greaves' (1.9). With maximum allowable
first coordinate $a=1/s_0$, write $h_i(s;s_0)=Q_i(s,a)$.
The first kernel is the integral of $dv/[v(1-s-v)]$ for
$\max(s,1/3)<v<\min(a,(1-s)/2)$. For $i\ge2$, removing the largest
coordinate and rescaling the remaining simplex gives the recurrence
$$
 Q_i(s,a)=\int_s^{\min(a,1/3)}
     Q_{i-1}\left(\frac{s}{1-v},\frac{v}{1-v}\right)
                 \frac{dv}{v(1-v)} .
$$
An empty integral is zero. All kernels vanish for $s\ge1/3$.
For $s\ge.08$ there are no $i\ge11$ since the $i$ variables and
the two further entries $s,1-s-\sum v_j$ are each at least $.08$.
The checker uses the mesh $1/600$ and upward integer rounding at
scale $10^9$. A cell stores an upper for the full $s$ interval and
the specified *upper endpoint* for $a$. In the first kernel replace
$1-s-v$ by its lower bound, at least $v$ on the actual domain. In the
recursion use all image $s$ cells touched, the upper image $a$, and
the lower endpoint for the increasing factor $v(1-v)$. Finally the
positive term is charged below and both debits above by endpoint
bounds. The arithmetic uses no floating point and works unchanged
under Python optimization.

Consequently the true tuple count exceeds
$.1\,(\log 2)\big(\int_{J_0} dt/[t(1-t)]\big) X_P/L^2$ for large $P$,
since $2(.032)/.523>.12$ and $0\le W\le1$.
Contributing $m$ have $P^-(m)\ge Y^{.08}=P^{.04184}$.
Discard any square of such a prime by the previous physical
square-divisor estimate, allowing all $(r,\ell)$ divisor choices;
now $\nu_{Y,U}(m)=\Omega(m)$. The small $r$ is distinct from every
factor of $m$, and is its resulting partner $y$'s *unique* smallest
factor. The short $\ell$ is likewise unique on $x$. Thus this is
a count of genuinely distinct ordered pairs inside (1).

For own-log coordinates, on a semiprime with smaller exponent $u$
the native quadratic divisor score is $4u(1-u)$. On a triprime with
ordered exponents $u\le v\le c$, $u+v+c=1$, it is $8uv$ for
$c\ge1/2$, and $2-4(u^2+v^2+c^2)$ otherwise. In the latter case
$v^2+c^2\le(1/2)^2+(1/2-u)^2$ by convexity whenever $u$ is the
small tagged exponent here. Thus all these scores are strictly
positive uniformly on the specified subset, with $u\ge.00025$ and
(for the triprime) $v\ge.04184$, up to vanishing normalization
errors. Actual rank-three truncation costs at most $32\theta^2+o(1)$
in the normalized score. Neither count nor native sign uses a
parity model for the other rows. The earlier [two-axis Chen
corner](https://github.com/mxym/math/commit/2f9bfe36) also has a
semiprime opposite a tagged prime-or-semiprime, by switching and with
different tag scales. The result here is chiefly the signed all-rank
mass (1) on a literal least-factor cut, not a priority claim for a
sum of two almost primes.
