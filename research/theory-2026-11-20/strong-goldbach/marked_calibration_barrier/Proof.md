# Why the marked-flat positive tail cannot be uniformly small

This is a limitation on a proposed upper bound, not on the original Goldbach conjecture. It uses genuine products of independent primes, averaged over the resulting **even targets**; it does not posit a counterfeit model at a prescribed target.

Fix a smooth nonnegative nonzero $W$ supported in $(1/3,2/3)$, not necessarily symmetric. Write $L=\log P,\ F=n(P-n),\ X_P=P\int W$ and use the usual Goldbach singular series $\mathfrak S(P)$ as in the [coupled-product theorem](https://github.com/mxym/math/commit/5190f4df). Let $K$ be its sharp quadratic hinge or a common fixed smooth version with symmetric probability density supported on $[-\delta,\delta]$, $0<\delta\le10^{-5}$. In the sharp case put $v=0$; otherwise set $v=\int u^2\nu(u)\,du\le\delta^2$.

Consider a detector on squarefree rows with the coupled $K$ minus a finite sum of real (possibly signed) contributions
$$
 L^2\sum_{\substack{\ell\mid F,\ \ell\ {\rm prime}\\\ell\le\sqrt P}}
   c_j(\log\ell/L)\sum_{d\mid F}\mu(d)\psi_j(\log d/\log\ell).
$$
Each $\psi_j$ equals 1 at 0 and vanishes at arguments $\geq1/4$. Lower tag cutoffs are allowed if they include $P^{1/7}\leq\ell\leq P^{7/15}$ asymptotically (a fixed cut inside this window can instead be absorbed as a zero amplitude). Amplitudes have fixed, bounded, piecewise continuous restrictions to compact intervals in $(0,1/2)$, allowing uniform $o(1)$ perturbations there. Write $c=\sum_j c_j$. This includes normalized finite real linear combinations of the [fixed-rank weights](https://github.com/mxym/math/commit/f39f90b2) sharing the same base, and the [fixed-cut smooth variants](https://github.com/mxym/math/commit/0fe054ab). A positive mixture is not required.

Suppose the resulting $D$ keeps its positive signed mean $8X_P\mathfrak S(P)+o(X_P\mathfrak S(P))$ on physical squarefree rows and its genuine prime atom $4G$ (diagonal negligible). Suppose that it suppresses the rank-three contamination on the interval in the following weak sense: the total weighted positive part there is $o(X_P\mathfrak S(P))$ for all large even $P$, or even just after dyadic target averaging. Then, with $V_T=\sum_{T<P\leq2T,\ 2\mid P}X_P\mathfrak S(P)$,
$$
\liminf_{T\to\infty}V_T^{-1}
 \sum_{T<P\leq2T,\ 2\mid P}\sum_{\substack{n:\, F\ {\rm squarefree}\\
                             n,\ P-n\ {\rm both\ genuine\ semiprimes}}}
 W(n/P)(-D(F))_+ > 8.25 .
\tag{1}
$$
Consequently the average **positive** non-prime-pair mass of $D$ is $>12.25 V_T$ asymptotically in the liminf sense. If all nonprime total ranks $\leq r$ have negligible positive part, the same lower bound applies above $r$. In particular, a target-uniform bound below $8X_P\mathfrak S(P)$ for just that positive tail is impossible. The genuine *signed* compensation in those low ranks cannot be discarded. There is no assertion that these counts hold separately on every even target, or that a signed upper bound taking account of negative mass cannot work.

## Two profile evaluations

Set $A=1/7,\ B=7/15$. A row $p+ab=P$ with distinct odd primes, $a<b$, and $\log a/\log(ab)=t\in[A,B]$ has exactly one eligible tag $a$ for large $P$. The two larger prime factors exceed $\sqrt P$, and the divisor kernel at $a$ equals one for every shape, because all nontrivial divisors are $\geq a$. Replacing $\log(ab)$ by $L$ changes the normalized exponent by $O(1/L)$ uniformly.

Uniformly on these macroscopic profiles the value of $K/L^2$ tends to $8t(1-t)-4v$. Indeed the three labels $1,a,b$ are strictly inside the hinge cutoff by a fixed exponent gap, and contribute the full quadratic and its variance with signs $+,-,-$. The two labels $p,ab$ are each at exponent $1+O(1/L)$ in base $P$, occur with opposite signs, and their normalized values differ by $O(1/L)$. The other three labels are outside by a fixed exponent gap. The variance contribution from $1,a,b$ is therefore $-v(\log F/L)^2=-4v+o(1)$. This includes the sharp case without a smoothing loss. By the independent prime average below the suppression hypothesis implies
$$
                    c(t)\geq8t(1-t)-4v
          \quad\hbox{for almost every }t\in[A,B].
\tag{2}
$$
In fact any positive-measure violation contributes a strictly positive averaged rank-three mass, with density $2\,dt/[t(1-t)]$ for the two orientations.

Now take ordered legs $ab$ and $hj$ with four distinct odd primes, $a<b,\ h<j$, and respective smaller exponents $t=\log a/\log(ab)$, $u=\log h/\log(hj)$ in $[A,B]$. Both larger prime factors exceed $\sqrt P$. The only tags are $a,h$, and *all* nontrivial divisor-log ratios to either tag are at least $A/B+o(1)>1/4$. Every marked inner sum is thus **exactly 1**. Also $K=0$ exactly on this even rank; complementary divisor bits reduce the kernel to the fourth alternating difference of a quadratic. Hence $D/L^2$ tends to $-c(t)-c(u)$ away from discontinuities. Formula (2) gives the joint negative cost, in units $V_T$, of at least
$$
16(B-A)\,H-8v H^2,\qquad
H=\int_A^B \frac{dt}{t(1-t)}
   =\log\left(\frac{B/(1-B)}{A/(1-A)}\right)=\log(21/4).
\tag{3}
$$
There is no extra factor $1/2$: the legs are ordered and on each leg the smaller prime has already been distinguished. Here $B-A=34/105$ and $8/5<H<2$, so (3) exceeds $16(34/105)(8/5)-32\cdot10^{-10}>8.25$. For example $e^{8/5}<5<21/4$ follows from the exponential series with geometric tail, and $e^2>21/4$.

## Verification of the target average and its normalization

The even-target mean of $\mathfrak S(P)$ is 2. Indeed expand the finite product over odd target primes as $\sum_{d\mid P}h(d)$ with $h$ supported on odd squarefree integers and $h(p)=1/(p-2)$. The mean after counting multiples of $2d$ follows by dominated convergence since $\sum h(d)/d=\prod_{p>2}(1+1/[p(p-2)])=C_2^{-1}$, where $C_2=\prod_{p>2}(1-(p-1)^{-2})$. Partial summation gives $V_T\sim(\int W)\int_T^{2T}s\,ds$.

For independent central integers $n,m$ with $s=n+m\in(T,2T]$, changing variables to $s$ and $x=n/s$ gives $dn\,dm=s\,ds\,dx$. Replacing each distinct macroscopic prime factor by density $dw/\log w$ in the rank-three and rank-four sums is an ordinary multivariate consequence of the prime number theorem, not a Goldbach asymptotic. More explicitly, separate the prime variables into multiplicative boxes of fixed ratio $1+\xi$ on $[T^{A/2},2T]$. On all boxes the one-dimensional prime counts are their logarithmic integrals times $1+o_\xi(1)$ uniformly, so for nonnegative bounded weights one may sum the product upper and lower Riemann approximations. Endpoint boxes differ by relative $O(\xi)$ strips in $s/T$ or in physical shares, and by $O(\log(1+\xi)/\log T)$ strips at the exponent cuts. Enclose the finitely many discontinuities first by intervals of arbitrarily small total length for piecewise continuous amplitudes. Take $T\to\infty$, then $\xi\downarrow0$ and the discontinuity enclosures to zero. Collisions of prime labels give a power saving: a shared prime $p\geq T^{A/2}$ on opposite legs restricts both integers to its multiples, with total $O(T^{2-A/2+o(1)})$ by the divisor bound and $\sum_{p\ge T^{A/2}}p^{-2}$; equal factors on a single leg cannot occur on these exponent boxes. All these prime tuples give even $s$ automatically.

On a semiprime leg $n=ab$ use $t=\log a/\log n$. The Jacobian is $da\,db=(da/a)\,dn=(\log n)\,dt\,dn$; hence the prime density becomes $dn\,dt/[\log n\,t(1-t)]$. A prime leg has density $dm/\log m$. Since central $\log n,\log m=L+O(1)$, the normalized density after multiplying by $L^2$ is respectively $dt/[t(1-t)]$ for one semiprime and $dt\,du/[t(1-t)u(1-u)]$ for two. The physical integral of $W(x)$ factors out, for either orientation individually, with no symmetry assumption on $W$. This proves the claims used in (2) and (3). The same ordinary PNT calculation with two prime legs and the original log-prime weights gives $\sum_P G(P)\sim V_T$.

Finally the identity between signed mass, positive mass and negative mass gives total nonprime positive mass at least total mean minus the prime positive contribution plus any displayed negative submass. After division by $V_T$ this is at least $8-4$ plus (3), proving the assertion. The instance prevents trying to close the *absolute or positive-part-only* tail through a better generic bound. It does not exclude differently supported tests that distinguish the two marked balanced semiprime factors, or estimates of their actual cancellation against other configurations.

## Comparison

[Arneth’s September signed Euler-block paper](https://zenodo.org/records/23016171) uses a different averaged semiprime obstruction to a global energy criterion. His [October cubic minorant](https://zenodo.org/records/23477014) isolates a separate signed fixed-target correlation. The obstruction here is calibrated by actual prime–semiprime and semiprime–semiprime profiles for the precise singly marked quadratic bank. It does not apply to a coupled two-tag counterterm or establish priority.
