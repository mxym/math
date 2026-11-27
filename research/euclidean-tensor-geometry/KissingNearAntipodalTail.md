# An explicit near-antipodal tail for hypothetical 73- and 127-point kissing codes

Work on the unit sphere, with the kissing condition $x\cdot y\le 1/2$ for distinct points. Call $\{x,y\}$ an **$h$-near pair** when $\|x+y\|\le 2h$; its angle differs from $180^\circ$ by at most $2\arcsin h$. There is no lattice, root-system or exact-pair assumption.

**Theorem.** In each half of each row, the indicated number $a$ of disjoint $h$-near pairs is impossible in the stated dimension and cardinality. The integer $10^6h$ is exact; degrees are rounded **only** to illustrate the scale.

| 6D, 73 points: excluded pair count $a$ | $10^6h$ | angular defect (degrees) | 7D, 127 points: excluded pair count $a$ | $10^6h$ | angular defect (degrees) |
|---:|---:|---:|---:|---:|---:|
| 28 | 85 | 0.00974 | 55 | 43 | 0.00493 |
| 29 | 920 | 0.10542 | 56 | 475 | 0.05443 |
| 30 | 1800 | 0.20626 | 57 | 960 | 0.11001 |
| 31 | 2800 | 0.32086 | 58 | 1500 | 0.17189 |
| 32 | 4000 | 0.45837 | 59 | 2200 | 0.25210 |
| 33 | 5700 | 0.65318 | 60 | 3150 | 0.36096 |
| 34 | 8200 | 0.93966 | 61 | 4650 | 0.53285 |
| 35 | 19600 | 2.24614 | 62 | 11450 | 1.31210 |
| 36 | 30700 | 3.51851 | 63 | 18400 | 2.10860 |

For instance, 73 points in six dimensions cannot contain 36 pairs all within $3.5^\circ$ of antipodal; 127 in seven dimensions cannot contain 63 pairs all within $2.1^\circ$. Throughout these ranges the near-pair graph is already a matching: two partners strictly within $30^\circ$ of the same antipode would violate the $60^\circ$ separation. The same exclusions apply to larger codes by retaining the listed pairs and taking a subset of the indicated size.

The [exact-pair estimates](KissingAntipodalTradeoffSixSeven.md) count pairs only at inner product $-1$. Here the excluded interval has explicit positive length, including for codes with **no exact antipodes**. These are distance-distribution restrictions, not upper bounds of 72 or 126 on the unrestricted cardinality. For the broader context of interval counts, see [Musin's multipoint SDP framework](https://arxiv.org/abs/2309.13854); his near-antipodal experiments concern dimension four. The argument below instead combines a two-population kernel inequality with an existing local moment certificate.

## 1. Straightening the marked pairs without moving the residual code

Set $P=36$ in dimension six and $P=63$ in dimension seven. Suppose a code of size $2P+1$ has $a$ specified near pairs. Write their points as
$$m_i\pm t_i u_i,\qquad \|u_i\|=1,\quad m_i\perp u_i,\quad \|m_i\|\le h,\quad t_i=\sqrt{1-\|m_i\|^2}.$$
Averaging the two same-sign original constraints and then the two opposite-sign constraints gives
$$|u_i\cdot u_j|\le c_A=\frac{1/2+h^2}{1-h^2}.$$
For every unmarked point $z$ the two constraints give
$$|u_i\cdot z|\le c_M=\frac{1/2+h}{\sqrt{1-h^2}}.$$
The error between **two** marked axes is quadratic in $h$, not linear. Importantly, the remaining $2P+1-2a$ points still obey the *original* kissing constraint with one another.

Keep the marked axes fixed. Among kissing sets of that residual size satisfying the symmetric bounds $|u_i\cdot z|\le c_M$, take one maximizing its number $j$ of actual antipodal pairs. It need not realize the original midpoints; it belongs to a larger, nonempty class. Write $p=a+j$ for the total number of marked axes and residual pairs, and $q=2P+1-2p$ for the remaining singleton count.

## 2. A weighted projective test

Let $\lambda=c_A^2$, $f(t)=t^4-\lambda t^2$, $T=f(1)=1-\lambda$, and
$$f_0=\frac{3}{n(n+2)}-\frac{\lambda}{n},\qquad M=c_M^2(c_M^2-\lambda).$$
The nonconstant Gegenbauer coefficients of $f$ are nonnegative: the degree-two coefficient is $(n-1)(6/(n+4)-\lambda)/n$, positive in all rows, and the degree-four coefficient is positive. The spherical addition formula gives weighted energy at least $f_0$ times squared total weight. The even kernel $f$ is nonpositive for ordinary projectively compatible pairs ($|t|\le1/2$) and for two marked axes ($|t|\le c_A$). A marked–unmarked interaction costs at most $M$.

Consider $a$ marked axes together with $b=P+1-a$ ordinary unit representatives, the latter satisfying pairwise $|t|\le 1/2$ and the mixed bounds. Give each marked axis unit weight and distribute a total weight $B>0$ equally on the ordinary lines. Necessary is
$$f_0(a+B)^2\le Ta+2aBM+B^2/D,\qquad D=b/T. \tag{1}$$
In every row an exact choice of $B$ violates (1), so these $P+1$ lines are impossible. Thus $p<P$: if $p\ge P+1$, take the requisite residual pairs; if $p=P$, include the one remaining singleton. All relevant lines are distinct since $c_A,c_M<1$.

Put $s=P-p\ge1$, so $q=2s+1$. Join two residual singletons for inner product $<-1/2$. Each degree $d$ is at least two: otherwise insert the antipode of that singleton in place of its sole neighbor (or any other singleton when there is no neighbor), preserving the symmetric marked bounds and increasing $j$. Three pairwise negative edges are impossible by the squared norm of the sum of their three unit vectors. The neighbors of any singleton are therefore mutually projectively compatible; together with all paired axes they pass the hypotheses used in (1) on any subset of $P+1$ lines. Hence $2\le d\le s$, ruling out $s=1$.

## 3. The remaining weighted energy

Add the odd polynomial $0.46t^5+0.26t^3-0.081t$ to $f$, obtaining $F_\lambda$. Its odd Gegenbauer coefficients are nonnegative in dimensions six and seven by the recurrence in the [local moment proof](KissingAntipodalTradeoffSixSeven.md). Let $\delta=\lambda-1/4$. Compared with the kernel of that proof, $F_\lambda$ subtracts exactly $\delta t^2$ and has constant coefficient $f_0$. For a residual singleton of degree $d$, its diagonal and all its interactions with other singletons therefore have sum at most
$$K_d=\frac{1389}{1000}+U_d+(q-1-d)\frac4{625}-\delta(1+d/4).$$
Indeed, its $d$ negative neighbors have $t^2>1/4$, and the diagonal has $t^2=1$. Here $10^5U_d$ for $d=2,\ldots,8$ are $11258,11898,12538,13178,13818,14458,15098$. These are uniform bounds from the [rational Bernstein certificate](verify-kissing-antipodal-tradeoff.js), not fitted point samples.

Let $K=\max_{2\le d\le s}K_d$. Give each of the two artificial signs on a marked axis weight $1/2$, each true residual pair total weight $u$ equally split, and each singleton weight $v$. The odd terms cancel against any paired axis. Distinct unmarked interactions involving an actual antipodal pair have nonpositive even cost, and the marked mixed cost is at most $M$. Consequently
$$ f_0(a+ju+qv)^2\le T(a+ju^2)+2a(ju+qv)M+qv^2K.$$
Set $D=j/T+q/K$ and use $u=B/(TD)$, $v=B/(KD)$. Then $ju+qv=B$ and the necessary condition is again exactly (1), now with this new $D$.

For **both** uses of (1), the [standalone rational replay](verify-kissing-near-antipodal-tail.py) takes
$$ B=\frac{a(f_0-M)}{1/D-f_0}>0$$
and verifies that the left side exceeds the right side strictly. It checks the projective test in all 18 rows and the residual test for every possible $2\le s\le P-a$. All inputs are rational because only $c_M^2$ is used. Run the Python script (standard library only); the linked Node.js checker reproduces the separate continuum inequalities underlying $U_d$.
