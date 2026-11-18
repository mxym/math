# Independent internal review

**Verdict:** No mathematical gap found in the stated first transitions for the three- and four-dimensional cubes or their one-sided dimension-uniform consequences. This was an independent AI internal review, not external peer review. The two checkers use different arguments; neither is a formalization of the entire proof.

## Checks that determine the scope

* On any positive-dimensional face, condition on the transverse corner bits. Their Hamming weight does not change the uniform distribution of the free bits. The trace calculation on faces of dimension at least two is legitimate because no vertex lies in their relative interiors. The decreasing factor $e^{-sr}/r$ has nonpositive covariance with the increasing trace bracket. The crucial worst low-dimensional bound uses the corner value of the **mean** distance in a square, not its diameter. Both root enclosures are strictly below $4/(2+\sqrt2)$.
* For the positive edge weights $p_k$ in the [proof](PROOF.md), set $R(u)=\mathbb E_p[r_k(u)]$, including $r_0(u)=u$ for $u>0$. Independent differentiation gives
  $R'(u)=\mathbb E_p[u/r_k]+\mathrm{Cov}_p(r_k,-u(s/r_k+1/r_k^2))>0$:
  the first term is positive, and both covariance arguments increase with $r_k$. This independently confirms that $H(1-t)/H(t)$ decreases in $s$. At $t=0$ one must instead use the nonsingular values of $h_0$ and the $h_k$ for $k>0$.
* The lifting only uses $h_k(1-t)>h_k(t)$ at reflected points for $k\ge1$. It does not assume pointwise growth of each $h_k$ on $[0,1]$, which is not guaranteed in this scale range.
* Strict positive definiteness identifies a unique optimizer among all corner-supported probabilities. The negative one-sided derivative for $s>s_D$ excludes this measure only at the tested base dimension $D$. It is enough to establish the best common threshold over $d\ge D$, not the threshold of each $d>D$.

## Independent proof of the critical edge sign

The [second certificate](independent.py) uses exact rational arithmetic with no third-party packages. For each $k>0$ write $r=\sqrt{k+u^2}$, $c=e^{-sr}$. The contributions to $H'$ and $H''$, before multiplying by the positive binomial multiplicity, are

$$
c(k/r^3-su^2/r^2),\qquad c(s^2u^3/r^3-3ku/r^5-3sku/r^4).
$$

The $k=0$ contributions are $-se^{-su}$ and $s^2e^{-su}$. On each entire parameter bracket it checks $F''=H''(1-t)-H''(t)$ over the first quarter-edge and $F'=-H'(1-t)-H'(t)$ over the next, with 128 adjacent closed cells per region. Root and exponential enclosures come from integer square roots and repeated rational interval squaring of $1-x/m\le e^{-x/m}\le(1+x/m)^{-1}$, not from Taylor sums. The resulting **upper** bounds are:

| $D$ | $F''$ on $[0,1/4]$ | $F'$ on $[1/4,1/2]$ | $F(0)$ at bracket endpoints: lower bound at left; upper bound at right |
|---|---:|---:|---:|
| 3 | $-214588/10^6$ | $-19326/10^6$ | $8440/10^9$; $-4303/10^9$ |
| 4 | $-405304/10^6$ | $-32195/10^6$ | $4907/10^9$; $-8877/10^9$ |

At the exact parameter root, $F(1/2)=F(0)=0$. Strict decrease on the right implies $F(1/4)>0$. Concavity on the left puts $F$ at least as high as its chord from 0 to this strictly positive value. Together these give $F>0$ on the entire open half-edge.

Both verifiers were rerun with Python assertions disabled; their safeguards remain active. See [CHECKS.txt](CHECKS.txt) for outputs and [SOURCES.md](SOURCES.md) for scope and precedence.
