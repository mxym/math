# The symmetric, recursively varying layered maximizer for 1324

**Theorem.** The packing density of the permutation pattern $1324$ is attained by a **unique layered permuton**. It has a single central decreasing interval and two reflected, countably infinite chains of decreasing intervals. Their endpoints and the density are specified below by a contracting scalar Bellman equation with a unique nonempty-layer choice at every positive tail length. The ratios between consecutive tail endpoints tend to $(\sqrt3-1)/2$ but vary even arbitrarily near zero. This is not a classification of nonlayered extremizers or finite permutations, nor a decision on algebraicity. Sliačan–Stromquist’s PP2017 abstract already reported the numerical value to at least 100 digits using Mathematica; the point here is a proof of the extremal structure, identifying equation, and a reproducible certificate, **not discovery of the decimal**.

Throughout this note every terminating decimal in an inequality denotes the indicated exact rational number.

## 1. Additive interval reward

Stromquist’s layered replacement theorem (Albert et al., 2002, Thm. 2.2) gives some layered maximizer at each finite size. For layered permutations/permutons the middle inversion of a $1324$-copy must be in a single decreasing block, with one point strictly before it and one strictly after it. Thus a block occupying $(a,b)$ contributes, after dividing density by $4!/2!=12$,
\[
 B(a,b)=a(1-b)(b-a)^2.
\]
For a finite collection of blocks the formula follows by independent uniform sampling; the finite permutation count instead uses the binomial coefficient for selecting the inversion, bounded by half the squared size. Normalizing by $\binom n4$ costs a factor $n^4/(n)_4\to1$. Conversely a finite partition is approximated by integer block sizes. More generally a layered permuton is given by countably many disjoint open decreasing intervals, with the remaining points on the diagonal (zero-length layers); then the score is the sum of the same contributions, since the sampled inversion almost surely lies in one of the intervals. Endpoints of intervals are immaterial. Finite truncation of any constructed countable partition with vanishing residual tail lengths gives the same limiting score.

Let $S(t)$ be the optimal unnormalized reward inside the left tail $[0,t]$ for $0\le t\le1/2$, with the factors $a,1-b$ still measured in the full unit interval. Reflection gives identical right-tail rewards. We now construct $S$ and prove optimality, including in the presence of diagonal dust.

## 2. A contracting tail optimization

On $I=[.35,.405]$, $0\le t\le1/2$, define
\[
 H_f(t,y)=y^3 f(ty)+(1-t)y(1-y)^2,\qquad
 (Tf)(t)=\max_{y\in I} H_f(t,y).
\]
This operator on continuous functions maps into continuous functions and is a contraction in supremum norm with constant $q=.405^3<.067$. Let $G$ be its unique fixed point. We will prove that $S(t)=t^3G(t)$ and that the restriction of $y$ to $I$ does not throw away a better partition. The following bounds will also preclude spurious stationary candidates:
\[
 G(0)=g_0=2/\sqrt3-1,\quad -.151\le G'\le-.147,\quad 0\le G''\le.04\quad\text{a.e.};\qquad G\in C^{1,1}. \tag{1}
\]
Here $C^{1,1}$ means continuously differentiable with Lipschitz derivative.

Start iterating at $f_0(t)=g_0-.149t$. At $t=0$ the maximum of $y(1-y)/(1+y+y^2)$ on $[0,1]$ is $g_0$, achieved at $y_0=(\sqrt3-1)/2\in I$, so $f(0)=g_0$ is preserved by $T$. In fact a fixed value $g_0$ at $0$ requires maximizing $g_0y^3+y(1-y)^2$, equivalent to that ratio for $y<1$.

Suppose $f\in C^2$ has this intercept and the derivative bounds (1) everywhere. Evaluate $H=H_f$ at $t,y$ and write $f,f',f''$ below at $ty$. Its relevant derivatives are
\[
\begin{aligned}
 H_y &=3y^2 f+ty^3 f'+(1-t)(1-y)(1-3y),\
 H_{yy}&=6yf+6ty^2 f'+t^2y^3 f''+(1-t)(6y-4),\\
 H_t&=y^4 f'-y(1-y)^2,\
 H_{ty}&=4y^3 f'+ty^4 f''-(1-y)(1-3y),\qquad H_{tt}=y^5 f''.
\end{aligned}
\]
The following scalar checks are detailed in §5 and are independent of any unknown profile.
1. $H_y>0$ for $0\le y\le.35$ and $H_y<0$ for $.405\le y\le.7$.
2. On $I$, $H_{yy}<-1/3$, $-.151\le H_t\le-.147$ and $y^5 f''+3H_{ty}^2<.04$.
3. For $.7\le y\le1$,
\[
 (1+y+y^2)(g_0-.151t)-.151y^3t-(1-t)y(1-y)>0. \tag{2}
\]
Consequently on $I$ there is a unique interior maximizer $Y_f(t)$, continuously differentiable by the implicit function theorem (one-sided at the endpoints). The elementary envelope differentiation gives $(Tf)'=H_t$ and $(Tf)''=H_{tt}-H_{ty}^2/H_{yy}$ there. Thus $Tf$ again meets the same derivative bounds and is $C^2$. The iterates tend uniformly to $G$. By boundedness and equicontinuity of their derivatives a subsequence of derivatives converges uniformly; integration identifies its limit with $G'$. The inequalities $0\le f'(v)-f'(u)\le.04(v-u)$ pass to this limit. This proves (1).

Uniform convergence of the iterates, including of first derivatives along the above subsequence, passes $H_y$ bounds and the strong concavity bound on $I$ to $H_G$ (for strong concavity use the integrated derivative inequality). The strict margin of the sign checks is uniform on the compact sets. Thus on $I$ the maximizer $Y(t)$ is unique and interior and varies continuously. For $y\le.35$ or $.405\le y\le.7$, the derivative signs rule out any nonempty maximizer outside $I$. For $.7\le y<1$, the Lipschitz bound $G(ty)\le G(t)+.151t(1-y)$ and (2) imply $G(t)>H_G(t,y)$ after dividing by $1-y$. At $y=1$ the formal self-loop always gives equality but represents a **zero-length** block. Hence for $0\le a<b\le1/2$, multiplying by $b^3$ gives
\[
 B(a,b)\le b^3G(b)-a^3G(a),\qquad
 \text{equality exactly when }a=bY(b). \tag{3}
\]
Since the expression is $C^1$, uniqueness of the maximizing $y$ also gives $G'(t)=(H_G)_t(t,Y(t))$ by elementary one-sided difference quotients (or the envelope theorem).

Set $S(t)=t^3G(t)$, now verifying the optimality promised in §1. From (1), $S'(t)\ge t^2(3\cdot.1546-4\cdot.151t)>0$ for $0<t\le1/2$. For any disjoint collection of open blocks inside $[0,t]$, (3) and countable additivity of the integral of $S'$ bound the total reward by $S(t)$. Conversely successively choose $t_{j+1}=t_jY(t_j)$ from $t_0=t$. Then $0<t_{j+1}\le.405t_j$, and telescoping (3) gives reward exactly $S(t)$. For equality in the upper bound every positive block must satisfy (3), and the uncovered complement must have Lebesgue measure zero since $S'>0$ away from zero. Every such tight block with right endpoint at least $\epsilon>0$ has length $\ge(1-.405)\epsilon$, so there can only be finitely many of them. Full measure and this local finiteness force a last block ending exactly at $t$, then one ending at its left endpoint, etc. Hence this tail is unique, including among partitions with countably many intervals or diagonal dust.

## 3. The middle block

If $1/2$ lies inside a decreasing block, denote its endpoints by $l,1-r$, with $0\le l,r\le1/2$. Else use the degenerate pair $l=r=1/2$, splitting at a boundary or dust point. In both cases the full score is at most
\[
 W(l,r)=S(l)+S(r)+(1-l-r)^2lr. \tag{4}
\]
For any admissible $l,r$ the two optimal tails and the central block do attain (4), with the zero-length convention when $l=r=1/2$.

We first localize the sum $s=l+r$ using just a rough witness and an affine barrier. A finite symmetric configuration with $l=r=61/200$ and three successive tail cuts at the ratio $3/8$ on each side, then one residual end block on each side, gives $12W$ at least the score of that configuration, which exceeds $.244$. From (1), $G(t)\le \alpha-\gamma t$ for $\alpha=.1548$, $\gamma=.147$. Writing $P=lr$,
\[
 W(l,r)\le \alpha s^3-\gamma s^4+
 [(1-s)^2-3\alpha s+4\gamma s^2]P-2\gamma P^2. \tag{5}
\]
Here $\max(0,(s-.5)/2)\le P\le s^2/4$ because $l,r\in[0,.5]$. Exact univariate interval checks in §5 show that whenever $s\in[0,.58]\cup[.642,1]$, the right side of (5) multiplied by 12 is less than $.244$. So every maximizer satisfies $.58<s<.642$.

From (1), for almost every $0\le t\le1/2$,
\[
 S''(t) = 6tG(t)+6t^2G'(t)+t^3G''(t)
 \le 6\alpha t-12\gamma t^2+.04t^3
 \le (6\alpha)^2/(48\gamma)+.04/8
 =77947/612500<.128 .
\]
At fixed admissible $s$, the second derivative of $W(l,s-l)$ is bounded above by $2\cdot.128-2(1-s)^2<0$ almost everywhere. Its first derivative is Lipschitz and the admissible $l$-interval is symmetric about $s/2$, so strict concavity forces $l=r=s/2$. Thus all global maxima come from $J(t)=2S(t)+t^2(1-2t)^2$ at $t\in(.29,.321)$. Moreover
\[
 J''(t)\le2(77947/612500)+2-24t+48t^2<-2/5
\]
on this interval in the almost-everywhere sense (check the endpoints of the quadratic upper bound). Existence follows by compactness in (4); strict concavity shows the maximum is attained only at the unique zero $t_*$ of $J'$ in $(.29,.321)$. The packing density is precisely
\[
 \boxed{p(1324)=12[2t_*^3G(t_*)+t_*^2(1-2t_*)^2].} \tag{6}
\]
This proves both the value characterization and uniqueness among layered permutons, by (3) and reflection. In particular the interval containing the midpoint is nondegenerate and is centered. The equation is effective without assuming a symbolic closed form: for $f_j=T^jf_0$, (1) implies $\|G-f_0\|_\infty\le.001$. Replacing $G$ by $f_j$ in the maximization of $12J$ over $[.29,.321]$ changes the answer by at most $.003q^j$, since $24t^3\le3$. Each finite iterate uses only maximization of a continuous semialgebraic function on a compact interval over real algebraic data.

## 4. The ratios vary, but tend to Price's geometric ratio

Continuity gives $Y(t)\to y_0=(\sqrt3-1)/2$. To see why the tails are not exactly geometric, the envelope formula at zero yields $d_0=G'(0)=-y_0(1-y_0)^2/(1-y_0^4)$. At $(0,y_0)$, the first-order expansion of $(H_G)_y$ has $y$ coefficient $6y_0g_0+6y_0-4=2-2\sqrt3$ and $t$ coefficient $4y_0^3d_0-(1-y_0)(1-3y_0)$. This expansion follows from $G$ being $C^1$; no second derivative at zero is needed because $t$ multiplies the term containing $G'$. Consequently
\[
 Y(t)=y_0+\frac{107\sqrt3-183}{104}\,t+o(t),\qquad t\downarrow0,
\]
using $(H_G)_y(t,Y(t))=0$ (its nonzero linear $y$ coefficient first gives $Y(t)-y_0=O(t)$). The displayed coefficient is strictly positive. Thus the endpoint ratios along the optimal tail cannot be eventually constant: their only possible limiting value is $y_0$ and each sufficiently small positive $t$ has $Y(t)>y_0$.

## 5. Exact elementary certificates

[check.py](check.py) checks the signs and uniform bounds used in §2, not guesses about the optimizer. It bisects closed rectangles in $(t,y)$ (longer side first). It encloses $f(ty)$ by $[.1546,.1548]+ty[-.151,-.147]$ and uses $f'\in[-.151,-.147]$, $f''\in[0,.04]$ in the displayed polynomial derivatives. The lower endpoint for (2) is computed by the same enclosure. All interval operations round outwards to a multiple of $10^{-12}$ using integers. The program rejects an unresolved narrow rectangle rather than declaring success. For (5), on each closed $s$-interval $[u,v]$ it separately bounds the constant term and the linear coefficient above by $\alpha v^3-\gamma u^4$ and $(1-u)^2-3\alpha u+4\gamma v^2$, then maximizes the resulting concave quadratic in $P$ on $[\max(0,(u-.5)/2),v^2/4]$ by clamping its vertex. All quantities there are exact fractions. The output [CHECKS.txt](CHECKS.txt) lists the visit counts. This is a finite cover of **real intervals**, not discrete sampling.

[digits.py](digits.py) gives an optional numerical replay. An ordinary decimal Newton iteration proposes a trial scalar $t$ and a chain of trial ratios in $I$; it is **not** trusted. Outward-rounded integer arithmetic at $10^{-200}$ certifies the trial as follows. At the deepest length $u$, start with $G(u)\in g_0+d_0u+[0,.02]u^2$ and $G'(u)\in d_0+[0,.04]u$, by (1). Given child enclosures at $ty$, compute $H,(H_G)_y,(H_G)_t$ at trial $y$. Strong concavity gives $H\le G(t)\le H+\tfrac32(H_G)_y^2$ and $|Y(t)-y|\le3|(H_G)_y|$. Since $|(H_G)_{ty}|\le1$ on $I$ (also apparent from the derivative bounds in §2), $G'(t)$ is within $3|(H_G)_y|$ of $(H_G)_t$. These Lipschitz conclusions pass from the smooth iterates to the limit. Finally (6) and $J''\le-2/5$ imply $J(t)\le J(t_*)\le J(t)+5J'(t)^2/4$. The certified density starts $0.244054523929423329586873312859369205\ldots$. This confirms the digits displayed by Sliačan and Stromquist; the high-precision numerical direction was theirs.
