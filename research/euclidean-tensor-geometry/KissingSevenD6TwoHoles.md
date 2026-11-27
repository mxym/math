# A shallow-point tube for punctured D6 sections

**Scope and prior result.** The [earlier two-puncture theorem](KissingPartialD5D6Equators.md) already proves the arbitrary 58-of-60 bound and the sharp one-hole bound below, in addition to its five-dimensional equator cases. This note gives a different shallow-point tube proof and extends its counting estimate to **more than two signs on orthogonal root lines**. The two-hole statements themselves are not new results.

**Theorem.** Fix a normalized $D_6$ root system $R$ of 60 points in a hyperplane of $\mathbb R^7$. A 60-degree spherical code $C$ containing **any 58 of its 60 signed roots** has at most 126 points. No symmetry of the other points, antipodality of $C$, or equality between upper and lower layers is assumed. If exactly one directed root of $R$ is absent, the sharper upper bound is **125**, attained by deleting that root from $E_7$. The at-least-58 bound is sharp since $E_7$ contains the complete section. We do not classify equality for two omissions.

More generally, suppose all missing signed roots are on mutually orthogonal root lines and let $r\ge1$ be the number of missing **signs**, not lines. Then $|C|\le124+r$. This is useful, for example, with up to seven omissions, and the first theorem removes the orthogonality restriction for $r\le2$. These are conditional statements, not an improvement of the [unrestricted upper bound 132](https://www.mefyi.com/papers/kissing-numbers-five-seven/kissing-numbers-five-seven.pdf).

For context, the [complete $D_6$ equator proof](KissingEquatorialProjectivization.md) uses one-sided extension to projective codes; [Novgorodtsev](https://www.preprints.org/manuscript/202610.0335) treats the different complete $E_6$ section in dimension seven. Removing signs lets points approach the equatorial hyperplane, so the complete-section argument alone does not apply.

## 1. The shallow-point estimate

Work at unit norm. Write an outsider as $x=(v,t)$, where $v$ is horizontal, $\|v\|^2+t^2=1$, and call it shallow if $|t|<1/2$. The roots are $(\pm e_i\pm e_j)/\sqrt2$, $1\le i<j\le6$.

First consider omissions on orthogonal lines. Two orthogonal root lines of $D_6$ have disjoint two-coordinate supports or the same support. Complete these supports to three disjoint pairs of coordinates. Rotating each pair by $45^\circ$ turns the twelve possible within-pair signed roots into the standard signed axes $p=\pm e_i$ in the new basis. The other 48 roots remain present: their supports are any two of the three coordinate pairs, with all sixteen sign choices and coordinate magnitudes $1/2$.

Let $L_j$ be the sum of the two absolute values of $v$ in coordinate pair $j$. The 48 root constraints give $L_i+L_j\le1$ for $i\ne j$. If all $L_j\le1/2$, then $\|v\|^2\le3/4$. Otherwise let $L$ be the largest. We have $\|v\|^2\le L^2+2(1-L)^2$, so a shallow point needs $L>5/6$ (the quadratic is at most $3/4$ on $[1/2,5/6]$). Let $a$ be the larger absolute coordinate in that pair. Then
\[
 \|v\|^2\le a^2+(L-a)^2+2(1-L)^2.
\]
If $a\le5/6$, the last expression is no larger with $a$ than with $a=5/6$ (as $a\ge L/2$); its maximum for $L\in[5/6,1]$ is attained at an endpoint and is at most $3/4$. Hence $a>5/6$. For fixed $a$ maximize in $a\le L\le1$, again at an endpoint. Both $a^2+2(1-a)^2$ and $a^2+(1-a)^2$ are at most $(3a-1)/2$ for $a\in[5/6,1]$. Thus with $p$ the signed axis of this coordinate,
\[
 \|v-p\|^2=1+\|v\|^2-2a\ \le\ t^2/3. \tag{1}
\]
The signed root $p$ must be missing, since $p\cdot v>5/6$. A point outside the 48 roots can violate $p\cdot v\le1/2$ for at most one signed axis: different pairs satisfy the pair-sum constraint, while each individual $L_j\le1$. At $t=0$ inequality (1) forces an axis itself; thus all equatorial points belong to $R$. This argument also covers an outsider violating **only one** missing root's inequality, regardless of what other roots are absent: that individual horizontal point satisfies every root inequality except possibly the one and we may choose pairs adapted to it.

## 2. Projectivizing each side when the omissions are orthogonal

Within either open hemisphere use the absolute height $h=|t|$. Two deep points ($h\ge1/2$) have inner product at least $hh'-\sqrt{1-h^2}\sqrt{1-h'^2}\ge-1/2$. An outsider is at a signed site $p$ if $p\cdot v>1/2$. A shallow $x$ at $p$ and a deep $y$ satisfy
\[
 x\cdot y\ge p\cdot v_y+h_x(h_y-\|v_y\|/\sqrt3)\ge p\cdot v_y.
\]
So if $y$ is not at $-p$, their scalar product is at least $-1/2$. In particular, no deep point in that hemisphere can share a site with a shallow point (their scalar product would be greater than $1/2$). No two shallow points there share a site either: by (1) their squared distance is at most $(h+h')^2/3+(h-h')^2\le1/3$ for $h,h'\in[0,1/2]$.

For two shallow points at nonopposite sites $p,q$, use (1) for both. Since $p\cdot q\ge0$, their scalar product is at least
\[
 -(h+h')/\sqrt3+(2/3)hh'>-1/2 .
\]
Indeed the expression decreases in each height on this square and is greater than $-1/2$ at $(1/2,1/2)$.

It follows that the only possible failures of projective compatibility within a hemisphere (a scalar product below $-1/2$) are between opposite sites of a single line, with at least one of its two sites occupied by a single shallow point. Such a failure requires **both signs** of the line to be missing: the retained sign otherwise excludes any outsider at its site. For each doubly missing line one deletion suffices, since a site occupied by a shallow point contains nothing else. Sites are disjoint. After at most $b$ deletions, where $b$ is the number of doubly missing lines, the outsiders in that hemisphere therefore represent a projective code with absolute scalar products at most $1/2$; add all completely retained equatorial root lines.

Here is the strict part of the projective bound. [Anstreicher, Theorem 7](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf) gives at most 63 lines in $\mathbb R^7$, with equality only for the normalized $E_7$ root lines. Our equatorial core generates **every $D_6$ root under reflections**; indeed the 48 cross-pair roots already do so, since the two missing coordinates in a block can be linked through a third coordinate in another block. An $E_7$ line system is closed under reflections in its roots. A 63-line completion already containing our core would therefore have to contain *all* 30 equatorial root lines. But the selected lines consist of the completely retained lines and nonzero-height points; at least one equatorial line is absent. Hence we have at most **62** selected lines whenever any root sign is missing.

Write $s$ for the number of affected lines, so $r=s+b$. There are $60-r$ equatorial points and $30-s$ fully retained lines. Each open hemisphere has at most $62-(30-s)+b=32+s+b$ outsiders. This gives precisely $124+r$. With no omission we instead use all 30 lines and ordinary one-sided projectivization to get $60+2(63-30)=126$.

## 3. Two nonorthogonal omissions

Let the missing directions be $p,q$, with $p\cdot q=\pm1/2$. Their opposites are both present, so every outsider satisfies $p\cdot v,q\cdot v\ge-1/2$. If $p\cdot q=-1/2$, simultaneous violations of the two upper bounds $p\cdot v,q\cdot v\le1/2$ are impossible: $\|p+q\|=1$. Every shallow point then satisfies (1) with its own missing root (without a violation it satisfies the full root inequalities). In the obtuse case, two shallow points attached to different roots obey
\[
 v_x\cdot v_y=(v_x-p)\cdot(v_y-q)+v_x\cdot q+p\cdot v_y-p\cdot q
 \ \ge\ -h_xh_y/3-1/2.
\]
After adding $h_xh_y$, this is projectively permissible. Same-site and deep comparisons are as above.

When $p\cdot q=+1/2$, every shallow point instead satisfies
\[
 \operatorname{dist}(v,[p,q])\le |t|/\sqrt3. \tag{2}
\]
The one-violation cases already follow from (1). For a simultaneous violation, take $P=\sqrt2p=e_1+e_2$, $Q=\sqrt2q=e_1+e_3$ and $w=\sqrt2v$. Interchange $2,3$ so $w_2\ge w_3$, and sign-sort the last three entries. The remaining root constraints and the two violated constraints put $w$ in the simplex described by
\[
 0\le w_6\le w_5\le w_4\le1-w_1\le w_3\le w_2,\qquad w_2+w_3\le1 .
\]
For instance $w_4\le1-w_1$ follows from the retained $e_1+e_4$ inequality, and the joint violation gives $1-w_1\le w_3$. Cut this simplex by $(P+Q)\cdot w=13/5$. On the lower part $\max\|w\|^2=3/2$; on the upper part $\max(\|w\|^2+3\operatorname{dist}(w,[P,Q])^2)=2$. Both functions are convex, so it suffices to check the vertices. The [short exact verifier](verify-kissing-seven-d6-two-holes.py) enumerates six active linear equations at a time; there are seven vertices before the cut, and fifteen and twelve in the two pieces. These exact maxima establish (2). In either two-hole case $t=0$ would require a unit vector in the missing singleton or segment, necessarily an endpoint, so again all equatorial points belong to $R$.

For the acute case take an approximating point of $[p,q]$ for each shallow point as in (2). Its inner product with any deep horizontal $v_y$ is at least $-1/2$ since $-p,-q$ are both present; the same height calculation proves projective compatibility. Two approximants in this segment have norms at most one and mutual inner product at least $1/2$, so the nonopposite-site estimate from §2 applies as well. Thus in both nonorthogonal cases all outsiders in a single open hemisphere are already projectively compatible, **without deletions**.

The 28 fully retained equatorial lines generate all $D_6$ roots (also checked by the verifier for every relative root type). The same strict projective argument gives at most $62-28=34$ outsiders per side. The total is at most $58+2\cdot34=126$. Together with §2 this covers every pair of missing signs.

Run the finite identities with plain Python:

~~~sh
python3 verify-kissing-seven-d6-two-holes.py
~~~
