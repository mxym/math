# Exactly when a punctured D-type equator admits one-sided projectivization

Let $D_n=\{\pm e_i\pm e_j:i<j\}\subset\mathbb R^n$, including the same coordinate model in ranks 2 and 3. Remove an arbitrary set $M$ of **signed** roots. Does testing a vector against the retained roots ensure that, within either hemisphere in $\mathbb R^{n+1}$, no two admissible vectors make an angle greater than $120^\circ$? The answer is controlled by only three local patterns, regardless of how many roots are removed. This classifies the **projectivization criterion**, not the kissing number itself. There is an elementary proof; the [independent finite replay](verify-kissing-dn-projectivization-obstructions.py) is optional.

## The three obstructions

Write $P(M)=\{v:v\cdot r\le1\text{ for all }r\in D_n\setminus M\}$. A feasible lift is $(v,h)$ with $v\in P(M)$ and $\|v\|^2+h^2=2$. Call $M$ **good** if any two feasible lifts in the same closed hemisphere have dot product at least $-1$. Thus the points on one side of any actual kissing code with these retained roots are mutually projectively compatible. The property does not claim a kissing upper bound for arbitrary feasible vectors before a code is chosen.

**Classification.** For $2\le n\le6$, $M$ is good exactly when it contains none of the following subsets, up to permuting coordinates and changing their signs independently:

1. An opposite pair $\{r,-r\}$.
2. The triangle $\{e_1+e_2,e_2+e_3,e_3+e_1\}$, when $n\ge3$.
3. A star $\{e_1+e_j:2\le j\le k+1\}$ with $k=\min(4,n-1)$ **distinct** leaves.

For $n\ge7$, even $M=\varnothing$ fails. The low-rank redundancies are simple: in rank 2 any omission fails; in rank 3 a listed triangle already contains a forbidden star. In ranks 4, 5 and 6 the list is irredundant. In particular the *only* inclusion-minimal defects in either $D_5$ or $D_6$ are an opposite pair, a coherently signed triangle, and a coherently centered four-star. Their numbers before quotienting by symmetry are respectively $(20,80,160)$ and $(30,160,960)$. Failure can always be witnessed **strictly inside one open hemisphere**, by a pair still satisfying the ordinary kissing constraint.

Earlier [two-puncture bounds](KissingPartialD5D6Equators.md) allow for an isolated conflict in the opposite-root case; [an elementary tube argument](KissingSevenD6TwoHoles.md) treats some orthogonal multi-punctures. Neither describes all omission patterns. The classification here is an exact test on the omitted signed graph, not an inference that failure of the test creates a large code.

## Proof of necessity

An opposite pair admits the horizontal vectors $r,-r$ themselves, with dot product $-2$. For a triangle take the equatorial point $v=\sqrt{2/3}(1,1,1,0,\ldots)$ and the lift of $w=(-1/2,-1/2,-1/2,0,\ldots)$. Only the three omitted inequalities can fail, while $v\cdot w=-\sqrt{3/2}<-1$.

For a four-star in ranks 5 and 6, take the equatorial $v=(1,1/2,1/2,1/2,1/2,0,\ldots)$ and the lift of $w=(-1/2,-1/2,-1/2,-1/2,-1/2,0,\ldots)$. The dot is $-3/2$. For the full star of a smaller rank $n=2,3,4$, put $u=(3/2,1/2,\ldots,1/2)$. The only constraints $u$ violates are its star; radially scale to $v=\sqrt2u/\|u\|$. Since $\|u\|^2=(n+8)/4>2$ and $v_1^2=18/(n+8)>1$, the lift of $w=-e_1$ has product less than $-1$ with $(v,0)$. Each example survives further omissions, and slightly shrinking each equatorial projection and giving it the corresponding positive height preserves strict failure. Finally for $n\ge7$ put $v=(1/2,\ldots,1/2,0,\ldots)$ on seven coordinates. The intact equator allows both $v$ and $-v$; at the same height $1/2$ their dot is $-3/2$.

## Proof of sufficiency

Suppose no listed pattern occurs and $n\le6$. Every $v\in P(M)$ has $|v_i|\le1$: otherwise for each $j\ne i$, the root with signs aligned to $v_i,v_j$ (choose either if $v_j=0$) is violated, giving the forbidden star. At any vertex of the now bounded polytope, take $n$ linearly independent tight equations $\pm v_i\pm v_j=1$. In a connected component of their coordinate graph, all coordinates equal $\pm t+$ an integer along a spanning tree. Some further equation must determine $t$ or this component gives a nonzero null vector. It says $2t$ is an integer. Hence every vertex is half-integral. This signed-graph observation is not new; the rest of the proof uses the special geometry of the forbidden patterns.

All vertices belong to the following three types (a superset of the true vertex list is harmless):
* **Small:** all coordinates have modulus $0$ or $1/2$; squared norm at most $n/4\le3/2$.
* **Root:** two coordinates have modulus one and the others vanish. Indeed if two unit entries occur, any third nonzero entry would produce a forbidden coherent triangle. Such a root $r$ is itself omitted, so $-r$ is retained.
* **Brush:** one unit coordinate, called the center, and at most three half-unit entries on distinct leaves, the rest zero. Each center-to-leaf signed root with the same signs as these two coordinates is omitted. Four such leaves would be forbidden. Its squared norm is at most $7/4$.

In particular all vertices are in the ball of radius $\sqrt2$, with equality only for roots. Put $H(v)=\sqrt{2-\|v\|^2}$. On this ball $H$ is nonnegative and concave. For two convex combinations of vertices, the lifted product $v\cdot w+H(v)H(w)$ is at least the product-weighted average of the lifted vertex products. It is enough to check the following cases.

* A root $r$ is compatible with everything, since $-r$ was retained and it has height zero. Two small vertices each have height at least $1/\sqrt2$ and horizontal length at most $\sqrt{3/2}$, so their lifted dot is at least $-1$.
* A small vertex against a brush loses at most $1/2+3/4=5/4$ in the horizontal dot. Both heights are at least $1/2$, restoring at least $1/4$.
* Two brushes with the same center and same sign have horizontal dot at least $1-3/4$. If instead their center signs are opposite, each shared leaf has matching signs: a contrary sign would require two opposite omitted roots on that edge. The only negative contribution is then $-1$ from the center.
* For brushes with distinct centers, the two center-to-leaf cross terms are each $0$ or $\pm1/2$. They cannot both be negative, since that again requires an opposite pair of omitted roots on the edge between the centers. Thus their sum is at least $-1/2$. The other shared leaves lose at most $3/4$; the product of the heights restores at least $1/4$.

This proves the classification. In the three irredundant ranks, all proper subsets of each listed prototype avoid the other prototypes, so the minimality assertion follows as well.

## Consequence for six- and seven-dimensional kissing codes

Let $n=5,6$, $p=n(n-1)$ be the number of equator axes, and $K=36,63$ respectively be [Anstreicher's maximum projective kissing sizes and equality classification](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf). Suppose a code contains exactly $2p-m$ roots of this particular equator and its missing set is good. There are no equatorial outsiders: a convex combination of the vertices above can have squared norm two only at a root, by strict convexity. All outsiders on either open side, together with the $p-m$ paired axes, are projectively compatible. Thus the total size is at most $2K+m$.

If $1\le m\le2(n-2)$, the upper bound improves to **$2K+m-2$**. If some hemisphere saturated $K$ projective lines, Anstreicher's equality case would make its double an $E_6$ or $E_7$ root system; it contains every root generated by reflections in the paired axes. Each omitted root $r$ has $2(n-2)$ decompositions $r=a+b$ with $a,b$ roots of inner product $-1$: choose a spare coordinate and its sign, using it once positively and once negatively. The $2\cdot2(n-2)$ summand axes across those decompositions are all different, and none is the axis of $r$. At most $m-1$ more axes are unpaired. Some decomposition therefore survives in full, and reflection restores $r$. No unpaired equator line was among the selected lines, a contradiction. So both sides fall short by at least one. The same improvement holds for larger $m$ whenever the paired roots' reflection closure contains at least one missing axis.

For example a 74-point six-dimensional candidate containing 37 of the 40 signed $D_5$ roots, or a 128-point seven-dimensional candidate containing 57 of the 60 signed $D_6$ roots, **must** omit an opposite pair or a coherently signed triangle. This criterion does not assert that either exceptional pattern admits such a code or decide the unrestricted kissing numbers.
