# A two-clique replacement at every nonreciprocal density

**Theorem.** Fix $0<\beta<1/2$ with $1/\beta\notin\mathbb N$. The limiting density of the clique sequence proposed in [Balogh et al., Question 1](https://arxiv.org/abs/2601.03433v1) is strictly below $I(AC_4,\beta)$.

A labelled copy is an ordered injection $(u,v,w,x)$ for which $uv,wx$ are red and $vw,xu$ are blue; the two diagonals are unrestricted. For a sequence of complete two-coloured graphs on $n$ vertices we divide the number of copies by $n^4$ and require the fraction of red pairs to tend to $\beta$. We compute finite-block limits by taking four independent labels; repetitions in an $n$-vertex graph have probability $O(1/n)$.

## The two selected cliques

Set $k=\lceil1/\beta\rceil$. The prescription has $k-1$ asymptotically equal large red cliques and one red clique of limiting mass $b\le 1/k$, with all cross edges blue. In fact the masses necessarily converge: every subsequential limit of the small-clique fraction satisfies
$$
g(b)=\frac{(1-b)^2}{k-1}+b^2=\beta.
$$
On $[0,1/k]$, $g$ is strictly decreasing from $1/(k-1)$ to $1/k$: its derivative is $2(kb-1)/(k-1)$ and is negative throughout the interior. The unique root is therefore in $(0,1/k)$, and the large masses converge to $a=(1-b)/(k-1)>b$.

Choose one large clique and the small clique; let $S$ be their union, of mass $s=a+b$. Its relative blue density is $t=2ab/s^2\in(0,1/2)$. Inside $S$ the two prescribed red edges must lie in different cliques, which is also sufficient. The old alternating density conditional on all four labels being in $S$ is $2a^2b^2/s^4=t^2/2$.

## Recolouring with the same internal density

Take $h=\lceil1/t\rceil\ge3$. Choose positive masses $u_1,\ldots,u_h$ summing to one, with the first $h-1$ tied for largest and $\sum_i u_i^2=t$. To see that this is possible, take $u_1=\dots=u_{h-1}=x$ and $u_h=1-(h-1)x$. The sum of squares ranges continuously from $1/h$ up to, but not including, $1/(h-1)$ as $x$ runs from $1/h$ up to $1/(h-1)$. At the included endpoint all masses are equal. There are at least two maximal masses and a third positive one, so
$$
\max_i u_i^2<t/2,\qquad
\sum_i u_i^4\le (\max_i u_i^2)\sum_i u_i^2<t^2/2.
$$

Within $S$, put **blue** cliques on these relative masses and make every other internal edge red. The blue density inside $S$ is still $t$, so the global red density is unchanged. Now the two prescribed *blue* edges must lie in different cliques, which suffices for both red edges. The new internal alternating density is
$$
\sum_{i\ne j}u_i^2u_j^2=t^2-\sum_i u_i^4>t^2/2.
$$

All edges across the boundary of $S$ are blue. Any mixed copy must consequently have one entire prescribed red edge inside $S$ and the other outside. Its contribution depends only on the red edge masses of the two regions, not on their internal arrangements: in either ordering every such pair of edges automatically has both required blue pairs. Thus all mixed contributions and all-outside copies are unchanged. The global gain equals
$$
s^4\Big(t^2/2-\sum_i u_i^4\Big)>0.
$$
Each fixed $\beta$ uses finitely many parts; rounding their sizes to integers summing to $n$ realizes the two constructions along all orders. This proves the theorem. The same local criterion applies to any pair of unequal positive red cliques with all edges from their union to the outside blue.

The new construction is not asserted to be extremal, regular, or uniformly better by a gap bounded away from zero near the reciprocal densities. At $\beta=1/k$, the known equal-clique optimum is unchanged. The component-count and colour-symmetry principles are also prior; see [sources](SOURCES.md).
