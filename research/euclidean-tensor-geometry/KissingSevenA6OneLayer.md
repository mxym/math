# Seventy-seven approximate E7 sites suffice: a one-sided A6 layer theorem

**Theorem.** Let a seven-dimensional kissing code contain the 42 roots of an $A_6$ equator. If one side has 35 outsiders at the smallest allowed height, then the code has at most **126** points. At 126 points it is an orthogonal copy of **$E_7$**. There is no initial assumption on the other side and no fixed list of labels for the 35 points. The same upper bound holds if the 35 heights exceed the minimum by at most $10^{-12}$, without an equality classification in this perturbed statement.

A second version needs **no exact roots, no exact hyperplane, and no exact layer**: it suffices that 77 distinct points lie within Euclidean distance $10^{-5}$, independently, of the 42 signed $A_6$ roots and 35 sites of one side of the minimum-height layer described below, after an orthogonal placement. All vectors and distances in this paper are at radius $\sqrt2$, with off-diagonal inner products at most one. The numerical tolerance is conservative.

This is a conditional theorem. It does **not** settle the full $A_6$-only case, let alone the unrestricted kissing number. The [109-root retention theorem](KissingSevenRetentionAndIntegralCore.md) permits arbitrary omissions but needs more exact $E_7$ roots; it does not cover this 77-site hypothesis. The previous [equator criterion](KissingADEProjectivizationClassification.md) shows that even an unpunctured $A_6$ alone fails direct one-sided projectivization. Here a single side's layer restores projectivization on the *opposite* side, including for arbitrary continuous outsiders. Compare the distinct complete $E_6$ and $D_6$ cross sections in [Novgorodtsev](https://www.preprints.org/manuscript/202610.0335) and [the exact-equator analysis](KissingEquatorialProjectivization.md); constructions of the classical $E_7$ are not new.

## The layer is forced by its cardinality

Write points as $(v,h)$ with $v$ in the sum-zero hyperplane of $\mathbb R^7$, and $A_6=\{e_i-e_j:i\ne j\}$. The horizontal polar consists of vectors with coordinate spread at most one. Its vertices are among $q_S=1_S-(|S|/7)1$, the projected cube vertices. Their squared norms are $k(7-k)/7$, for $k=|S|$, with maximum $12/7$ only at $k=3,4$. By strict convexity the only minimum-height sites are consequently $(q_S,\pm c)$ for $|S|=3,4$, where $c=\sqrt{2/7}$.

On one side, represent the 70 candidate projections as $+q_T$ and $-q_T$ with $|T|=3$. Two opposite-sign sites indexed by disjoint triples have product $11/7>1$. Their forbidden bipartite graph, after complementing the negative triples, is the incidence graph between triples and four-subsets of a seven-set. It is 4-regular and connected: one triple can be changed into another by one-element exchanges using an intermediate four-set. For a family $F$ on the left, degree counting gives $|N(F)|\ge |F|$, strictly for a nonempty proper $F$ since equality disconnects its neighborhood. An independent set of 35 must therefore be the whole of one side of this bipartition. Equality is attainable within either label orientation. Up to global horizontal sign, the 35 upper sites are **all** $(q_S,c)$ with $|S|=4$.

In the standard $E_7$ model, using $A_7$ roots and the balanced half-sign vectors on eight coordinates, this is one minimum-height layer above the $A_6$ on the first seven coordinates. The other upper orbit consists of the seven singleton projections $q_i$ at height $2c$; the lower half consists of the negatives of the upper 42. This provides the sharp example.

## How one layer controls both sides

Sort $v$ in decreasing coordinate order. The sorted polar is a simplex with vertices $Q_k=q_{\{1,\ldots,k\}}$, $0\le k\le6$ (with $Q_0=0$): its successive coordinate differences are nonnegative and sum to at most one. Write $C(v)=v_1+\cdots+v_4$. Compatibility with the 35 specified upper sites implies
$$
 C(v)+c h\le1\quad\text{on the upper side},\qquad
 C(v)-c h\le1\quad\text{on the lower side},
$$
where $h$ henceforth denotes absolute height. In the first inequality exclude the 35 designated sites themselves.

**Upper side.** Throughout the simplex $C(v)\ge\|v\|-1/2$: it suffices to check the vertices by convexity, as in the [rational replay](verify-kissing-a6-one-layer.py). If $r=\|v\|\ge 99/100$, then
$$
 C(v)+c h\ge r-1/2+c\sqrt{2-r^2}>1.02.
$$
Indeed the right side is concave in $r$, so its minimum on $[.99,\sqrt{12/7}]$ is at an endpoint. At .99 use $c>.53$ and $\sqrt{2-.99^2}>1$; at the other endpoint use $\sqrt{12/7}>1.3$ and $c^2=2/7$. Thus each additional upper point has $r<.99$ and $h>1$. Distinct horizontal projections have strictly negative pairwise product, since the full product is at most one. At most seven nonzero vectors can be pairwise strictly obtuse in dimension six: otherwise an affine dependence with coefficient sum zero gives equal positive and negative convex combinations and their cross product is negative despite being a squared norm. A zero projection can occur only alone. The upper side has at most $35+7=42$ points.

**Lower side.** Here there is no assumed layer. With $s=h/c$, consider the relaxed region in the ordered simplex:
$$
   s\ge\sum_k\lambda_k g_k,\qquad
   s\ge (7C(v)-7)/2,\qquad
   g=(1,1,5/4,1,1,5/4,1),\qquad v=\sum_k\lambda_k Q_k.
$$
The first inequality follows by concavity of the true height since $g_k\le\sqrt{(14-k(7-k))/2}$. The second is the lower-side constraint. Reversing the coordinates of the second sorted argument minimizes the horizontal product among all relative permutations. The following bilinear inequality holds throughout this relaxed epigraph:
$$
             v\cdot\operatorname{rev}(w)+\tfrac27 s t\ge-1 .
$$
Its lower boundary is the graph of the maximum of the two affine functions displayed above. Its vertices are their maxima over the seven simplex vertices, plus their crossing on simplex edges whose endpoints have strictly opposite differences. Indeed projecting each affine piece gives a simplex intersected by one halfspace. There are exactly 12 lower generators; the only recession direction is vertically upwards. It suffices to test their 144 ordered pairs, since both vertical coordinates are positive. The [standalone checker](verify-kissing-a6-one-layer.py) works entirely in rationals: the minimum is $-1$ and the next distinct value is $-55/56$.

Thus all lower outsiders and the 21 equator axes form a projective kissing code. By [Anstreicher](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf) it has at most 63 lines, so the lower side too has at most 42 points. This proves the 126 bound.

## Exact equality

At 126, the 21 equator axes and 42 lower lines attain projective equality; their double must be $E_7$. Its root reflections in $A_6$ permute the seven coordinates and fix the normal. The projections of its lower roots have pairwise coordinate differences in $\{0,\pm1\}$ by integrality against the equator and the kissing inequalities for both signs. Thus any lower orbit has projections all $q_S$ for one fixed size $k$, with uniquely determined height. Its possible sizes are $1,7,21,35,35,21,7$ for $k=0,\ldots,6$. Totalling 42 is possible only as $35+7$ or $21+21$. The latter would include $q_2$ and $q_5$ with nested supports and lifted product $8/7>1$ (subscripts here denote support sizes). Likewise $q_3,q_1$ and their complements are incompatible by taking nested supports or their negatives. The two possible lower collections are therefore $(q_4,q_1)$ or their horizontal negatives $(q_3,q_6)$. Repeating the upper $q_4$ orientation across the two sides would put corresponding points at dot $10/7>1$, so the lower collection is forced to be $(q_3,q_6)$. In particular the lower minimum layer is also full. Reversing the roles of the hemispheres makes the upper collection a projective equality case as well, hence $(q_4,q_1)$. This is precisely the displayed $E_7$ configuration.

## Independent perturbations of the 77 sites

Let $e=10^{-5}$. For clarity work with labels approximating the 42 roots and the 35 upper four-subset directions, but do not equate any labelled point with its reference. Remove those 77 points from the code temporarily, and take an arbitrary remaining $(v,\pm h)$. Its horizontal spread is at most $k=1+2e$, by testing against the near-roots. Put $v_0=v/k$ and $h_0=\sqrt{2-\|v_0\|^2}$. Then $v_0$ is in the exact polar, and $h>1/2$ since $\|v\|^2\le k^2(12/7)$. The synthetic point $(v_0,\pm h_0)$ differs from the real point by at most $9e$: the horizontal change is at most $3e$, and $|h-h_0|\le (k^2-1)(12/7)/(h+h_0)<7e$.

Against each exact upper four-subset reference, the synthetic point has dot at most $1+\eta$, $\eta=20e$: the actual comparison has dot at most one, and the two vector errors cost at most $\sqrt2(e+9e)$. This gives the same two cuts as before with right side $1+\eta$. In the upper cut the strict $1.02$ bound persists, so $\|v_0\|<.99$ and $h\ge h_0-7e>1$. There are again at most seven additional upper points.

In the lower cut, raise $h_0$ by $\eta/c<2\eta$. This restores the original cut and preserves the other lower-envelope inequality, so the 144-pair certificate applies to these artificially raised points. Undoing both height raises costs at most $6\eta+4\eta^2$ in a pair product, and undoing the synthetic perturbations costs less than $26e$. Thus each lower pair's *actual* product is at least $-1-146e-1600e^2$, and of course at most one. In unit normalization the lower lines and all 21 exact comparison axes have absolute inter-line scalar products at most $a=1/2+73e+800e^2$, since the axes' cross terms are at most $(1+2e)/2$ in that normalization. No lower point is equatorial and the lines are distinct.

For lines in dimension seven at separation $|t|\le a$, the even polynomial $t^2(t^2-a^2)$ has constant Gegenbauer coefficient $(1-3a^2)/21$ with nonnegative remaining coefficients here (the degree-two coefficient has the sign of $6/11-a^2$). The elementary projective LP bound is $21(1-a^2)/(1-3a^2)<64$ because $a^2<43/171$. Hence the lower side still has at most $63-21=42$ actual residuals. The 77 removed labels, seven upper residuals and 42 lower residuals give at most 126 irrespective of where each near-root lay.

Finally, for an **exact $A_6$** suppose merely that there are at least 35 upper points with $h\le c+t$, $t=10^{-12}$. Their horizontal squared norms are within $D=2ct+t^2$ of $12/7$. Express $v$ as a convex combination of original polar vertices. The identity $\sum\lambda_S\|q_S-v\|^2=\sum\lambda_S\|q_S\|^2-\|v\|^2\le D$ yields a vertex within $\sqrt D$. It must be a three- or four-subset, since the next squared norm is only $10/7$. Including the height error gives distance at most $\sqrt{D+t^2}<e$ to the corresponding minimum site. No two points receive the same label (their separation is at least $\sqrt2$), and labels on opposite orientations with disjoint triples remain impossible since $11/7-2\sqrt2 e>1$. The same connected-graph argument forces all 35 labels of one orientation. The perturbation theorem now applies. The [exact replay](verify-kissing-a6-one-layer.py) also verifies the numerical slack inequalities.
