# Every density-maximizing permuton of a nontrivial layered pattern is layered

**Theorem.** Let $\sigma$ be any layered permutation of order $m\ge2$. Every permuton attaining the packing density of $\sigma$ is layered. There is no restriction on the lengths, locations, or consecutive runs of singleton layers. Equivalently, every subsequential limit of any sequence of near-optimal permutations is layered. This does not assert that there is only one optimal layered permuton or that its number of layers is finite.

This answers the nontrivial case of Kabela, Král’, Noel and Pierron's Problem 3 (2022, §5) in the negative. If their question is read as including the one-point pattern, every permuton maximizes that constant density, giving a trivial exception. The theorem is about limits: the finite nonlayered maximizer for $43215$ exhibited by Albert, Atkinson, Handley, Holton and Stromquist (2002, Remark 2.3) is unaffected.

A permuton $\mu$ is a probability measure on $[0,1]^2$ with uniform marginals. The density $d(\sigma,\mu)$ is the probability that $m$ iid samples, sorted by their first coordinates, rank in their second coordinates as $\sigma$. In particular, all comparisons of distinct sampled coordinates are strict almost surely. A layered permutation is a direct sum of decreasing permutations; in its increasing product order, points in the same layer are incomparable and all points of each earlier layer precede every point in each later layer. A permuton is layered iff it has zero densities of $231$ and $312$ (Kabela et al., §2). Its layers may include increasing diagonal dust. The usual compactness, continuity of pattern densities, and sampling of permutons identify the maximum permuton density with the limiting finite packing density. We prove the statement for an arbitrary maximizing $\mu$.

## 1. Incomparable roots transfer a labelled completion

Write $x\prec y$ if $x$ is smaller in both coordinates; $x\parallel y$ denotes incomparability. Use the three labels $<,>,\parallel$ for this order, not the left/right orientation of incomparable points.

Let $p=d(\sigma,\mu)$. Define $h(x)$ as the conditional completion probability with one prescribed root and $m-1$ fresh samples; $F(x,y)$ uses two prescribed ordinary roots and $m-2$ fresh samples. Define $c(x)$ in the same way with two formal incomparable copies of $x$ instead of ordinary roots. Copies have the same relation to any ordinary point, but are ordered decreasingly among themselves. We first record the extremality test (the measure variation used in the earlier single-pattern $1324$ argument).

For positive-mass measurable $B$, put $\nu_B=\mu|_B/\mu(B)$. Perturb the geometric sampling law to $\mu-\varepsilon\nu_B$ plus an additional copy-fiber mass $\varepsilon$ at a fixed $x$, for $0\le\varepsilon\le\mu(B)$. Each draw from that fiber carries an independent uniform key; ties among copies are resolved by increasing keys in the first coordinate and decreasing keys in the second. Ordinary marginal ties have probability zero, also with a fixed $x$. Every finite iid sample ranked by these two orders gives a permutation. For sample sizes $N\ge m$ its expected induced $\sigma$-density equals the perturbed $m$-sample probability, hence is bounded by the order-$N$ maximum; letting $N\to\infty$ bounds the polynomial in $\varepsilon$ by $p$. No marginal-preservation assumption on the unranked law is needed.

For $B$ the whole space the first derivative at zero gives $h(x)\le p$ and $\int h\,d\mu=p$, hence $h=p$ almost everywhere. The linear term now vanishes for every such $x$ and every $B$. The nonpositive quadratic term divided by $\binom m2$ gives
\[
c(x)-2\int F(x,y)\,d\nu_B(y)+ F_{BB}\le0,
\qquad F_{AB}=\iint F\,d\nu_A\,d\nu_B.
\]
Averaging first over $x\in B$ yields $c_B\le F_{BB}$, where $c_B=\int c\,d\nu_B$. Averaging the same inequality instead over $x\in A$ gives
\[
c_A+c_B\le2 F_{AB}. \tag{1}
\]

Fix incomparable $x,y$, off coordinate ties. If $(x,y,u_1,\ldots,u_{m-2})$ induces $\sigma$, the roots must occupy the same layer of $\sigma$. Replacing their pair by two incomparable copies at either root still induces $\sigma$: all other layers have the same comparisons to both; points in their common layer remain an antichain whose internal ordering is decreasing. In particular the event for the ordinary pair is contained in both events for copies; on that event the vectors of the three order labels of $x$ and of $y$ relative to the labelled fresh tuple $\mathbf u$ are equal. Therefore $F(x,y)\le\min(c(x),c(y))$. In (1) take $A,B$ to be any pair of rational rectangles such that every cross-pair is incomparable. Integrating the reverse pointwise inequality forces equality. A countable cover of all strict inversions by such rectangle pairs now gives $F(x,y)=c(x)=c(y)$ for almost every incomparable pair. The two larger copy events thus differ from the ordinary completion event only on null sets.

For a fresh tuple $\mathbf u$, let $g_{\mathbf u}(x)$ be a failure symbol if the copies at $x$ do not complete $\sigma$, and otherwise the vector of labels comparing $x$ to each $u_j$. The preceding statement gives, by Fubini, for almost every $\mathbf u$,
\[
g_{\mathbf u}(x)=g_{\mathbf u}(y)\quad\text{for }\mu^2\text{-almost every incomparable pair }(x,y). \tag{2}
\]

## 2. Intervals spanned by inversions

Let $O$ be the union of all open first-coordinate intervals $(v_1,w_1)$ for points of the support with $v_1<w_1$ and $v_2>w_2$. Its connected components are countably many disjoint open intervals $I=(a,b)$. Almost surely, every sampled inversion has both endpoints within one component: its open span lies in a component and the sampled first coordinates avoid all component endpoints. Thus comparisons between distinct components, and comparisons involving a point with first coordinate outside $O$, agree with first-coordinate order almost everywhere. Write $H_I=\{x:x_1\in I\}$. Its mass is $b-a$. It occupies the square $I^2$ up to null sets: the regions to its left, in it, and to its right have almost surely strictly ordered second coordinates across regions. Uniform second marginals force their second-coordinate intervals to be $[0,a], [a,b], [b,1]$, respectively, up to null sets. For example, for a first-coordinate cut at a component endpoint $t$, the two ordered groups have masses $t,1-t$, so the first occupies the lowest $t$ fraction of the uniform second marginal; null groups are harmless. Consequently the conditional law on $H_I$ after rescaling both axes is a permuton $W$, and it can be replaced there by any other rescaled permuton without changing outside comparisons or the two marginals.

If a measurable finite-valued $g$ is equal on almost all incomparable pairs, then $g$ is almost surely constant on each $H_I$. Here is an elementary proof. For each support inversion $v,w$ and compact subinterval $[s,t]\subset(v_1,w_1)$ with $s<t$, take positive-mass neighborhoods $A,B$ of $v,w$ lying to the left and right of $[s,t]$ and separated in reversed second-coordinate order. Cross-pairs are incomparable, so independent draws from $A,B$ have equal $g$ almost surely. That common value is a fixed constant, since the draws are independent. For any third point with first coordinate in $[s,t]$, at least one of the two comparisons with the cross-pair is an inversion (otherwise the two outer points would be ordered). By Fubini, $g$ is equal to the fixed value almost surely throughout that band. Exhaust the open span by such subintervals. Overlapping open spans agree on their constants since their first-coordinate overlap has positive uniform mass. A countable subcover of the union of spans suffices, and connectedness joins the overlapping spans in each $I$ (distinct chains of overlaps would separate it). This proves the claim. Applied to (2), for almost every fresh tuple the completion signature is constant almost everywhere in each $H_I$.

## 3. What part of an occurrence can lie in a component?

Fix $I$ and abbreviate $H=H_I$. Almost surely, in an occurrence of $\sigma$ the sampled points in $H$ occupy consecutive positions and form a union of whole target layers. Indeed first-coordinate membership is an interval, and no target antichain of size at least two can be split between $H$ and its strictly ordered exterior. If the points inside use a nonsingleton layer and any other layer, prescribe two points $x,y$ of the nonsingleton layer as roots and one point $u_j\in H$ of the other layer as a member of the fresh tuple. There are only finitely many choices of sampled labels to consider. On this occurrence $g_{\mathbf u}(x)$ is valid, and its $j$-th entry is a strict comparison with $u_j$. By §2 this same valid value occurs at almost every point of $H$. That would put almost every point of $H$ to one side of the first coordinate of $u_j$, which is impossible because $a<(u_j)_1<b$ and the conditional first coordinate is uniform on $(a,b)$. By independence and Fubini these occurrences have measure zero. Hence, in any occurrence up to a null event, two or more samples from $H$ form either a single decreasing layer or a run of singleton layers, thus an increasing permutation. This conclusion concerns occurrences in the **original** extremal measure only.

## 4. Replacing an entire component

For any replacement permuton $W'$ inside $I^2$, write $f(W')$ for the resulting $\sigma$-density. Condition on which samples fall in $H$, numbers to its left and right, and the outside sample. If the positional cuts are not boundaries between layers of $\sigma$, or the two exterior patterns do not agree with their required segments, the contribution is zero. Otherwise the internal samples must realize precisely the intervening standardized consecutive segment $\pi$ of the target. Thus
\[
 f(W')=C+\sum_{r=2}^{m}\ \sum_{|\pi|=r} w_{r,\pi}\,d(\pi,W'),\qquad
 w_{r,\pi}\ge0,\quad w_{m,\sigma}=(b-a)^m>0.        \tag{3}
\]
Here $C$ contains zero- and one-sample terms and is independent of the replacement. All coefficients are fixed independently of $W'$; some of them may vanish. By §3, $w_{r,\pi}d(\pi,W)=0$ for each nonmonotone $\pi$.

Denote the increasing and decreasing permutations of order $r$ by $J_r,D_r$ and their permutons by $J,D$. Put $q=d(21,W)$. If $0<q<1$, then
\[
 d(D_r,W)\le q,\quad d(J_r,W)\le1-q\quad(r\ge2),
\]
with both inequalities **strict** for $r\ge3$. To verify strictness, draw four points: the event that the first pair is decreasing and the second increasing has probability $q(1-q)>0$. Such a four-set has a triple with both comparison colors, since if every triangle were monochromatic their shared edges would force all edges of the four-set to have the same color. By exchangeability a random triple is mixed with positive probability and, in some ordering, its first pair can have either color. Thus a decreasing first pair need not extend to a decreasing triple, and similarly for an increasing one. Larger monotone samples require their first three to be monotone.

Consequently (3) gives
\[
p=f(W)\le q f(D)+(1-q)f(J)\le p.                  \tag{4}
\]
The upper inequality follows because both replacements are admissible; the lower follows term by term using §3 for the nonmonotone terms. Equality forces $f(D)=f(J)=p$ and all monotone coefficients of orders $r\ge3$ to vanish by strictness. Now the sum of the terms of order at most two in (3) is an affine function of the inversion density of the replacement. It equals $p$ at both endpoints (nonmonotone terms vanish at $J,D$), so it is identically $p$. For a nonmonotone $\sigma$ one has $m\ge3$; choosing the uniform planar permuton as replacement adds at least the all-internal term $(b-a)^m/m!>0$ to that affine part, a contradiction. For monotone $\sigma$ the conclusion is immediate anyway: its maximum is one and every pair then has its prescribed orientation almost surely.

We have excluded $0<q<1$ on every positive component. All its sampled pairs are therefore almost surely of a single orientation. Together with the ordered exterior from §2 this forbids a triple of type $231$ or $312$: its inversion edges form a connected path meeting all three points, placing them in one component where their pattern instead is monotone. Thus $\mu$ is layered. The assertion about near-optimal sequences follows by compactness and continuity. No quantitative stability rate or finite equality characterization is used.
