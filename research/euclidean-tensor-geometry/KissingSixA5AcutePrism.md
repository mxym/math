# Two acute punctures in the A5 equator: a reverse-convex cap certificate

**Theorem.** Suppose a six-dimensional kissing code contains 28 of the 30 signed roots of an equatorial $A_5$, the two absent roots making an angle of $60^\circ$. Its total size is at most **74**. If there is an equatorial outsider, the upper bound improves to **73**. This includes arbitrary real outsiders with no symmetry hypothesis. We do **not** exclude 73 or 74 in general, and do not assert sharpness. The [earlier punctured-equator analysis, §4](KissingE6PunctureHull.md) already gives 72 for nonacute two-hole $A_5$, and explicitly leaves the acute case open because its projected polytope protrudes beyond the unit ball. The new point here is a bound for precisely that obstructed case.

We also obtain a structural statement with no reference to a particular code: within a single closed hemisphere, any two points that violate **both** omitted constraints strictly and lie below absolute height $1/2$ are strictly less than $60^\circ$ apart; no strict gap for the supremum is claimed. Consequently each such hemisphere contains at most one of these points of a kissing code.

## 1. Ordinary points and the exceptional wedge

Work with unit vectors $x=(v,t)$ in the orthogonal sum of the sum-zero subspace of $\mathbb R^6$ and a vertical line. The 30 roots are $(e_i-e_j)/\sqrt2$. By permuting coordinates and possibly changing overall sign, take the missing roots to be $p=(e_1-e_2)/\sqrt2,\ q=(e_1-e_3)/\sqrt2$. Denote $w=\sqrt2v$. The remaining inequalities are $w_i-w_j\le1$ for all retained arrows. Every outsider satisfies $p\cdot v,q\cdot v\ge-1/2$ since the opposite arrows are retained. Call an outsider exceptional if $|t|<1/2$ and $p\cdot v,q\cdot v>1/2$.

If all root inequalities hold, $w$ is the projection of $[0,1]^6$ to its sum-zero hyperplane. Its squared norm is at most $3/2$: at cube vertices the value is $k(6-k)/6$. Suppose only one root inequality, say that of $p$, is violated. Set $a=(w_1-w_2)/2>1/2$. Each other coordinate lies within $1-a$ of the midpoint of $w_1,w_2$. Centering the vector with entries $a,-a$ and those four deviations can only reduce its norm, hence $\|w\|^2\le2a^2+4(1-a)^2$, with $a\le1$. If $|t|<1/2$ then $\|w\|^2>3/2$, forcing $a>5/6$. On $[5/6,1]$ the quadratic is at most $3a-1$, giving
\[
 \|v-p\|^2=1+\|v\|^2-2a\le t^2/3.
\]
The same applies to $q$. In particular any ordinary equatorial outsider would have to be one of these missing roots themselves, a contradiction.

On one open hemisphere, all **nonexceptional** outsiders are mutually projectively compatible, i.e. their scalar products are at least $-1/2$ as well as at most $1/2$. Two deep points ($h=|t|\ge1/2$) have lower bound $hh'-\sqrt{1-h^2}\sqrt{1-h'^2}\ge-1/2$. A shallow one is within horizontal distance $h/\sqrt3$ of a missing root $s\in\{p,q\}$, so its product with a deep $y$ is at least $s\cdot v_y+h(h_y-\|v_y\|/\sqrt3)\ge-1/2$. For two shallow ones use their approximants $s,s'$ with $s\cdot s'\ge1/2$: the lower bound is at least $1/2-(h+h')/\sqrt3+(2/3)hh'>-1/2$.

Add the 13 completely retained $A_5$ lines to these nonzero-height outsider lines. The [sharp projective bound of Anstreicher](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf) is 36 in dimension six, with equality only for the $E_6$ root lines. The retained equatorial roots generate all of $A_5$ under their reflections (their differences are edges of a connected graph, and an edge reflection exchanges its endpoints). Thus an equality system would contain both missing equatorial lines, absent from this collection; the collection instead has size at most 35. Each open hemisphere has at most $35-13=22$ nonexceptional outsiders. It remains to bound the exceptional points.

## 2. A prism and its exterior-sphere hull

In the joint-violation region order the two sink coordinates so $w_2\le w_3$, and order $w_4\ge w_5\ge w_6$. Temporarily translate so $w_2=0$. The inequalities place these translated values in the chart
\[
 w=(1+a_2,0,a_1,a_5,a_4,a_3),\qquad 0\le a_1\le a_2\le a_3\le a_4\le a_5\le1 .
\]
Indeed $w_3\le w_1-1$ since both missing constraints are violated, and the other three entries lie between $w_1-1$ and $1$. Also $w_3\ge0$ by the sink order. Subtract the mean to return to the sum-zero model. Write $W_0,\ldots,W_5$ for the images of the six order-simplex vertices, with the last $i$ entries of $a$ equal to one for $W_i$. In these coordinates the polytope contains the notorious vertex $W_4=(7,-5,-5,1,1,1)/6$ of squared norm $17/6$. Ordinary concavity of lifted height over the entire polytope is not available.

Instead use the lifted prism $Q=\operatorname{conv}(W_0,\ldots,W_5)\times[0,1]$, where $z=2|t|$. Its quadratic norm is $E(w,z)=\|w\|^2/2+z^2/4$. Actual points lie on $E=1$. The barycentric coordinate $\lambda_4$ of $W_4$ is positive for every genuine joint violation, since $w_1-w_3=1+\lambda_4$. The same notation $\mu_4$ is used for a second point.

**Exterior-hull lemma.** For a positive definite quadratic norm on a polytope, every point of its unit sphere in the polytope lies in the convex hull of (i) polytope vertices on or outside the unit sphere and (ii) intersections of polytope edges with the sphere. To see this, intersect the polytope with the exterior supporting halfspace tangent to the sphere at that point. Every vertex of the cut polytope is an original vertex or is on an original edge. The entire cut is outside the open ball. Along each original edge, every portion outside the ball is in the convex hull of its outside endpoints and its boundary crossings. This proves the claim, including boundary and lower-dimensional cut cases.

For this 5-simplex prism there are 12 vertices, 36 edges and just **16** resulting generators (including the outside ones). For two sorted points put $\pi=(1)(2\,3)(4\,6)(5)$ in one-based coordinates, reversing each of the two sortable blocks. Rearrangement gives the lowest possible scalar product over the allowed labeling choices. The following bilinear inequality holds over the two exterior hulls:
\[
 \frac12\sum_{i=1}^6 w_i w'_{\pi(i)}+\frac14zz'
 \ \ge\ \frac12+\frac12\lambda_4\mu_4 .
\]
It suffices to check the 256 generator pairs: the barycentric coordinate is affine. The [standalone exact replay](verify-kissing-a5-acute-prism.py) builds the order-simplex vertices, intersects their prism edges with $E=1$, and checks the displayed inequalities. Rational square roots are taken exactly, other quadratic roots are enclosed between rational endpoints using integer square root. The test uses the worst corner for each bilinear parameter box; it passes at both 48 and 77 bits with no uncertain sign. This is a continuous-domain certificate, not a sample of the sphere.

For a pair of actual exceptional points on the same side, $\lambda_4\mu_4>0$, so the scalar product is strictly above $1/2$. Each closed hemisphere contains at most one such point. If an equatorial outsider occurs, it is exceptional and belongs to both, so it is the **only** exceptional point globally. The total is at most $28+2\cdot22+2=74$, or $28+2\cdot22+1=73$ in the latter case. What is not ruled out is a shallow joint violator on each open side with enough ordinary outsiders; ordinary one-sided projectivization does not automatically absorb those two points.

Replay with `python3 verify-kissing-a5-acute-prism.py` (standard library only).
