# Five strict pieces for filled edges with controlled tip vectors

**Yongxian Zhang.** AI-assisted proof development and internal mathematical checks; no external peer review claimed.

Use the full filled edge locus and cyclic edge orientation of [the full-edge spindle theorem](BorsukFourFullEdgeSpindle.md). For a nonapex point \(p\) on edge \(i\), let \(z_p=s_p/(1-s_p)\) be its odds from the terminal apex, \(v_p=w_p/\sqrt{3s_p(1-s_p)}\) its normalized transverse vector (in the unit disk), and \(\alpha_p=1-\|v_p\|^2\). Let \(X\) be compact in the filled edge locus with diameter at most \(D=\sqrt3\). Either of the following sufficient conditions gives a cover by five sets of diameter strictly below \(D\):

1. For all sufficiently small positive odds on neighboring edges \(i,i-1\), the actual normalized vectors satisfy \(\|v_p-v_q\|\le\sqrt3\) for every such pair, equality allowed. In particular it suffices that the norms are bounded by \(\kappa_i,\kappa_{i-1}\) with \(\kappa_i+\kappa_{i-1}\le\sqrt3\), including \(\kappa_i=\sqrt3/2\) on all edges. A distinct sufficient condition is the **strict** cross-distance \(<\sqrt3\) for every pair in the two limiting normalized tip sets, rather than for the actual pairs.
2. Suppose the actual normalized radii near the tips are at most \(\kappa_i\in[0,1]\) on the respective edges. Put
\[
R_i=\max\!\left\{r\ge0:(2-\kappa_i^2)r^2-2\kappa_i\kappa_{i-1}r+1-\kappa_{i-1}^2=0\right\},
\]
with \(R_i=0\) if there is no such root. If \(\prod_i R_i<1\), five strict pieces exist. For example, \((\kappa_0,\kappa_1,\kappa_2)=(1,1,3/5)\) meets this test although the first test's radius-sum bound fails on one interface.

These conditions allow nonspherical accumulation from both halves of each filled edge. They do not settle arbitrary compact filled subsets or the four-dimensional Borsuk problem. The preceding [cutoff barrier](BorsukFourFilledTipCutoffBarrier.md) has squared normalized cross-distance approximately \(3.365>3\) and is not covered by the first condition. For the current general six-piece upper bounds see [Chalmers](https://arxiv.org/abs/2611.17375) and [Tolmachev](https://arxiv.org/abs/2611.16775).

## Gap at a tip interface

For \(p\in i,\ q\in i-1\), put \(r=\sqrt{z_p/z_q}\), \(t=z_q\). Multiplying the squared gap \(D^2-\|p-q\|^2\) by the positive factor \((1+z_p)(1+z_q)/(3z_q)\) gives
\[
G(r,t;v,w)=r^2+\alpha_p r^2\frac{1+t}{1+r^2t}
+\alpha_q\frac{1+r^2t}{1+t}+2r\,v\cdot w .
\]
A diametric pair necessarily has \(r\le2\), since all radial-deficit terms are nonnegative and \(v\cdot w\ge-1\).

For a common cutoff \(c\), the potentially dangerous outgoing-main/preceding-tip pairs have \(z_p\ge c\ge z_q\), so \(r\ge1\). At these ratios the two coefficients of \(\alpha_p,\alpha_q\) are at least 1. Hence
\[
G\ge r^2+\alpha_p+\alpha_q+2r\,v\cdot w.
\]
The expression on the right is increasing for \(r\ge1\) and strictly increasing past 1. Its value at \(r=1\) is \(3-\|v-w\|^2\). Thus under condition 1 a cross clash must have \(z_p=z_q=c\) and \(\|v-w\|^2=3\).

With the alternative strict limit assumption, any sequence of clashes at cutoffs tending to zero has \(r\in[1,2]\), both odds tending to zero and subsequentially convergent normalized vectors. The limiting bound is positive, a contradiction. This also covers cases in which either edge has no nonapex sequence tending to its tip.

## Critical odds have no interval

For each ordered interface, let \(E_i\) be the set of small positive odds \(t\) for which there are \(p_t,q_t\) on the two edges, both with odds \(t\), satisfying \(\|v_t-w_t\|^2=3\), where \(v_t=v_{p_t}\), \(w_t=v_{q_t}\). This set is closed locally on positive odds bands, by compactness of \(X\) and continuity away from an apex. We show it contains no interval.

For any vectors \(v,w\) under condition 1, put \(S=\|v\|^2+\|w\|^2\). Their dot product is at least both \(-S/2\) and \((S-3)/2\), hence at least \(-3/4\). Differentiating at \(r=1\) gives
\[
\partial_rG=2+2v\cdot w+2\alpha_p/(1+t)+2t\alpha_q/(1+t)\ \ge\ 1/2.
\]
On a fixed positive compact odds band this bound gives a uniform lower derivative, say \(1/4\), for \(r\) sufficiently close to 1, by continuity over the compact set of normal pairs of squared distance at most 3. For two nearby odds \(t<u\) in \(E_i\), compare \(p_t,q_u\); the actual diameter hypothesis gives \(G(\sqrt{t/u},u;v_t,w_u)\ge0\). Integration to \(r=1\) yields
\[
\|v_t-w_u\|^2\le3-C(u-t)
\]
for a positive constant depending on the band. The other cross square \(\|v_u-w_t\|^2\) is at most 3 by hypothesis. Subtract the two diagonal squares (each 3) to get \(2(v_t-v_u)\cdot(w_t-w_u)\le-C(u-t)\). In particular
\[
\|(v_t-w_t)-(v_u-w_u)\|^2\ge C(u-t).
\]
These difference vectors lie on the circle of radius \(\sqrt3\) in the transverse plane. If \(E_i\) contained an interval, choose a compact subinterval short enough for all the derivative estimates and take \(n\) equally spaced values. The corresponding \(n\) directions have pairwise distances bounded below by a fixed multiple of \(n^{-1/2}\), but the circle accommodates at most a fixed multiple of \(\sqrt n\) such points (compare consecutive arc lengths). Contradiction. A small positive cutoff can therefore be chosen outside the finite union of the three relatively closed nowhere dense sets. There are no cross clashes at this cutoff.

## Proportional cutoffs

Under condition 2 choose positive ratios \(\ell_i>R_i\) of product one, possible by the strict product condition. Choose positive \(\gamma_i\) with \(\sqrt{\gamma_i/\gamma_{i-1}}=\ell_i\), and use cutoffs \(c_i=\gamma_i c\) for one small \(c>0\). A cross clash on interface \(i,i-1\) would have \(r\in[\ell_i,2]\), \(z_q\le c_{i-1}\), and \(z_p\le4c_{i-1}\); thus both points lie in the controlled tips for small \(c\). The gap at \(t=0\) is at least
\[
(2-\kappa_i^2)r^2+(1-\kappa_{i-1}^2)-2\kappa_i\kappa_{i-1}r.
\]
This is positive on the compact interval because \(\ell_i>R_i\). The explicit gap formula converges uniformly there as \(t\to0\). Hence no cross clash occurs once \(c\) is sufficiently small. A similar proof works with \(R_i\) defined as the supremum of largest nonnegative roots of \((2-\|v\|^2)r^2+(1-\|w\|^2)+2rv\cdot w\) over the compact cross pair of limiting normalized tip sets (adjoin zero as the root bound for an empty set or a polynomial without nonnegative roots). For that version a countersequence of clashes suffices instead of a bound on all actual radii.

## Complete the routing

With either choice, give base color \(i\) all tips on edge \(i-1\) and the retained main points on edge \(i\), including \(a_i\) if present. The common-apex endpoint cases are strict by the positive shared barycentric coordinate, just as in the [earlier compact routing](BorsukFourFullEdgeSpindle.md#compact-routing). On any one edge equality at \(D\) other than the apex pair requires reciprocal odds and opposite spherical transverse rays. Use closed central bands \([c_i,2/c_i]\); main points outside their upper cut cannot have a reciprocal partner in the main range. In each central band route two shared near-quadrants to the spare colors and leave a closed arc of width \(<\pi\) in the base. There is a common positive lower bound \(b\) on positive barycentric coordinates on the three central bands. The shared near-quadrants can have width \(\pi/2+\varepsilon\) with \(\sin\varepsilon<2b^2\) and together cover more than \(\pi\), so any two points sharing a spare color have squared gap \(\ge3b^2-(3/2)\sin\varepsilon>0\). The two base pieces on a single color are each strict, and their cross pairs are strict by the cutoff rule. Use closed cones including zero transverse vector and closed tip/central/outer ranges. The resulting compact color pieces have strict diameters. This is a cover and can be turned into a partition by assigning overlaps arbitrarily.
