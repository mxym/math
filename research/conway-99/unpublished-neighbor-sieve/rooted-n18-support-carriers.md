# Sparse same-class support intersections force many distinct rooted short fields

Assumptions and notation are those of the [preceding same-residue proof](rooted-n18-same-residue.md): rank 42 on the two-type face, four representative signed norm-18 residue classes of n=50,51,52,53 true fields each; S=2,5,8,11 excess raw (1,23) fields beyond the 99 site fields. Call root o exceptional if some true original-zero neutral field of norm 28 or 42 vanishes on all of N[o]. Then there are at least **10,10,10,9** distinct exceptional roots in the four cases, respectively.

The following support intersection bound is of independent use. For t≠u in the same selected signed residue, write H(t) for its 18-point support. Then
[
 \sum_{\beta}\sum_{\{t,u\}\subset\beta} (|H(t)\cap H(u)|-4)_+ \le 24S .
]
Here the four chosen signed classes contain no opposite vectors.

Proof. Same-residue dots are −3 or 4. In the first case t+u has neutral norm 30 and is unit: any coefficient ≥2 in magnitude, oriented positive, gives charge −1 of norm ≤25 upon subtracting its site field; (1,25) is absent as a raw field on the face, as are all smaller allowed costs produced by the step of 14. Thus no same-sign agreements occur, and support intersection is exactly 3. In the second case c=t−u has norm 28. Its number of doubled locations m is the number of opposite-sign conflicts, hence the support intersection has size 4+2m. For every (antipodal c direction, doubled site p), orient c with c_p=+2. Then b=d_p−c has charge +1, norm 23 and value +1 at p. It is not an ordinary d_j: c=d_p−d_j has norm 0,42 or56, not28. Nonordinary charge-1 norm-23 fields in this face are unit (a +2 would lead to a norm-14 field, a −2 would give, by adding d_i, a charge-two norm-22 field positive at i, whereas such a field is entirely nonpositive; lower coordinates are too short) and have six positive sites. Thus the total number of pairs (direction,doubled site) is ≤6S, by the inverse c=d_p−b. Each direction receives at most two unordered source pairs among all four selected classes, by the preceding proof (compatible with orientation of their ordered differences). Counting 2m per source proves 24S. No separate two-conflict estimate is needed.

For any k sites T, e internal edges, d_i the internal degrees, h the outside neighbor counts, sum h=14k−2e and sum binom(h,2)=2 binom(k,2)−e−sum_i binom(d_i,2). Since h−binom(h,2)≤1_{h>0} and d/2−binom(d,2)≤1/2, the common exterior anticomplete carrier has at most k²−16k+99+floor(k/2) sites. Only k=3 is needed: at most 61.

Suppose all exceptional roots are in a set E of q sites, extending E arbitrarily to that size if necessary. For each class let r_t be the number of its zero-star roots in E. Every t has at least eight zero stars by the [existing height-three cap](shared-norm-18/height-three.md); each root outside E supports at most one such t per class. So sum r_t≥8n−(99−q). The convex integer minimum V for sum binom(r_t,3) is obtained by balancing n integers at this lower total. There is some triple T in E whose star union is missed by at least m=ceil(V/binom(q,3)) fields of this class. Select any m of them. Their supports lie in a common carrier of size ≤61. The minimum L of sum_i binom(f_i,2) for the vertex frequencies f_i is found by balancing 18m incidences over 61 sites. Hence the support-overlap excess of the selected fields is at least l=L−4binom(m,2); summing over four disjoint classes is legitimate even if different triples T are used. In the respective cases the tuples (n,S,q,V,binom(q,3),m,l,4l,24S) are
(50,2,9,1150,84,14,34,136,48);
(51,5,9,1200,84,15,50,200,120);
(52,8,9,1250,84,15,50,200,192);
(53,11,8,1285,56,23,191,764,264).
Every left bound exceeds the permitted 24S, proving the assertions. A short standard-library replay checks only these four convex comparisons; the counting proof does not assume symmetry among roots or residue classes. These are lower bounds on locally nonempty short shells, NOT exclusions of any of the four graph cases.

Run `python3 rooted-n18-support-carriers.py` for the four exact convex comparisons.
