# Two independently moving ternary coordinates in five-dimensional kissing codes

Let two independent third turns act on $\mathbb C^2\oplus\mathbb R$. In a spherical $60^\circ$ code invariant under both turns, a point with both complex coordinates nonzero has a nine-point orbit. How many such orbits can coexist if their fixed-coordinate heights and phases are free?

**Theorem.** There are at most **three**, or **27 points** on that support, and this is sharp. At most two of the orbits can lie in either closed height hemisphere. This is not a determination of the unrestricted five-dimensional kissing number, or of the maximum counting the single-plane orbits as well.

**Seven-dimensional consequence.** In the [independent-three-plane theorem](https://github.com/mxym/math/blob/d2381c12458ad5a7b0aa01c92568e54691dcf405/research/euclidean-tensor-geometry/KissingSevenThreeIndependentThirdTurns.md), the zero-triple branch now has at most **103** points (previously 118). The structural conclusion for high cardinality applies already **above 117**: only deletions of equatorial axis triangles from either of the two 126-point configurations are possible. The completion need not be unique as an unrestricted code. No assertion that 117 or 103 is sharp is made.

## Three orbits cannot all have heights of the same sign

An orbit is described by radii $a,b\ge1/\sqrt3$, unsigned height $z\ge0$ with $a^2+b^2+z^2=1$, and two phases modulo $120^\circ$. The lower radius bounds follow because changing only the corresponding coordinate must move a code point by at least one.

For two permissible triples of radii and heights,
\[
              aa'+bb'+2zz'\ \ge\ (1+\sqrt2)/3 .
\]
To minimize a positive linear functional of $(a,b,z)$ first fix $z$ and minimize on the permitted circular arc in $(a,b)$. The minimum occurs at an endpoint, where one radius is $1/\sqrt3$, by concavity of the positive sine-cosine combination. For either endpoint choice, varying $z$ gives a constant plus a nonnegative multiple of $\sqrt{2/3-z^2}$ plus a linear term, again concave. It therefore suffices, separately in both triples, to test the three scaled endpoint vectors $(1,\sqrt2,0),(\sqrt2,1,0),(1,1,1)$ divided by $\sqrt3$. These give the stated minimum.

For any three phases on a circle of circumference $120^\circ$, the sum of the cosines of their three nearest separations is at least **2**. Holding two phases at distance $\delta$, the sum of the two cosines involving the third is concave on each arc cut out by the antipodes of the first two. Its minimum is $1/2+\cos(60^\circ-\delta)$. Adding $\cos\delta$ and minimizing the concave cosine sum on $[0,60^\circ]$ gives 2.

For each of three same-hemisphere pairs, split each cosine into $1/2$ plus a nonnegative remainder. In each complex coordinate the sum of these three remainders is at least $1/2$, and each corresponding product of radii is at least $1/3$. Thus the sum of the three *largest* pairwise cross-orbit inner products is at least
\[
         \tfrac32\,(1+\sqrt2)/3+2(1/3)(1/2)
           =(1+\sqrt2)/2+1/3>3/2 .
\]
The largest products are obtained by choosing nearest phases independently within the two coordinate circles. The contradiction proves the hemisphere bound, even when heights vanish.

## The remaining balanced four-orbit case

Four orbits would now have two positive and two negative heights, none zero. We give a small interval proof, checked by [an exact integer program](verify_kissing_five_three_pair_orbits.py). Scale coordinates by $\sqrt3$. Write an unsigned height as $z\in[0,1]$ and parametrize the scaled squared radii by
\[
   a^2=1+d(1-z^2),\qquad b^2=1+(1-d)(1-z^2),\qquad 0\le d\le1 .
\]
This covers even the common endpoint $z=1$. Write the phases $x,y$ in units of a whole $120^\circ$ phase circle. For every pair of orbit labels $i,j$ a necessary inequality is
\[
 a_i a_j\cos(120^\circ\,\|x_i-x_j\|)
 +b_i b_j\cos(120^\circ\,\|y_i-y_j\|)
 +\sigma_i\sigma_j z_i z_j\le3/2 ,
\]
where $\|\,\cdot\,\|$ is distance to the nearest integer and $\sigma=(+,+,-,-)$.

Reflect the height and reorder the orbits so the first is of smallest unsigned height and is positive. Interchange the complex coordinates if necessary so $d_1\ge1/2$. Rotate their phases to $x_1=y_1=0$, and conjugate each complex coordinate independently to put both phases of the second positive orbit in $[0,1/2]$. The two negative labels remain interchangeable. These are coordinate normalizations, not assumptions about extra symmetry.

The coarse grid divides $z,d,x,y$ into respectively $8,4,20,20$ intervals. Closed boxes use lower radius bounds from the upper height endpoint and the appropriate $d$ endpoint. Use the lower heights when their product has positive sign and the upper heights when it has negative sign. The cosine is bounded below at the largest allowed circular distance: the center distance plus the two phase half-widths, capped at half a circle. Every rejection is strict. Square roots are rounded down using integer square roots; cosines are rounded down at scale $10^4$ by the degree-ten alternating Taylor lower polynomial at the upper angle given by $\pi<355/113$, treating $60^\circ$ exactly. Signed integer products fit below $10^{13}$. In particular, no floating point tests decide a branch.

There are 12,800 one-orbit boxes. Intersecting the six pairwise compatibility lists, keeping the unsigned-height order and the arbitrary ordering of the two negative coarse boxes, leaves 51,160 coarse quadruples. Points on grid faces are included: equal heights can be put in the same bin before sorting, and either negative label ordering covers an equality of coarse indices. Imposing the first orbit's exact zero phases leaves 14,065. Bisect the third orbit's height, then its $d$ coordinate, then the fourth orbit's $d$ coordinate; the surviving quadruple counts are **1,845, 39, 0**. Both halves of every interval are retained unless ruled out by one of the same six inequalities. Translating a phase-index row to generate the remaining rows is just cyclic permutation of the full phase grid.

## Attainment and application

A middle orbit can have radii $1/\sqrt2,1/\sqrt2$, height zero, and phases $0^\circ,0^\circ$. Add one orbit at each of heights $\pm1/\sqrt3$, both with radii $1/\sqrt3,1/\sqrt3$ and phases $60^\circ,60^\circ$. Within an orbit each nontrivial change costs at least unit distance. The maximum pair cross product from the middle orbit to either of the others is $1/\sqrt6$, and between the two other orbits it is $1/3$. This gives 27 points, and either closed hemisphere contains two of the orbits.

For the seven-dimensional consequence let $p\in\{0,1,2\}$ count poles, $n$ count single-support points and $k$ count pair orbits, assuming no triple orbit. Every pair of the three moving coordinates forms exactly a five-space of the kind just studied, hence $k\le9$. Even without invoking any five-dimensional kissing bound, $p+n\le36$ by three ordinary three-dimensional sections, so $N=p+n+9k\le117$. For the stronger zero-triple bound, each five-dimensional section has size congruent to $p\bmod3$ and at most 43 by [Tomar's certificate](https://doi.org/10.5281/zenodo.23638108). The integral section bounds $B_p$ are therefore $42,43,41$ respectively. Summing the three sections yields
\[
       2N\le 3B_p+9k-p\le3B_p+81-p .
\]
Together with $N\equiv p\bmod3$ this gives $N\le102,103,101$ respectively. The one-triple and incomplete two-triple branches already had size at most 117 in the seven-dimensional proof, so $N>117$ forces its full two-layer structure. Neither result requires knowing an unrestricted kissing number exactly in dimensions five, six or seven.

**Replay:** `python3 verify_kissing_five_three_pair_orbits.py` (NumPy; ordinary Python with assertions enabled).
