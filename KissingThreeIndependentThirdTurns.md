# A sharp 60-point rigidity threshold for three independent third turns in six dimensions

Identify $\mathbb R^6$ with three orthogonal complex lines. Let $G=(C_3)^3$ rotate each line independently through $120^\circ$ and fix the other two pointwise. A kissing code consists of unit vectors with pairwise distances at least one.

**Theorem.** A $G$-invariant kissing code has at most **72** points, and equality is unique up to orthogonal isometry: the $E_6$ root code. More strongly, **every such code with more than 60 points is contained in a unique copy of the 72-point $E_6$ code** in the same six-dimensional space. The threshold is sharp: **up to isometry there is exactly one** $G$-invariant 60-point kissing code not contained in *any* isometric copy of $E_6$. With exactly one triple orbit the sharp maximum is 57.

No transitivity, antipodes or assumed root subconfiguration is required. The independent actions are essential: a single order-three symmetry or a diagonal simultaneous rotation does not give the hypothesis. This is a symmetry-class theorem and does **not** exclude an arbitrary 73-point code. The [ordinary six-dimensional kissing-number problem](https://cohn.mit.edu/kissing-numbers/) remains separate.

## Only three supports are possible

In each plane where a point is nonzero, its radius is at least $1/\sqrt3$, since rotating just that plane moves the point distance $\sqrt3$ times the radius. A point therefore has one, two or three active coordinates, and its orbit has 3, 9 or 27 points respectively. Call these axis, pair and triple orbits. Every triple orbit has radii exactly $1/\sqrt3$. A pair orbit has radii $a,b\ge1/\sqrt3$, $a^2+b^2=1$ on its specified support. Any two permissible pair radius-vectors $(a,b),(a',b')$ on the same support satisfy
\[
     aa'+bb'\ge2\sqrt2/3 ,
\]
because all lie on the circular arc from $(1,\sqrt2)/\sqrt3$ to $(\sqrt2,1)/\sqrt3$.

Record a phase modulo $120^\circ$. Two phases have nearest angular separation $\delta\in[0,60^\circ]$. Comparing different orbits, the largest inner product is obtained by taking the nearest phases independently on every common coordinate. In particular each axis holds at most two axis orbits (six circle points).

On any given pair support there are at most **two** pair orbits. With three phases in the first coordinate a closest pair would have $\delta\le40^\circ$. In the other coordinate $\cos\delta'\ge1/2$, giving a product at least
\[
 \tfrac12(aa'+bb')+(\cos40^\circ-\tfrac12)aa'
 >\sqrt2/3+(1/\sqrt2-1/2)/3>1/2 .
\]
The last inequality is $3\sqrt2>4$.

## Two triple orbits force the root code

For two triple orbits the largest mutual product is $\frac13\sum_{i=1}^3\cos\delta_i\ge1/2$. Thus equality is necessary in every coordinate: the second phase on every circle is the antipodal phase modulo $120^\circ$. It is uniquely specified by the first, so there are at most two triple orbits.

Suppose there are two. No pair orbit can occur: measured from the first triple its two phase separations are $\delta,\gamma$ and from the second they are $60^\circ-\delta,60^\circ-\gamma$. The two kissing inequalities would give
\[
 \sqrt3\ge a[\cos\delta+\cos(60^\circ-\delta)]
              +b[\cos\gamma+\cos(60^\circ-\gamma)]
 \ge \tfrac32(a+b)>\sqrt3 .
\]
Here the cosine sum is minimized at an endpoint, and $a+b>2/\sqrt3$ since $a^2+b^2=1$. Each axis point must also be at angular distance at least $30^\circ$ from the phases of *both* triples on its coordinate. These are precisely the six midpoint rays. Thus, after rotating the three planes, **every point** belongs to
\[
 \mathcal E=T\ \cup\ (-T)\ \cup\
 \{(\text{one coordinate }\exp(i(\pi/6+j\pi/3)),\;\text{the others zero}):0\le j<6\},
 \quad
 T=\{(\omega^i,\omega^j,\omega^k)/\sqrt3:0\le i,j,k<3\},\qquad
 \omega=e^{2\pi i/3}.
\]
The axial set here includes all three choices of coordinate. Between distinct vectors all products in $\mathcal E$ are in $\{-1,-1/2,0,1/2\}$. The [integer checker](verify_kissing_three_independent_third_turns.py) identifies the code explicitly: represent $\sqrt3\,\mathcal E$ in $\mathbb Z[\omega]^3$, find six simple roots whose Cartan graph has arm lengths $1,2,2$ and apply their six reflections. The resulting orbit is exactly these 72 vectors, hence this is the unit $E_6$ root code. The $E_6$ configuration itself is classical, not a new configuration.

There is uniqueness of *completion*, not just an explicit extension. Any copy of the $E_6$ root code containing $T$ also contains $-T$ by antipodality. For $x,y\in T$ that differ in just one coordinate, $x\cdot y=1/2$, so reflection in the root $y$ sends $x$ to $x-y$. These differences give all six stated axial directions on each coordinate. Thus any such copy contains all of $\mathcal E$, and equality of their sizes forces it to be $\mathcal E$. This argument does not assume the proposed completion respects the original symmetry planes.

## With at most one triple orbit, the size is at most 60

Let $p$ be the number of planes having some axis points; a nonempty axis supplies a whole phase orbit. First suppose there is **no** triple orbit. If a pair support joins two nonempty axes, it carries at most one pair orbit. Indeed each pair phase, tested against the corresponding axis orbit, lies within $30^\circ$ of the opposite axis phase: $\rho\cos\delta\le1/2$, $\rho\ge1/\sqrt3$. At a coordinate with $\rho\ge1/\sqrt2$ this allowable radius is only $15^\circ$. For two proposed pair orbits, use a larger coordinate of the first. The two phases there would be at distance at most $15^\circ+30^\circ=45^\circ$; in the other coordinate the distance is still at most $60^\circ$. The preceding radius-vector estimate, now with $\cos45^\circ$, gives product at least $(3\sqrt2-1)/6>1/2$. If **both** axes contain their full six points, even one pair orbit is impossible: the nearest axis ray is at distance at most $30^\circ$, so both radii must be at most $1/\sqrt3$, inconsistent with $a^2+b^2=1$.

For $p=0,1,2,3$ these facts give upper bounds **54, 60, 54, 45**: for $p\le1$ there are at most six pair orbits and $6p$ axis points. For $p=2$ there are at most five pair orbits and nine axis points unless both axes are full, when the pair support between them is empty and the bound is $4\cdot9+12$. For $p=3$ there are at most three pair orbits and at most 18 axis points. In particular the maximum here is at most 60.

Now take exactly **one** triple orbit, putting its three phases at zero by rotating the coordinate planes. If a pair orbit has phase distances $\delta,\gamma$ from zero, then
\[
                   a\cos\delta+b\cos\gamma\le \sqrt3/2 .
\]
This implies $\delta,\gamma>36^\circ$. For otherwise the left side is at least $a\cos36^\circ+b/2$, minimized on the permissible radius arc at $(a,b)=(1,\sqrt2)/\sqrt3$. This minimum exceeds $\sqrt3/2$ because $\cos36^\circ>4/5$ and $1/\sqrt2>7/10$. Consequently all pair phases at each coordinate lie in the open arc $(36^\circ,84^\circ)$ modulo $120^\circ$. Two pair orbits on the same support would have nearest products at least $(2\sqrt2/3)\cos48^\circ>1/2$: use $\cos48^\circ>\sin36^\circ>1/\sqrt3$. There is now at most one pair orbit per support.

Furthermore, a pair support **cannot join two nonempty axes**. On each coordinate an axis phase must belong to $[30^\circ,90^\circ]$ to coexist with the triple orbit. For the pair phase at distance $\delta\in(36^\circ,60^\circ]$ from zero, the greatest possible distance to a phase in this axis arc is $90^\circ-\delta$. This follows by reflecting the phase circle if necessary and observing that the opposite point is outside that arc. Kissing compatibility therefore requires $a\sin\delta\le1/2$. If both axes were nonempty the two inequalities would imply
\[
  a\cos\delta+b\cos\gamma
   \ge \sqrt{a^2-1/4}+\sqrt{b^2-1/4}
   \ge (1+\sqrt5)/(2\sqrt3)>\sqrt3/2 .
\]
The concave sum of the two square roots is minimized at an endpoint of $1/3\le a^2=1-b^2\le2/3$. This is the desired contradiction.

Counting now gives at most $27+9(3-\binom p2)+6p$ points, respectively $54,60,57,45$ for $p=0,1,2,3$. This proves that more than 60 forces the two-triple case above.

## What happens at the boundary

The maximum is **54+18=72** with two triple orbits, **57** with exactly one, and **60** with none. In the last case there is just **one** 60-point code up to isometry, namely the non-root witness below. In particular the largest counterexample to root containment is unique.

Here is the additional upper bound when there is exactly one triple orbit. A putative size above 57 must equal 60 (all orbit sizes are multiples of three). The count just proved forces one full six-point axis, say the first, and one pair orbit on each of the three supports. The full axis has phases $30^\circ,90^\circ$ modulo $120^\circ$, forced by compatibility with the triple at phase zero. On supports $12,13$ the first radius is exactly $1/\sqrt3$: a nearest axis point is within $30^\circ$, and the radius is at least $1/\sqrt3$. The first pair phase is a midpoint between consecutive axis rays, and must be $60^\circ$ rather than zero by the triple constraint. On the other active coordinate the radius is $b=\sqrt{2/3}$, and compatibility with the triple puts its phase in $[45^\circ,75^\circ]$ since
\[
  (1/\sqrt3)\cos60^\circ + b\cos\delta\le\sqrt3/2 .
\]

Let $c_2,c_3$ be the radii of the putative pair on support $23$. Let $\alpha_i\in(36^\circ,60^\circ]$ be its phase distances from zero, and write $x_i=c_i\cos\alpha_i,\ y_i=c_i\sin\alpha_i$. Then $x_i\ge m=1/(2\sqrt3)$ and the triple constraint gives $x_2+x_3\le3m$. The phase distance to the corresponding $12$ or $13$ orbit is at most $15^\circ+(60^\circ-\alpha_i)$. Consequently
\[
  sx_i+ky_i\le t,\qquad s=\sin15^\circ,\quad k=\cos15^\circ,\quad
  t=1/(2b)=\sqrt6/4.
\]
Since $y_i\ge0$ we may square these bounds. From $\sum_i(x_i^2+y_i^2)=1$ we get the necessary condition
\[
  0\le x_2^2+x_3^2-2st(x_2+x_3)+2t^2-k^2 .
\]
But this convex quadratic is negative at every vertex of the triangle $x_i\ge m,\ x_2+x_3\le3m$. At $(m,m)$ it equals $2/3-\sqrt3/2$, and at the two other vertices it equals $25/24-5\sqrt3/8<0$. Thus 60 is impossible.

To attain 57 take $T$, the first-axis triangle of phase $30^\circ$, and three nine-point orbits on supports $12,13,23$, all with equal radii $1/\sqrt2$. Their respective phase pairs are $(75^\circ,60^\circ),(75^\circ,60^\circ),(60^\circ,60^\circ)$. Across different pair supports the maximum product is at most $1/2$. Against $T$ the largest pair product is $(1+\sqrt2)/(2\sqrt6)<1/2$; against the axis triangle the bound is $\cos45^\circ/\sqrt2=1/2$. The within-orbit and axis-to-triple bounds are immediate.

For the uniqueness statement with no triple orbit, attaining 60 forces a single full axis (say the first) and two pair orbits on every support. On supports $12,13$ the full axis forces the first radius to be $1/\sqrt3$ and its phases to be precisely midpoints between axis points; the other radius is $b=\sqrt{2/3}$. Two orbits on the same support with identical radii must be negatives: their nearest inner product is at least $(a^2+b^2)/2=1/2$, with equality only for opposite phases on both coordinates. Thus the two orbits on each such support project onto six equally spaced rays in plane 2 or 3. By compatibility with those six rays, *each* radius of a $23$ orbit must be at most $1/(2b\cos30^\circ)=1/\sqrt2$. Both are therefore $1/\sqrt2$, their phases are midpoints, and the two orbits on $23$ are negatives too.

Rotate plane 1 to make its full axis have phase zero. In each of the signed blocks $12,13$, choose the sign whose first phase is $30^\circ$, and rotate its other plane so its other phase is zero. In block $23$ each coordinate phase is now $30^\circ$ or $-30^\circ$ modulo $120^\circ$. Conjugating either of planes 2 and 3 fixes the already normalized blocks as sets and lets us select $30^\circ$ in both. This gives exactly the witness below.

## A non-root 60-point witness

Set $\eta=e^{i\pi/6}$. Take all $G$-translates and negatives of each of the four seeds
\[
 (1,0,0),\qquad (\eta/\sqrt3,\sqrt{2/3},0),\qquad
 (\eta/\sqrt3,0,\sqrt{2/3}),\qquad (0,\eta/\sqrt2,\eta/\sqrt2).
\]
These give $6+18+18+18=60$ points. Within one pair support, a nontrivial third turn costs at least unit distance; comparing opposite phase orbits gives product at most $1/2$. Between supports $12$ and $13$ products have magnitude at most $1/3$. With support $23$ the overlapping coordinate contributes at most $\sqrt{2/3}\cdot(1/\sqrt2)\cos30^\circ=1/2$. The first-axis comparisons have the same upper bound. The second and third displayed seeds have product **$1/3$**, impossible in an $E_6$ root subset. Hence the threshold 60 cannot be lowered.

**Replay.** Run `python3 verify_kissing_three_independent_third_turns.py` in normal standard Python. The program checks all 2,556 unordered pairs of the root model and all 1,770 pairs of the non-root example by exact integer arithmetic, all 1,596 pairs of the one-triple 57-point example, as well as the simple-root diagram and the full 72-point reflection orbit. The orbit-support bounds and the case split in the proof are analytic. This differs from a global vertex-transitivity assumption, as in the [earlier six-dimensional result](https://github.com/mxym/math/blob/21ddf28035c77f159f6ea0032d7b0d868ab78d4a/research/euclidean-tensor-geometry/KissingSixVertexTransitive.md), and from classic [local rigidity of the already specified root code](https://arxiv.org/abs/1102.5060).
