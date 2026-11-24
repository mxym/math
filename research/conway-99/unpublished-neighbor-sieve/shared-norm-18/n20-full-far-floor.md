# Exact far-coordinate congruence at a norm-twenty seed

Work in a hypothetical SRG(99,14,1,2); use the \(P=(3I-A+J/9)/7\) projector and the near calculation from the [five-low-angle proof](n20-low-five-projection.md). A rooted norm-20 marking is a signed-unit \(-4\) field with independent shores, positive root \(o\), and the same four negative parents \(Q\) in \(N(o)\). Let \(R\) be their four mates in \(N(o)\), and \(B\) the six first-layer vertices on the other three axes. Every far vertex is specified by its two first-layer parents in distinct axes. We assume the true neutral minimum is 20 where explicitly used, and assume the angle alphabet \(\{5,6,9,10\}\) in the stated high-graph estimates. No residue or averaging condition is imposed.

The near projection \(t_0\) is the same for each marking. Its squared norm is \(35/4\). The inverted near equations already give coefficient \(c_o=0\), \(c_q=-35/16\), \(c_r=-7/16\), \(c_b=7/16\), \(\sum c_i/9=-7/8\). Therefore \(t_0\) takes these far values by parent type:
\[
\begin{array}{c|rrrrrr}
\text{type}&QQ&QR&QB&RR&RB&BB\\ \hline
\text{count}&6&12&24&6&24&12\\
t_0&1/2&1/4&1/8&0&-1/8&-1/4 .
\end{array}
\]
For example a \(QR\) label uses different axes, so it has one parent coefficient \(-35/16\) and the other \(-7/16\). Including the constant \(-7/8\) and dividing by seven gives \(1/4\). The other five entries follow identically. In particular \(8t_0\) is a genuine integral neutral eigenfield (its near values are also integral).

## Three and five copies of the near pattern

Take an integral neutral eigenfield \(z\) whose near values are five times those of a rooted marking. The sum of far values adjacent to a first-layer site is \(15\) on \(Q\), zero on \(R\), and \(-5\) on \(B\), by its exact eigen-equation. For each far type use baseline integral values \(x_0=(2,1,1,0,-1,-1)\). On one site each let \(f(x)=(x-5t_0)^2\). The sum of baseline energies is \(39/4\), and one choice of discrete supporting slopes is
\[
c_{QQ}=0,\quad c_{QR}=1/2,\quad c_{QB}=-1/4,\quad
c_{RR}=1,\quad c_{RB}=1/4,\quad c_{BB}=-1/2 .
\]
For every integer \(x\), \(f(x)-f(x_0)\ge c_{\rm type}(x-x_0)\): each displayed value is one of the two adjacent-unit secant slopes of the convex quadratic. It is also the sum of the two parent weights \((\lambda_Q,\lambda_R,\lambda_B)=(0,1/2,-1/4)\). The baseline row sums at each first-layer vertex are \(15,-3,-4\) on \(Q,R,B\) respectively, by the numbers of parents of each type. Thus deviations have total \(0,12,-6\) on those three groups, and the exact energy bound is
\[
 \|z-5t_0\|^2\ge39/4+12/2+6/4 = 69/4.
\]
Equality at every coordinate gives the following allowed integer values:
\[
 QQ:\{2,3\},\ QR:\{1,2\},\ QB:\{0,1\},\
 RR:\{0,1\},\ RB:\{-1,0\},\ BB:\{-2,-1\}.
\]
By replacing an integral field with near pattern three by \(8t_0-z\), the same energy floor \(69/4\) holds for three copies, with equality ranges
\[
 QQ:\{1,2\},\ QR:\{0,1\},\ QB:\{0,1\},\
 RR:\{-1,0\},\ RB:\{-1,0\},\ BB:\{-1,0\}.
\]
In particular any three actual markings at the seed with all pairwise dots at most six have all dots exactly six, since their residual energy is at most \(3(45/4)+6(6-35/4)=69/4\), and any dot below six reduces it. In such a low triangle, every center occurs in one or two fields, and no positive singleton site can be shared, since QR and QB sites never have negative values in any source.

Call a pair high when its dot is nine or ten. For five markings with at most two high pairs, the residual energy is at most \(5/4+8\cdot2=69/4\), where \(5/4\) is the all-dot-six comparison and each possible high pair adds at most eight. Thus every five-set has at least two high pairs; exactly two require those two dots ten, all other dots six, and all equality ranges above. This does not assert impossibility of the exactly-two configuration.

## Low K4 saturation and uniqueness

In a four-clique of low pairs all dots are six by the triple conclusion. For each center, every three of the four coordinates have sum one or two; hence its full sum is two. The four markings have twelve center selections in total. Each marking individually selects at least three centers: the four negative parents each have exactly three additional positive neighbors beyond \(o\), so twelve parent incidences fall on the nine other positive sites, and at most two per site. Consequently all four select exactly three centers and have exactly six singleton positives and no zero-parent positives. Their six private negatives per marking are all at zero-parent sites.

The projection \(4t_0\) is integral except on the 24 QB and 24 RB sites, where it is a half-integer. Thus the squared distance to an integral field agreeing with the near pattern is at least \(48/4=12\). The sum of the four actual fields attains exactly 12 by the dot-six Gram. Hence its far values are fixed on QQ, QR, RR, BB as \(2,1,0,-1\), respectively, and lie in \(\{0,1\}\) on QB and \(\{-1,0\}\) on RB. In particular the individual fields never mark an RR site (all values there were nonpositive), and the twelve QR positives as well as the twelve BB negatives occur once each.

At every \(r\in R\), the adjacent near values \(+1,-1\) cancel. In each of the four fields, the only possible adjacent marked far sites are positive QR and negative RB, since RR sites are entirely unused. Summing these row equations over \(R\) gives \(\#QR^+=\#RB^-\) per field. Since every field has six private negatives and six positive singletons, each has exactly six nonzero entries across QB and RB combined. If the neutral minimum is 20, a low triangle has at most one completion to a low K4: two candidates have the same entries on QQ, QR, RR, BB by subtraction of the fixed four-sums, and both have only six support entries in QB and RB. The signs are fixed in each of those categories; hence the neutral difference would have squared norm at most 12.

## The actual 44-set emitted by every low triangle

For a low triangle set \(z=t_1+t_2+t_3\), \(D_Q=\sum_{q\in Q}(3I-A)e_q\). Then \(z^2=96\), \(D_Q^2=116\) (the four parents are independent), and \(z\cdot D_Q=-84\). The field \(b=z+D_Q\) has charge four and squared norm 44. Equality between this cost and absolute coordinate sum forces \(b=-1_Y\) for an actual 44-set \(Y\), with induced degree four. It contains the root and exactly its four \(R\)-mates among \(N(o)\), so \(Y,o\) recover \(Q\) and \(z=b-D_Q\).

Assume now the actual neutral minimum 20. The three sources are determined by the sum \(z\). If two distinct triples give the same sum and share one source, the remaining pair sums would agree, but dotting with one source gives \(20+6=26\) on its own side and at most 20 on the other, since any two distinct norm-20 fields have dot at most ten. Sharing two sources makes the decompositions equal. If the triples are disjoint, their nine cross dots sum to at most 90, whereas their sums are equal with squared norm 96. Thus there is at most one low triangle for fixed \((Y,o)\) and at most 44 per literal 44-set. A five-set attaining the two-high equality also produces a 44-set by the same argument with the integral field \(z=8t_0-\sum_{i=1}^5t_i\) in place of the low triple sum; this does not assert that the complemented field admits a low triple decomposition.

## Graph-wide counting consequences

Under the same neutral minimum and angle alphabet assumptions, let \(T_{\rm hi}\) count high triangles with their common positive rooted seeds. A triangle-free high graph at a seed has at most ten vertices when every five-set contains at least two high edges. Here is the elementary extremal check. An independent five-set is forbidden. If there is no independent four-set either, \(R(3,4)=9\) bounds the order by eight. Otherwise fix an independent four-set \(I\). Every exterior vertex has at least two neighbors in \(I\). For any \(i\in I\), its exterior nonneighbors are independent (any two share a neighbor within the other three of \(I\), so cannot be adjacent) and number at most three, since they are also independent with \(i\). All degrees are at most four, as are the independent neighborhoods. Thus there are at most seven exterior vertices; if exactly seven, every \(i\) has degree four. Total incidences into \(I\) then equal 16, so either two exterior vertices have three contacts or one has four. Such vertices are isolated within the exterior, as their \(I\)-subsets meet any of the other \(I\)-subsets. The other exterior vertices have size-two \(I\)-subsets; they can be adjacent only between complementary classes (three disjoint class pairs). Two isolates and five further vertices give an independent set of at least five. One isolate and six further vertices force every complementary pair to have balanced class sizes, or else an independent five-set again. Each class has size at most two, as three together with the two omitted vertices of \(I\) would be independent. The three balanced class sizes sum to three, so one is one. The isolate, one entire class per pair, and the other singleton of the size-one pair form five vertices with at most one edge, contradiction.

From a pool at a seed delete one vertex per high triangle; what remains is triangle-free. In all 55,440 seeds, each oriented norm-20 field appears ten times. This yields \(T_{\rm hi}\ge10N_{20}-554{,}400\). Alternatively delete one vertex per high triangle and per low K4, so \(R(3,4)=9\) leaves at most eight. Every low K4 has four distinct low triangles, none shared with another low K4 at that seed, and low triangles globally number at most \(44G_{4,44}\) by the actual 44-set recovery. Hence
\[
 T_{\rm hi}+11G_{4,44}\ \ge\ 10N_{20}-443{,}520.
\]
These are literal graph counts; \(N_{20}\) is oriented and the charge-four count uses the one canonical charge orientation. No upper on the total high triangles that would close a rank or support is claimed.

### More pressure from monochromatic triples

If a seed has \(m\) fields and high-graph degrees \(d_i\), its total number of high and low triangles equals
\[
 \binom m3-\frac12\sum_i d_i(m-1-d_i)
 \ \ge\ \binom m3-\frac m2\left\lfloor\frac{(m-1)^2}{4}\right\rfloor .
\]
Indeed a nonmonochromatic triple is counted twice in the degree sum (the two vertices incident with edges of different colors). The integer ceiling of this lower bound is always at least \(24m-272\). For \(m=2k\), the difference before rounding, multiplied by 3, is \((k-8)(k^2+5k-102)\), nonnegative for integer \(k\ge0\). For \(m=2k+1\), the difference multiplied by 6 is \((k-8)(2k^2+13k-186)\), also nonnegative except at \(k=7\), where the difference is \(-1/2\) and the ceiling gives equality. The resulting linear bound can be summed over seeds directly. Since there are at most \(44G_{4,44}\) low-triangle incidences, it gives the additional exact inequality
\[
 T_{\rm hi}+44G_{4,44}\ \ge\ 240N_{20}-15,079,680.
\]
Here \(G_{4,44}\) is the actual charge-four count, not a residue average. A bound on it from a different face cannot be used to close this inequality.

A [physical far-coordinate Schur obstruction](n20-eighteen-block-obstruction.md) excludes the special 18-marking Gram pattern of six low triangles all separated by dot nine. It is not a general cap on seed occupancy.
