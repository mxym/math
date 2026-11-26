# Three directions suffice for the planar Hadwiger–Debrunner (4,3) bound

**Theorem.** Fix three distinct unoriented directions in the plane. Every finite family of at least four nonempty compact convex polygons all of whose edges use those directions, and in which every four members have three with a common point, can be pierced by three points. This bound is sharp, even for pairwise-intersecting families of proper six-sided translates with those directions. More generally the upper bound applies to any sets expressible as intersections of strips from three fixed directions, including degenerate such intersections.

The unrestricted planar problem is not settled here. The published general bounds are \(3\le HD_2(4,3)\le9\), the upper due to [McGinnis](https://arxiv.org/abs/2010.13195). The purely homothetic-triangle case and its nine-translate sharpness example are due to [Kynčl–Tancer, Theorems 7–9](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v15i1r27). This argument handles both orientations of triangle and arbitrary mixed polygons using all six oriented normals, with no homothety, symmetry, or pairwise intersection assumption on the original family. The sharpness construction below is a rational barycentric form of their example, with exact perturbation into hexagons. A targeted prior-art search found no overlapping result; [Katchalski–Nashtir, arXiv:1201.0241](https://arxiv.org/abs/1201.0241) binds families of related polygons under pairwise intersection without requiring the (4,3) property, and its three-normal case is the positively homothetic triangle class. This is not an exhaustive priority claim.

## 1. Box coordinates and one-sign families

Three nonparallel planar linear forms have a linear dependence whose three coefficients are nonzero. Rescale and sign the forms to express the plane in coordinates \(x_1+x_2+x_3=0\). Each member \(S\) is the section of a box by this plane, with bounds \(l_i(S)\le x_i\le u_i(S)\). Use the tight bounds, namely the actual extrema on \(S\). For any nonempty subfamily \(\mathcal G\), write \(L_i(\mathcal G)=\max_{S\in\mathcal G} l_i(S)\) and \(U_i(\mathcal G)=\min_{S\in\mathcal G}u_i(S)\). Its intersection is nonempty if and only if
\[
 L_i(\mathcal G)\le U_i(\mathcal G)\quad(1\le i\le3),\qquad
 \sum_iL_i(\mathcal G)\le0\le\sum_iU_i(\mathcal G). \tag{1}
\]
Indeed an axis-aligned box is nonempty exactly when its intervals are; the range of the sum on that box is the interval between those two sums.

Call \(\mathcal G\) coordinate-overlapping if \(L_i(\mathcal G)\le U_i(\mathcal G)\) in all directions, as is necessarily the case for any pairwise-intersecting family. If its total intersection is empty, exactly one sum inequality in (1) fails. Call the family lower-obstructed if \(\sum_i L_i>0\), upper-obstructed if \(\sum_i U_i<0\). For a lower-obstructed coordinate-overlapping family, every subfamily has a common point exactly when its lower maxima sum to at most zero: all its coordinate intervals overlap, and its upper minima sum is at least the original \(\sum U_i\ge\sum L_i>0\). Upper-obstructed is the reflection of this principle. In particular, for all lower-obstructed families we can check just one scalar sum for *every* subfamily, without changing the nerve or replacing original polygons by larger sets in the final piercing construction.

## 2. Three canonical clusters in the pairwise case

Assume \(\mathcal G\) is pairwise intersecting, inherits the (4,3) condition, and is lower-obstructed. Set \(L_i=L_i(\mathcal G)\) and choose \(B_i\in\mathcal G\) at which the lower extremum \(L_i\) is attained. The witnesses are necessarily distinct: if two extrema came from one member, its pair with a witness for the third would be disjoint by (1). Define
\[
 q_i=-\sum_{j\ne i} L_j,\qquad
 \mathcal G_i=\{S\in\mathcal G:l_i(S)\le q_i\}.
\]
Since \(\sum L_i>0\), one has \(q_i<L_i\). Each cluster \(\mathcal G_i\) has common intersection by (1): its lower maxima are bounded above by \(q_i\) in direction \(i\), and by \(L_j\) in each other. If \(\{i,j,k\}=\{1,2,3\}\), the pair \(B_j,B_k\) intersects, so \(l_i(B_j),l_i(B_k)\le q_i\), and \(B_j,B_k\in\mathcal G_i\). Also \(B_i\notin\mathcal G_i\). More precisely,
\[
 B_j\cap B_k\cap S\ne\varnothing
 \quad\Longleftrightarrow\quad S\in\mathcal G_i. \tag{2}
\]
Indeed at directions \(j,k\) the lower maxima in this triple are already \(L_j,L_k\); the contribution from \(i\) is at most \(q_i\) exactly when \(l_i(S)\le q_i\).

The three clusters cover \(\mathcal G\): the three witnesses are covered by their membership in the other clusters, and for any fourth distinct member \(S\), the witness triple is empty so some two witnesses meet \(S\) by (4,3), giving (2). This also handles a three-member lower-obstructed family, when there is no fourth member to consider. If a pairwise family is instead upper-obstructed, reflect all coordinates. If it has common intersection, use one point. This proves the theorem for pairwise families, including its use on small subfamilies below.

## 3. Reduction in the nonpairwise case

The disjointness graph has no two disjoint edges (their four vertices would violate the (4,3) condition) and no triangle (add any fourth vertex). Thus if it has edges they all share a center \(A\). Write \(\mathcal R=\mathcal F\setminus\{A\}\), and partition \(\mathcal R=\mathcal M\sqcup\mathcal N\) into members meeting and disjoint from \(A\), respectively. The families \(\mathcal R\) and \(\mathcal P=\{A\}\cup\mathcal M\) are pairwise intersecting. The nonempty family \(\mathcal N\) has a common point: any three of its members must intersect by considering their quadruple with \(A\), and Helly's theorem applies (pairs already intersect). In fact any two distinct members of \(\mathcal N\) and any third member of \(\mathcal R\) intersect, by the same four-set test.

If \(\mathcal R\) or \(\mathcal P\) has common intersection, we can pierce by at most two points, using respectively one extra point in \(A\) or in \(\bigcap\mathcal N\). If the two pairwise families have opposite obstruction signs, \(\mathcal M\) has common intersection: its coordinates overlap, it inherits the lower inequality from the upper-obstructed family and the upper inequality from the lower-obstructed one. Piercing \(\mathcal M,\mathcal N,\{A\}\) separately takes at most three points.

We may therefore reflect coordinates and assume both \(\mathcal R\) and \(\mathcal P\) are lower-obstructed. Let \(B_1,B_2,B_3\) denote the lower-extremal witnesses of \(\mathcal R\) as in §2. There are three cases.

### 3a. An extremal witness of \(\mathcal R\) is disjoint from \(A\)

Use the witnesses \(B_1,B_2,B_3\) and clusters \(\mathcal R_i\) of §2 for \(\mathcal R\). Renumber so \(A\cap B_1=\varnothing\). Keep clusters \(\mathcal R_2,\mathcal R_3\) as two pierced groups. Let \(\mathcal X=\mathcal R\setminus(\mathcal R_2\cup\mathcal R_3)\), so \(\mathcal X\subseteq\mathcal R_1\) and consists of no witnesses. Our third group is \(\{A,B_2,B_3\}\cup\mathcal X\).

In the quadruple \(A,B_1,B_2,B_3\), the witness triple is empty and \(A,B_1\) are disjoint, so \(A\cap B_2\cap B_3\ne\varnothing\). For every \(S\in\mathcal X\) and \(j\in\{2,3\}\), the quadruple \(A,B_1,B_j,S\) forces \(A\cap B_j\cap S\ne\varnothing\): it cannot use \(A,B_1\), and \(B_1,B_j,S\) is empty by (2) and the definition of \(\mathcal X\). In particular, the third group lies inside \(\mathcal P\).

To check its global lower sum, choose witnesses for the three lower maxima of this group. In directions 2 and 3 they can be chosen from \(A,B_2,B_3\), since \(B_2\) and \(B_3\) attain the respective global maxima on \(\mathcal R\). Thus if direction 1 is witnessed by \(S\in\mathcal X\), the witnesses are \(S\) with two members of \(\{A,B_2,B_3\}\), possibly fewer if the labels repeat. The pair \(B_2,B_3\) meets \(S\) by (2) and \(S\in\mathcal R_1\); the pairs \(A,B_j\) meet \(S\) by the preceding forced triples. If direction 1 is not witnessed by \(\mathcal X\), all witnesses are in the intersecting triple \(A,B_2,B_3\). Thus in every case the witnesses intersect, the lower sum is feasible, and (1) for subfamilies of \(\mathcal P\) proves that the third group intersects.

### 3b. \(A\) is a lower-extremal witness of \(\mathcal P\) in some coordinate

Renumber that coordinate as 1, and use \(A\) as the first extremal witness in the canonical clusters for \(\mathcal P\). In this paragraph the remaining two witnesses refer to \(\mathcal P\) rather than \(\mathcal R\). Let \(B_2,B_3\) be the other two witnesses and use \(\mathcal P_2,\mathcal P_3\) as the first two pierced groups. The unassigned members of \(\mathcal P\) are \(\mathcal X=\mathcal P\setminus(\mathcal P_2\cup\mathcal P_3)\subseteq\mathcal P_1\), a subfamily of \(\mathcal M\) excluding all three witnesses. The third group will be \(\mathcal N\cup\{B_2,B_3\}\cup\mathcal X\), a subfamily of \(\mathcal R\).

For each \(N\in\mathcal N\), \(N\cap B_2\cap B_3\ne\varnothing\) by the quadruple \(A,N,B_2,B_3\): neither triples using \(A,N\) nor the canonical witness triple \(A,B_2,B_3\) can meet. For every \(S\in\mathcal X\) and \(j\in\{2,3\}\), \(N\cap B_j\cap S\ne\varnothing\) by \(A,N,B_j,S\), since \(A\cap B_j\cap S=\varnothing\) by (2). Finally \(B_2\cap B_3\cap S\ne\varnothing\) by (2) and \(S\in\mathcal P_1\), and any two distinct members of \(\mathcal N\) and any third member of \(\mathcal R\) meet as noted above.

For the third group's lower maxima, the witnesses for directions 2 and 3 may be chosen from \(\mathcal N\cup\{B_2,B_3\}\), since \(B_2,B_3\) attain those maxima over \(\mathcal P\). All triples in \(\mathcal N\cup\{B_2,B_3\}\) intersect. When the direction-1 witness is from \(\mathcal X\), the preceding forced triples likewise cover every pair of the other witnesses. Repeated witnesses need only the pairwise property in \(\mathcal R\). Thus the lower maxima sum to at most zero, and (1) on \(\mathcal R\) proves the claimed common intersection.

### 3c. Neither condition holds

As \(A\) is not lower-extremal for \(\mathcal P\), we have \(l_i(A)\le L_i(\mathcal R)\) for each \(i\). Each extremal witness \(B_i\) of \(\mathcal R\) meets \(A\), which implies \(u_i(A)\ge L_i(\mathcal R)\). Thus each \(L_i(\mathcal R)\) belongs to all projection intervals in coordinate \(i\), and \(\mathcal F\) is coordinate-overlapping and lower-obstructed. Apply (4,3) to the four distinct members \(A,B_1,B_2,B_3\). As the witness triple is empty, \(A\) meets two witnesses \(B_j,B_k\) together. If \(i\) is the remaining coordinate, their intersection requires \(l_i(A)\le q_i=-L_j(\mathcal R)-L_k(\mathcal R)\). Hence \(A\) may be added to the canonical cluster \(\mathcal R_i\): the resulting lower maxima are still at most \(q_i,L_j(\mathcal R),L_k(\mathcal R)\) in coordinates \(i,j,k\), and those sum to zero. All three groups therefore intersect by (1).

This completes the upper bound.

## 4. Explicit sharpness in proper hexagons

Use the affine plane \(\sum_i y_i=2\). Let \(P\) be the nine vectors \(e_i\) and \(c_{ij}=\frac34e_i+\frac14e_j\) for \(i\ne j\), in the affine plane \(\sum_i c_i=1\). Define the triangles \(T_c=\{y:\sum_i y_i=2,\ y_i\ge c_i\text{ for all }i\}\) for \(c\in P\). A subfamily intersects precisely when the sum of coordinatewise maxima of its parameter vectors is at most 2.

Any two intersect, since both are nonnegative vectors of sum 1 and their coordinatewise maximum is bounded by their sum. To prove (4,3), assign every parameter to its unique dominant coordinate \(i\). Some two of any four have the same dominant coordinate. If both are the offset parameters of class \(i\), their maximum in that coordinate is \(3/4\), and for any third vector of a different class the two other maxima are at most 1 and \(1/4\). A third vector in class \(i\) also gives sum at most \(1+1/4+1/4\). If the pair is \(e_i,c_{ij}\), the only third vector that can give sum greater than 2 is \(e_k\) for the third coordinate \(k\): this follows by checking whether its dominant coordinate is \(i,j,k\); in the last case either it is \(e_k\) or its dominant entry is \(3/4\) and other coordinates at most \(1/4\). There are two distinct candidates for the third vector, so at least one yields a meeting triple.

If two points pierced all triangles, one point would pierce \(T_{e_i},T_{e_j}\) for distinct \(i,j\), forcing its coordinates to be \(y_i=y_j=1,y_k=0\). Such a point misses the three triangles with parameters \(e_k,c_{ik},c_{jk}\); their maxima sum is \(1+3/4+3/4>2\), contradiction.

Replace each triangle by the box section
\[
 H_c=\{y:\sum_i y_i=2,\ c_i-1/32\le y_i\le c_i+1+1/32\ (1\le i\le3)\}.
\]
All \(H_c\) are translates of the same proper hexagon. Each contains its original triangle, since in \(T_c\) every coordinate is at most \(c_i+1\). Before imposing the upper cuts, lowering all three lower bounds by \(1/32\) gives a triangle whose extreme value in coordinate \(i\) is \(c_i+1+2/32\). The upper cut removes a small corner at each of its three vertices; the cuts are disjoint because two upper constraints cannot simultaneously bind or be exceeded in this expanded triangle (in that case their sum with the third lower bound is at least \(3+1/32>2\)). Thus each original edge persists, and all three new edges are nonzero. For any originally empty subfamily the lower sum was at least \(2+1/4\), since all \(c_i\) are multiples of \(1/4\); the new lower sum is still at least \(2+1/4-3/32>2\). The entire nerve and thus the piercing number are unchanged. These proper hexagons give the exact lower bound 3 for the wider class.

## 5. Proof technique and scope

The two features are the one-sign feasibility reduction in a codimension-one box section and the three extremal-witness clusters. The latter give a short independent proof for the pairwise-intersecting triangle case and handle the general star-disjointness case by switching which pairwise subfamily supplies the extrema. The upper proof is self-contained apart from planar Helly's theorem; the triangle paper supplies historical attribution and the basis of the sharpness example.

The argument does not apply to arbitrary polygons with four directions; their box coordinates involve two independent linear constraints, and separate positive-circuit obstructions can coexist. It makes no claim about arbitrary (4,3) families.

The companion `verify_three_direction_piercing.js` checks the complete nerve of the nine rational examples, the 126 four-member tests, and the exact piercing number with integer arithmetic.
