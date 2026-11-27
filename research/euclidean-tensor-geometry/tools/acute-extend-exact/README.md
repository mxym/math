# Exact one-point extension for acute sets

Given a finite rational acute set \(A\subset\mathbb Q^d\) of at least two points, the accompanying standard-library program [acute-extend-exact.py](acute-extend-exact.py) decides whether some point can be added in the same ambient space. On success it gives rational coordinates that pass exact angle tests. On failure it computes an exact maximum slack of zero, proving the particular input set is inclusion-maximal, not globally maximum. Use `python acute-extend-exact.py < points.json`; input is a JSON list of \(d\)-vectors with exact integers/decimals or quoted rational fractions. The algorithm is for small-dimensional, small-cardinality input; it does not solve the global acute-set problem.

## Reduction

For each unordered pair \(a,b\in A\), let \(u=b-a\). The angles at \(a,b\) in triangle \(a,b,x\) are acute precisely in the open strip \(u\cdot a<u\cdot x<u\cdot b\). Define \(Q\) by the closed versions of all these strip tests. The angle at \(x\) is acute precisely when \(q_{ab}(x)=(x-a)\cdot(x-b)>0\). The old centroid \(m\) lies strictly inside all strip inequalities, since every old site lies in each closed strip and \(a,b\) occupy its two different faces. Thus there is an extension if and only if some \(x\in Q\) has all \(q_{ab}(x)>0\): move any such \(x\) slightly towards \(m\) if some strip inequalities are tight, without losing positivity.

If the affine span of \(A\) is proper, choose a nonzero rational \(u\) perpendicular to every old difference and use \(x=m+t u\) for sufficiently large rational \(t\). All strip tests are unaffected, and every \(q_{ab}\) increases by \(t^2\|u\|^2\). For full affine span, \(Q\) is bounded by strips anchored at an old point with linearly independent directions. Translate to put this anchor at zero.

The common quadratic term of all \(q_{ab}\) gives an exact polytope formulation:
\[
\max_{x\in Q}\min_{a,b}q_{ab}(x)
  =\max_{(x,z)\in P}(\|x\|^2-z),\qquad
P=\{(x,z):x\in Q,\ (a+b)\cdot x-a\cdot b\le z\le M
                      \text{ for all }a,b\}.
\]
Choose \(M\) greater than the maximum absolute value of every displayed affine form on the anchored-strip parallelepiped (rowwise \(\ell_1\) bounds suffice). Therefore \(P\) is bounded; the minimum feasible \(z\) for a given \(x\) is the maximum of the affine forms, and the equality follows. The right-hand objective is convex, so its maximum is attained at a vertex of \(P\). All vertices are rational; positivity is an exact finite computation. This is equivalent to taking maximizers of a convex quadratic on the cells associated with the lowest ball slack, but the single lifted polytope avoids separate cell construction.

## Exact enumeration

The initial product of the anchored-strip parallelepiped with \([-M,M]\) has \(2^{d+1}\) explicitly known rational vertices. Add the remaining inequalities one at a time. A new vertex must be an old surviving vertex or the crossing of the new hyperplane and an old edge. At any stage two distinct vertices span an edge precisely when the face cut out by their common tight inequalities has no third vertex; that face is the minimal face containing the two and a compact face is the convex hull of its vertices. The implementation stores tight inequalities as bit masks. The exact intersection of crossing endpoints retains their shared mask and sets the new inequality's bit. This argument also covers degeneracies; no floating-point hull computation is used. On success, the program moves toward the centroid by dyadic fractions until all ball slacks are positive, then checks all new angles exactly.

## Reproduced case

For the following nine-point \(\mathbb R^4\) seed, the exact maximum slack is zero across 1240 lifted vertices, so no tenth point can be added while keeping these nine fixed. Dividing all coordinates by 1000 is immaterial. This is a test of the algorithm and not a new numerical lower or upper bound for \(f(4)\).

~~~json
[[-519,-569,-679,68],[-706,-581,338,369],[-517,571,-610,-83],
 [-639,447,421,-486],[435,-597,-317,-533],[371,-637,614,69],
 [672,503,-423,29],[433,512,622,121],[-10,87,-106,1167]]
~~~

Harangi's [Acute Sets in Euclidean Spaces](https://doi.org/10.1137/100808095), §4, gives special-seed algebraic extension conditions and uses computational extension from a particular prefix. The tool above instead decides a one-point extension for an arbitrary prescribed rational input by vertex enumeration; no novelty or priority claim is made.

## Tests

Run `python test-acute-extend-exact.py` from this directory. The smoke test executes the CLI in subprocesses for two extendable cases, one maximal seed, and four invalid inputs. It checks new angles with exact rational arithmetic.
