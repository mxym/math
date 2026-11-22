# Reconstruction from the graph on 51 vertices outside a square

A Conway graph exists if and only if some simple graph on 51 vertices passes the reconstruction below. Its input is just exterior adjacency in arbitrary vertex order. Every candidate has 173, 174 or 175 edges, vertex degrees between six and ten, and eigenvalue three with multiplicity at least ten. The input graphs satisfying the necessary tests still require a search.

## The boundary and its four caps

Choose an induced square with four roots in cyclic order. The third vertex on each square edge is its cap. These four sites are distinct. The two common neighbors of opposite roots already belong to the square. Hence a site outside the square can see two roots only when it is their cap. Each root has ten ordinary neighbors that see just that root. The boundary thus consists of four caps and forty ordinary sites. There are 51 sites outside these closed neighborhoods.

Write $h$ for the number of adjacent opposite-cap pairs. Caps on adjacent sides cannot be adjacent because their common square root already pairs them separately with their other respective roots in its neighborhood. A cap sees either its opposite cap or one ordinary site at each of the two roots not incident to it. This follows by counting its two common neighbors with each such root. It has eleven exterior neighbors in the first case and ten in the second. An ordinary site has one mate at its own root, needs one further common neighbor with each adjacent root, and needs two with the opposite root. Each neighboring cap counts twice in these last requirements. It therefore has $8+c'$ exterior neighbors where $c'$ is its number of neighboring caps, between zero and two.

For an exterior point $z$, put $c_z$ equal to the number of caps it sees. Each root must have two common neighbors with $z$, so $z$ has $8-c_z$ neighbors in the boundary and exterior degree $6+c_z$. Consequently
$$\sum_z c_z=40+2h,\qquad |E(F)|=173+h.$$
Let $l_1,l_2$ be the marked length-two path counts for the two diagonals as in the [two-star count](two-star-cover.md). Two caps on adjacent sides share their corner and can share at most one ordinary site, detected by a length-two path at that corner. Opposite caps have no common boundary site or square root. Counting all six cap pairs gives
$$\sum_z {c_z\choose 2}=8-h-l_1-l_2.$$
If $h>0$ then $l_1=l_2=0$, since at either diagonal a mark on each side has already spent its single cross edge. For $h=2$, no ordinary site sees any cap and each cap sees its opposite one. The boundary/exterior common-neighbor equation summed over the caps gives $Fc=8\mathbf1-2c$, where $F$ is the 51-site adjacency matrix. In particular $(F^2-4F-20I)\mathbf1=0$ in this case.

The adjacency of the full graph has eigenvalue three of multiplicity 54, from the graph equation and its trace. Each such eigenvector obeys four independent local equations at the square roots, supported entirely on the 48-site shell. They are independent because each root has private ordinary neighbors. Restriction to the shell therefore has rank at most 44, leaving at least ten eigenvectors supported on the 51 exterior sites. Their restrictions give the stated multiplicity for $F$. The eigenvalue bound on the centered space of the full graph also shows that $F$ has at most one eigenvalue above three.

## Recovering contacts without their labels

The 44-by-51 boundary contact matrix $B$ has binary entries and is initially unknown. Squaring the full adjacency on the exterior gives its entire Gram
$$K=B^tB=12I+2J-F-F^2.$$
Let $V$ be the 44-by-4 boundary incidence matrix with the four roots. It has one entry on each ordinary row and two on a cap row. Since $V^t B=2J$, its three column differences are independent elements of the left kernel of $B$. Thus $K$ has rank at most 41. Each boundary row has weight from eight to eleven; two different rows cannot coincide since they could have at most two common neighbors.

The rows can be enumerated directly from $K$. Their supports have positive mutual entries in $K$ and induce maximum degree one in $F$, since every vertex neighborhood is a matching. They lie in the rational image of $K$. For an efficient exact superset, replace a rational row basis by an integer basis of the same span that is independent modulo two. If a new integer row is dependent modulo two on earlier rows, add its modular dependence and divide by two. Every such operation divides the absolute value of any fixed nonzero maximal minor of the current independent rational rows by two. Reduction therefore terminates. The final basis has an odd maximal minor. Every integer vector in its rational span has coefficients of odd denominator on this basis, so its reduction belongs to the resulting binary code.

Intersect the code with a proposed support by setting the other coordinates to zero. Once the dimension is small, enumerate all its binary words. Otherwise select the next least support position and restrict further to sites compatible with it in $K$. This enumerates every admissible row. Select 44 distinct candidate rows whose outer products sum exactly to $K$. Every such selection is tested by integer matrix multiplication.

## Recovering the square and its boundary edges

For the chosen $B$, find the binary vectors $v$ satisfying $v^tB=2\mathbf1^t$ and having weight twelve. Choose four such vectors. Their pairwise intersections on the boundary must be one on adjacent square vertices and zero on opposite ones. Every boundary site must belong to one or two of the four neighborhoods. This reconstructs $V$ and square adjacency $S$. When $B$ has rank 41, the affine solution space has dimension three. The four true neighborhoods span it affinely. On their private ordinary sites the four affine coefficients of a binary solution must themselves be zero or one, so these are the only four binary solutions.

Writing $D$ for boundary adjacency, the remaining linear equations are
$$DB=2J-B-BF,\qquad DV=2J-V(I+S).$$
Enumerate the binary preimages row by row, test their degrees and the zero diagonal, and enforce symmetry. In the rank-41 case there is even at most one real symmetric solution with zero diagonal once the four neighborhoods are known. The difference of two solutions has the form $VHV^t$ with $H$ a symmetric four-by-four matrix killing constants, because its rows and columns belong to the span of the three neighborhood differences. The diagonal at ordinary sites gives $H_{ii}=0$. The diagonal at each cap gives $H_{i,i+1}=0$, and the row sums give opposite entries zero as well. For lower ranks the enumeration still covers every possibility.

Assemble all 99 sites and test $A^2+A=12I+2J$ entry by entry. A true graph passes this construction at any square, and any accepted matrix directly gives a graph with the required parameters.

The [reconstructor](square_exterior.py) performs the binary and rational calculations. Without input it constructs and verifies the known 243-vertex graph of degree 22 and deletes its entire 80-site square neighborhood. Its sole input for reconstruction is the induced graph on the 163 remaining vertices. The algorithm finds exactly 76 candidate boundary rows, four parent neighborhoods, and a unique completion up to labels of the recovered shell. The resulting graph equals the original with every exterior label fixed. Here the contact rank is 72, below the maximum of 73 for that control. For a Conway candidate supply a JSON adjacency matrix as the script argument.

## A single determinant on the 51 vertices for all four lattice ranks

Let $r\in\{36,38,40,42\}$ be the global Seidel rank modulo seven. Form $T=4I_{51}+F$ and the integer
$$\Delta_F=28\det(T)-3\det(T+J).$$
Two requirements on the given exterior alone are
$$\operatorname{rank}_{\mathbb F_7}(25T-3J)\le r-4,
\qquad \Delta_F=7^{55-r}m^2\quad\text{for some }m\in\mathbb Z.$$
In particular the 51-site matrix has nullity at least thirteen modulo seven. The square and divisibility requirement allows zero, and the rank bound still applies in that case.

For the proof take $G=3I-A+J/9$, seven times the rank-44 orthogonal projector of the full graph. Its complementary projector scaled by seven is $H=4I+A-J/9$. Let $W$ consist of the 44 boundary sites, and $Z$ consist of the square plus its 51 exterior sites. The sizes 44 and 55 are exactly the ranks of the two projectors. Complete orthonormal column bases for the two spaces to one orthogonal matrix. The complementary minors of that matrix agree up to sign by the inverse-minor formula. Squaring shows
$$\det H_{ZZ}=7^{11}\det G_{WW}.$$
This identity includes zero minors. By the [determinant-49 marked lattice](../maximal-marked-lattice/README.md) the underlying rational 44-space has square discriminant, so $\det G_{WW}$ is a rational square. Moreover $9\det G_{WW}$ is integral by expanding the rank-one update $G_{WW}=3I-D+J/9$ in its columns. Thus $9\det G_{WW}$ is an integer square.

On $Z$ the induced adjacency is exactly $C_4\oplus F$. The four-root block $4I+C_4-J_4/9$ has eigenvalues $50/9,4,4,2$, determinant $1600/9$, and is invertible modulo seven. Its Schur complement in $H_{ZZ}$ is $T-3J/25$. The determinant of this complement is $\Delta_F/25$ by the rank-one determinant identity. Hence
$$64\Delta_F=7^{11}\big(9\det G_{WW}\big).$$
Since $\Delta_F$ is integral, it equals $7^{11}$ times an integer square. Modulo seven, $9H=-9G$ equals the Seidel matrix $2A-J+I$. The Schur complement rank is at most $r-4$. In particular its determinant, multiplied by the 7-adic unit 25 to give $\Delta_F$, is divisible by $7^{51-(r-4)}$. Combining with its square class proves the claim. The reconstructor checks both conditions before recovering boundary contacts.
