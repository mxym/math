# Equal populations in eight charged classes on a rank-42 three-type face

Suppose the graph has seven-rank 42 and **only** $N_{18},U_{1,21},U_{1,25}$ among the twelve selected signed-unit families may occur. Then the positive-charge $G_{1,21}=U_{1,21}$ population in each of the eight signed residues of its norm is the **same integer between 9 and 15**. Every signed norm-18 class contains at least 18 fields, and the populations on perpendicular directions agree. The total $N_{18}$ is divisible by four and at most 260. This is a necessary configuration, not an exclusion.

Use literal global raw populations $G_{a,t}$; $N_t=G_{0,t}$ counts both signs. For nonisotropic species write $W_{a,t}=G_{a,t}/8$. For each opposite-residue pair $i=\{\beta,-\beta\}$ let $X_i=(G_{a,t}(\beta)+G_{a,t}(-\beta))/2$ and $v_i=X_i-W_{a,t}$. Such half sums are integers for neutral species and may be half integers for charged species. No vertex symmetry is assumed.

**The angular equations.** Use the norm-four rank-48 quadratic harmonic identity on each of the four standard auxiliary gluings and all sixteen discriminant-plane isometries, as in [the two-type projective-balance calculation](two-type-residue-balance.md). On this face $G_{0,26}=8G_{1,21}$ and $G_{1,27}=9N_{18}$. These substitutions hold per opposite-residue pair: adding a graph column changes no seven-class. For the first, each of the five positive sites of a $(1,21)$ gives a norm-26 difference with negative doubled pivot. Counting both orientations and subtracting the doubly counted orientations from its unique positive edge gives $2\cdot5-2=8$. The norm-18 translation counts its nine negative pivots. There is no independent $U_{0,26}$ or $U_{1,27}$ term, and $U_{2,26}=0$. The other raw species removed (besides universal subminimum/impossible costs) are $(0,16),(0,20),(0,24),(2,26),(2,28),(2,30),(3,37)$. Average each equation with the equation obtained from the negative isometry, so only opposite-residue half sums occur. Subtract its full isometry average: zero-class terms cancel and deviations sum to zero on each norm circle. The companion rank42_u121_residues.py generates these rational equations; it does not assume balance.

In lexicographic order on the circle representatives, the $(1,21)$ deviations are $(x,-x,y,-y)$ and the $(4,44)$ deviations are $(-349x,349x,-349y,349y)/62$. Differences of **literal opposite-pair populations** are integers, so $4x,4y$ and $349(4x)/62,349(4y)/62$ are integral. Hence each of $4x,4y$ is divisible by 62. If either is nonzero, nonnegativity forces $W_{4,44}\ge349/4$, hence $G_{4,44}\ge698$.

**Independent site bounds.** The companion rank42_u121_site_bounds.py uses the existing original-site chart with no projective equalities assumed. Its five nonnegative identities give
$$
 G_{4,44}\le600,\qquad129\le2G_{1,21}\le254,\qquad
 18N_{18}-G_{1,25}\ge2466,\qquad N_{18}\le261.
$$
Its auxiliary $S=W_{1,23}-99-7W_{0,14}\ge0$ counts the nonstandard unit fields after removing the ordinary 99 marks and the Fano translates. Thus $x=y=0$.

**Separate the two signs for charge one.** For $b\in G_{1,21}$ the positive and negative sets $P,N$ have sizes 5,16. At this cost no coordinate has absolute value at least two: translating a doubled site by its graph column gives a subminimum neutral or charge-two cost. From $Ab=-4b-2\mathbf1$ one gets $e(P)=1+e(N)$ and $d_P(i)=2+d_N(i)$ for $i\in N$. The positive pair slots give
$$
 16+4e(N)\le\sum_{i\in N}\binom{d_P(i)}2\le20-e(P).
$$
Thus $N$ is independent and $P$ has a unique edge $pq$. Reflection $b'=d_p+d_q-b$ has the same charge and cost 21: $\|d_p+d_q\|^2=36$ and $b\cdot(d_p+d_q)=18$. At $p,q$ both resulting entries equal 1, so the same edge is used in the reverse reflection. Graph columns have zero seven-class, so this involution exchanges the two opposite signed classes. The global mass bounds give 9 to 15 per signed class.

With $x=y=0$, the $(0,18)$ deviations are $(-z,z,z,-z)/18$ and the $(1,25)$ deviations are $(z,-z,-z,z)$ for the same parameter. The norm-18 representatives are $(2,3),(2,4),(3,2),(3,5)$; the identified pairs are perpendicular. Since $|z|\le W_{1,25}=G_{1,25}/8$, each signed norm-18 class population is at least $(18N_{18}-G_{1,25})/144\ge137/8$, hence at least 18. Their total is four times the sum of the two per-signed-class values.

In particular there are at least 18 distinct positive edges missing every Hoffman coclique: the eight signed classes supply at least 72 total (1,21) fields, while the [physical-edge cap](cost21-cycle-edge-cap.md) permits four fields per edge under these same shell absences.

Replay [the residue checker](rank42_u121_residues.py) and [the site checker](rank42_u121_site_bounds.py), using SymPy and, for the latter, original_site_populations.py and its dependencies in this directory.
