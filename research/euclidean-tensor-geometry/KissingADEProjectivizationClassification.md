# One-sided completion for every punctured ADE root equator

**Question.** Fix a finite, reduced, simply-laced crystallographic root system $R$ spanning a Euclidean space $V$, with roots of squared length two. Delete an arbitrary subset $M$ of its **signed** roots. Exactly when can *every* kissing code compatible with the remaining equator be doubled on either side without creating a pair whose scalar product is less than $-1$?

Here is a complete forbidden-subset classification, with no bound on the number of deletions. It classifies this local completion operation, **not** the unrestricted kissing number. In the exceptional types there are only two minimal ways for an extra point to reach the equator, up to root-system isometry. In $E_6$ there is one further nonopposite obstruction that never reaches the equator: two positive-height points already make an angle greater than $120^\circ$.

Write $P(M)=\{v\in V:v\cdot r\le1\ (r\in R\setminus M)\}$. A feasible lift is $(v,h)$ with $v\in P(M)$ and $\|v\|^2+h^2=2$. The precise property is that **any two feasible lifts in the same closed hemisphere have scalar product at least $-1$**. We call such an $M$ *good*. The upper bound $+1$ for a pair of distinct chosen points is the prior kissing condition. The test requires no preexisting symmetry of the outsiders. A strict counterexample in a closed hemisphere gives one in an open hemisphere by slightly shrinking the horizontal parts of any points at height zero.

## Classification

All subsets in the table are forbidden **up to the full root-system isometry group**. Root multiplicities and signs are not discarded.

| Irreducible equator | Exactly the inclusion-minimal bad subsets |
|---|---|
| $A_1$ | Both signs of its only root. |
| $A_2$ through $A_5$ | An opposite pair; or two different arrows $e_i-e_j$ with a common head or with a common tail. |
| $A_r$, $r\ge6$ | The empty set already fails. |
| $D_4,D_5,D_6$ | An opposite pair; a coherent triangle; or a coherent star with $\min(4,n-1)$ leaves in rank $n$. See [the elementary D-type classification](KissingDnProjectivizationObstructions.md) for signs and witnesses. |
| $D_r$, $r\ge7$ | The empty set already fails. |
| $E_6$ | An opposite pair and exactly three more orbits, of sizes **5, 6, 8** as subsets. |
| $E_7$ | An opposite pair and exactly two more orbits, of subset sizes **6, 8**. |
| $E_8$ | An opposite pair and exactly two more orbits, of subset sizes **8, 12**. |

**Reducible equators.** Every **nonempty** omission set fails. With no omissions, take the sum of the squared polar circumradii of the irreducible components. The intact equator is good exactly if this sum is at most $3/2$. The individual values are $\lfloor k^2/4\rfloor/k$ for $A_{k-1}$, $\max(1,n/4)$ for $D_n$, and $4/3,3/2,1$ for $E_6,E_7,E_8$, respectively. In particular the rule covers all ranks and all orthogonal direct sums.

### Specifying the exceptional subsets

Use a chain of simple-root indices $0,1,\ldots,n-2$ and the extra edge $2$ to $n-1$. A digit string denotes **coefficients in the simple-root basis**. For a positive root $a$, $\uparrow a$ means all positive roots coefficientwise at least $a$. For each exceptional type the first two rows below are *exactly* the minimal omission sets permitting a feasible **nonroot point on the equator**, irrespective of whether other opposite roots are missing.

| Type | Representative | Size | Number of distinct labelled subsets in its orbit |
|---|---|---:|---:|
| $E_6$ | $\uparrow012211$ | 5 | 432 |
| $E_6$ | $\uparrow112111$ | 6 | 6,480 |
| $E_6$ | the eight-root set below | 8 | 2,160 |
| $E_7$ | $\uparrow1232112$ | 6 | 4,032 |
| $E_7$ | $\uparrow1222211$ | 8 | 30,240 |
| $E_8$ | $\uparrow13543213$ | 8 | 17,280 |
| $E_8$ | $\uparrow23432212$ | 12 | 181,440 |

The eight roots, with a minus applying to the whole following root, are

`−122111, −112111, −111111, −111110, 112211, 122211, 123211, 123212`.

For a concrete interior witness, the **simple scalar products** of the two projections are $(1/2,0,0,1/2,0,0)$ and $(-1,0,0,1/2,-1,0)$. Both squared lengths are $11/6$; their horizontal dot is $-4/3$. At the common height $1/\sqrt6$ their lifted dot is $-7/6$. They violate precisely the listed eight constraints in union. There is nevertheless no feasible nonroot equatorial point for these eight omissions.

**Scope relative to earlier results.** The projective cap and Weyl-chamber techniques, and root ideals encoding faces of intact root polytopes, are not new; see [Cellini–Marietti](https://arxiv.org/abs/1203.0756). [Novgorodtsev](https://www.preprints.org/manuscript/202610.0335) treats complete cross sections in kissing configurations. The [previous puncture-hull result](KissingE6PunctureHull.md) covers at most three $E_6$ omissions; the hull identity itself fails already for some four-sets, whereas the completion criterion need not fail. The [previous $E_6$ blocker spectrum](KissingE6ExactBlockerSpectrum.md) describes all exact equatorial masks, and [exceptional cap extrema](KissingE7E8AllCapAngles.md) already give extremal sizes, not the new off-equator compatibility classification. The [D-type case](KissingDnProjectivizationObstructions.md) is reused, not counted as a new D-type result here.

## Elementary parts of the proof

Two observations are useful in any type. If $x$ is a feasible nonroot equatorial point, $\|x\|^2=2$, then $|x\cdot r|<2$ for every root. Hence $w=-a x$ lies in the *intact* polar for some $1/2<a<1$ sufficiently close to $1/2$. Its positive lift has dot $-2a<-1$ with $(x,0)$. In particular any horizontal polar protrusion outside the sphere is fatal: shrink an exterior point slightly towards the origin to obtain strict inequalities while staying outside, perturb off the finitely many root rays, then project radially to the sphere. An opposite omitted pair fails using those two roots themselves.

If a bounded polar (or chamber piece) has only vertices of squared norm at most two, the hemisphere height $H(v)=\sqrt{2-\|v\|^2}$ is nonnegative and concave there. The lifted product of two convex combinations is at least the product-weighted average of the lifted vertex products. Vertices of squared norm at most $3/2$ are mutually compatible by Cauchy–Schwarz. A root vertex can be incompatible only if the opposite root constraint is absent, since a root vertex necessarily violates its own constraint.

**Type A.** Use the sum-zero subspace of $\mathbb R^k$, with $R=\{e_i-e_j:i\ne j\}$. The intact polar is the projection of $[0,1]^k$, with squared radius $\max_j j(k-j)/k$. If an intact centrally symmetric polar has squared radius larger than $3/2$, choose an opposite horizontal pair with equal squared lengths in $(3/2,2]$; the same-height lifts have product below $-1$. This explains the cutoff $k\ge7$. In rank one, when one sign of $r$ is missing, write $v=t r$ with $-1/2\le t\le1$; the products are bounded below even before adding height.

For $3\le k\le6$, two arrows out of the same vertex allow the vector obtained by centering $(1,-1,-1,0,\ldots)$; only those two inequalities are violated, and its squared norm is $3-1/k>2$. Reverse signs for two incoming arrows. Conversely, suppose each head and each tail occurs at most once in $M$ and no opposite pair occurs. Every missing arrow has a retained two-step path through any third index, so $P(M)$ has coordinate spread at most two. At a vertex the tight coordinate differences $v_i-v_j=1$ form a connected graph: otherwise the components admit a nonzero shift preserving the zero sum. Thus the coordinate differences are integral. A spread-two vertex has a unique maximum and a unique minimum, since every max-to-min arrow must be missing. All other coordinates are at the middle level, so the centered vertex is precisely a missing root. All remaining vertices are in the intact polar. The height and concavity bounds above prove sufficiency.

**Reducible case.** For the intact product, squared polar radii add; the opposite-horizontal-pair test and the height bound give the criterion. The D-type radius follows from $|v_i|+|v_j|\le1$: if $a=\max |v_i|\ge1/2$, maximize $a^2+(n-1)(1-a)^2$ on $[1/2,1]$ at an endpoint; both extremal candidates are attained. The exceptional radii are independently checked in the replay. If $r$ is missing in one component and $u$ is a unit direction in another, then

$
x=(\sqrt{1-\epsilon^2/2}\,r,\epsilon u,0,\ldots)
$

is a feasible nonroot equatorial point for all sufficiently small $\epsilon>0$. Distinct roots in the first component have dot at most one, and the other component constraints hold by smallness. Apply the nonroot-equator observation.

## Exact finite proof in the exceptional cases

The [standalone Python verifier](verify-kissing-ade-projectivization.py) uses only the standard library, rational Gaussian elimination, integer comparisons, and finite graph traversals. No precomputed Weyl tables, numerical optimizer, or external cases are inputs.

1. **Chambers and pruning.** Generate the roots by the simple reflections from the Cartan matrix $G$. Move a horizontal vector to the dominant chamber, writing $y_i=v\cdot\alpha_i\ge0$. Its actual violation set is an upper ideal $I$ in the positive-root order. The chamber polyhedron from removing the constraints in $I$ is simply $y\ge0$ and $a\cdot y\le1$ for the maximal roots $a$ outside $I$; no lower inequalities are necessary. Its squared norm is $y^T G^{-1}y$. Enumerate its vertices by support: a vertex with $k$ nonzero coordinates has $k$ independent tight upper equations on those coordinates. An unbounded coordinate, an exterior vertex, or a nonroot sphere vertex makes $I$ a genuine escape obstruction by the preceding observations. Stop that branch. Otherwise store all chamber vertices and grow $I$ by each maximal remaining root. This is exhaustive because every upper ideal is built from the empty ideal in this way. The escape-obstruction list consists exactly of the orbit-upward closure of the stopped masks: if an equatorial nonroot had its actual ideal in an unstopped chamber piece, strict convexity at the sphere would make it a norm-two nonroot vertex, contrary to the test.

2. **Which vertex pairs fail?** If $M$ contains no stopped mask in any orientation, every feasible projection is in the convex hull of chamber vertices whose actual violations are contained in $M$, in the corresponding orientation. By concavity it suffices to test pairs of these lifted vertices. Ignore the already settled opposite-root case; if a nonroot pair fails, at least one member $v$ has squared norm $>3/2$. Fix it dominant and vary the second member over the Weyl orbit of a chamber generator $w$. With $d=v\cdot w$ the exact failure test is $d<-1$ and $(d+1)^2>(2-\|v\|^2)(2-\|w\|^2)$. The failing orientations form a connected subgraph containing the antidominant representative whenever nonempty: reflecting at a positive simple product of $w$ cannot increase $d$, because $v$ is dominant; such a sequence reaches its antidominant representative. Breadth-first search starting there and accepting **only failing orientations** is thus exhaustive. Record the union of strictly violated signed roots, excluding unions with opposite roots. Every such union has the concrete pair as a witness. In $E_7,E_8$ none survive this opposite-root test.

3. **Equivalence and minimality.** For each candidate mask, fold the sum of its roots to the dominant chamber. Its Weyl stabilizer there is the standard parabolic subgroup generated by the simple reflections at zero simple products. Enumerate the mask orbit under that subgroup to obtain a canonical representative; also allow the diagram involution in $E_6$. Remove a candidate iff a subset belongs to a previously retained orbit. This proves inclusion-minimality, not merely inequivalence. The verifier checks the surviving representatives against the literal table, and recomputes every labelled count by full orbit traversal.

| Type | Chamber states visited | Unstopped / stopped | Distinct dominant vertices | Failing oriented pairs visited before opposite-root filtering | Distinct new masks after that filtering, before conjugacy |
|---|---:|---:|---:|---:|---:|
| $E_6$ | 12 | 7 / 5 | 12 | 210 | 4 |
| $E_7$ | 13 | 9 / 4 | 15 | 4,151 | 0 |
| $E_8$ | 19 | 13 / 6 | 20 | 24,106 | 0 |

As one consequence directly relevant to dimension seven, a kissing code containing exactly **68 of the 72** signed roots of an $E_6$ equator and missing no opposite pair has at most **128 points**. The 32 fully paired axes and all outsiders from one hemisphere are projectively compatible, with no equatorial outsiders. They cannot attain [Anstreicher's sharp 63-line equality case](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf): each missing root has ten decompositions as the sum of two roots of product $-1$ on disjoint pairs of axes, and at most three further missing axes can block these, as in the [puncture-hull argument](KissingE6PunctureHull.md). Reflection inside an equality root system would restore a missing axis that is not among the selected lines. Thus there are at most $62-32=30$ outsiders on each side, giving $68+2\cdot30=128$. The local criterion is exact; this derived kissing upper bound need not be sharp.
