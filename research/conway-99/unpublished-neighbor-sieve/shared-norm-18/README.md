# Screening two overlapping norm-18 supports

The [exact overlap proof and global counting consequences](exclusion.md) and the [higher-degree identity](higher-moments.md) supersede the preliminary screen below. The degree enumeration reconstructs the two input families, and integer certificates or independently verified DRAT proofs exclude every one of the 6,065 cores.

The [three-label exclusion](panel-heights.md#the-three-label-exclusion-and-the-rank-38-contradiction) rules out the rank-38 alternative with just norm-18 and norm-24 markings. Ranks 36 and 38 both need at least three of the twelve selected unit types. Whenever norms 16 and 20 are absent, all four ranks satisfy $N_{18}\le16,166$. At rank 36, [exactly three types including norm 18 would require at least 694,558 distinct 26-site supports](panel-heights.md#a-rank-36-consequence-if-norm-18-occurs). The [height-three theorem and norm-36 injection](height-three.md) hold at every rank.

In the remaining two-type case at ranks 40 and 42, [a residue count and a dimension bound](two-type-overlap-matching.md) force eight pairs of distinct norm-18 supports with six or seven common sites per pair. All sixteen supports are different.

The [short-population identity](two-type-short-counts.md) leaves ten integer tuples in the two-type case. Each extension has one or three eligible 22-cocliques and 400 to 448 eligible oriented norm-18 labels.

## Rank 36 requires at least four selected types

The [Fano square packing and original graph-lattice identity](rank36-four-types.md) force a neutral label of norm 16, 18 or 20 at rank 36. This excludes the final three-type alternative. At every rank, absence of norm 20 implies at most 198 oriented norm-14 labels. The [standard-library checker](rank36_four_types.py) verifies the identity and bounds.

## Nine earlier rank-36 three-type exclusions

The [charge-one packing bound and exact moment identities](affine-triples.md) rule out the alternative consisting of norm 24 and the unit types `(1,21)` and `(3,37)`. A [two-cycle packing bound](rank36-two-cycle.md) rules out the alternative consisting of norm 24, unit norm 26, and type `(1,21)`. A [combined short and scalar moment argument](rank36-third-triple.md) rules out unit norm 26 together with types `(1,25)` and `(1,27)`. A [coclique packing and moment argument](rank36-coclique-tangent.md) rules out norm 18, norm 24, and unit norm 26, the only surviving exactly-three-type alternative with norm 18. A [Sidon bound on compatible cocliques](coclique-sidon-cut.md) rules out norm 24, unit norm 26, and unit type `(1,27)`. A [degree-ten graph-site harmonic certificate](site-degree-ten.md) rules out norm 24 with unit types `(1,27)` and `(3,37)`. A [primal and extension calculation](rank36-primal-local-cuts.md) excludes two more alternatives, and a [graph-wide coclique packing calculation](rank36-primal-global-sidon-cut.md) excludes a third. These nine exclusions left one of the 220 exactly-three-type alternatives at rank 36: unit norm 26 together with types `(2,28)` and `(2,30)`. This does not exclude rank 36 itself or cases with more than three types. Run `python3 rank36_affine_triples.py`, `python3 rank36-third-triple.py`, `python3 rank36-coclique-tangent.py`, `python3 coclique_sidon_cut.py`, `python3 site_degree_ten.py`, and `python3 rank36_primal_sidon.py` to replay the exact identities with python-flint.

Without any three-type assumption, the [unconditional four-family bound](coclique-sidon-global.md) forces at least one of neutral norms 18 or 20, or the unit types `(2,30)` or `(3,37)`, at every remaining rank.

The [unconditional degree-ten site inequality](site-degree-ten-global.md) gives a second all-rank population constraint. In particular it rules out a graph whose selected units are confined to norm 24 and the types `(1,27)`, `(2,28)`, `(3,37)`.

[Global coclique Sidon packing](global-coclique-sidon.md) makes no assumption on residue-class compatibility: among all 22-cocliques, an ordered difference determines the pair.

[Fano difference packing](fano-difference-packing.md) makes the norm-14 bounds quantitative in terms of norms 20 and 24, with no rank restriction.

The [49 rank-36 support constraints](rank36-four-hit-sets.md) apply at every support size. They and two exact support implications leave at most 16 of the 495 four-type possibilities. Each of those 16 has a rational control for the specified relaxation, not a graph.

[Fano palette transports](rank36-four-fano-palette-cut.md) exclude three of those 16 supports; at most 13 four-type supports remain at rank 36. The old rational controls do not impose the new transport inequalities.

For rank 38, [27 exact support constraints](rank38-three-hit-sets.md) and the norm-16 support implication leave at most 15 of the 220 exactly-three-type supports. All 15 have controls for the stated relaxation, not for graph existence.

In the two-type case at ranks 40 and 42, [unaveraged residue balance](two-type-residue-balance.md) forces a compatible Hoffman coclique, at least 400 eligible norm-18 markings in every maximal extension, and at least 42 disjoint intersecting-support pairs there (at least 2,075 total distinct pairs in the rank-40 graph).

An [orthogonal-Fano transport](rank36-four-orthogonal-cut.md) excludes one more rank-36 four-type support, leaving at most 12 of 495.

The [Fano endpoint and triangle-free bound](rank36-four-endpoint-cut.md) excludes another rank-36 four-type support, leaving at most eleven.

The [original graph-site quartic](original-site-quartic.md) supplies two weight-26 identities at every remaining rank and a numerical lower bound from actual original-class marks, rather than counts averaged over extensions.

[Original graph-site populations](original-site-populations.md) exclude three more exactly-four-type supports at rank 36 and two exactly-three-type supports at rank 38, leaving at most eight and thirteen respectively. These counts apply only to the named support sizes.

A [Fano orthogonality cap](original-site-fano-four.md) excludes one further exact-four support at rank 36 and two exact-three supports at rank 38; at most seven and eleven respectively remain. This does not bound the ranks with larger support.

For [same-positive unit (1,27) fields](u127-same-positive-matching.md), squared distances 18, 20 and 22 are impossible; pairs at squared distances 16 or 24 form a matching. At distance 24 the common negative graph is a disjoint union of paths on three and four vertices, with 32 necessary local colored cores.

[Endpoint compatibility](two-type-no-fano.md) excludes Fano markings in the two-type case, reducing the short-count list from ten tuples to eight. If an extension has three eligible cocliques, its overlap matching has at least 45 pairs.

The [ternary rank of the Hoffman coclique design](hoffman-ternary-rank.md) is at least 19; if a Fano switch exists, it is exactly 21. The associated six-site restrictions have a residual collision bound, not an exclusion of a full rank.

The [rank-22 Hoffman residual lattice](hoffman-residual-theta.md) gives four exact theta relations and caps of 32 and 74 for oriented norm-18 and norm-24 fields vanishing on a fixed coclique, in each specified maximal ternary extension. They are not caps on all graph labels.

## Reproduce the rank-38 and rank-36 results

Run these commands from this directory in a checkout of the repository. Use Python with NumPy, pynauty, python-flint and python-sat, nauty's `genbg`, and a compiled `drat-trim`. Replace the two executable paths with their local paths.

```sh
python higher_moments.py
python packing.py
python panel_heights.py --genbg /path/to/genbg
python three_label_panels.py --genbg /path/to/genbg --drat-trim /path/to/drat-trim --jobs 4
python rank36_three_types.py
```

The three-label verifier reconstructs 9,106 twelve-edge cores and 1,959 thirteen-edge cores. It checks integer inequalities for 10,110 of them and regenerates and checks DRAT proofs for the other 955. The rank-36 verifier excludes 210 of the 220 possible triples and checks the population bounds for the remaining ten. The [earlier overlap replay](exclusion.md#replay) gives the commands for the supporting exclusions.

## Preliminary screen of November 22

The original experiment tested whether two oriented norm-18 vectors can share a positive root, its four negative neighbors and four designated positive pair labels, with dot product nine. All 6,065 archived inputs failed an exterior-contact test. At that stage the input completeness and the floating-point linear-programming rejections remained to be certified. The [bounds on all four ranks](../short-shell-moments.md) are independent of this experiment.

## Local inputs

The rooted dot-product bound gives squared difference at most 22. The difference has only signed units, so the two markings have no opposite signs. At dot product nine they agree exactly on the nine specified sites. Their difference is another norm-18 vector. The three sets of nine are the common sites and the sites exclusive to each of the two markings. In the common set take the original positive sign first. In each exclusive set take the original negative sign first. Each set then has five sites of its first sign and four of its second sign. The supports of the two vectors and their difference are each 4-regular bipartite graphs on 18 vertices.

Four of the six pair labels are specified. Up to relabeling the four negative neighbors, the two omitted pairs either meet (family 0) or are disjoint (family 1). The exploratory enumeration rooted one support, attached a second along the common nine sites, and filled the two crossing matrices subject to the three support degrees and the upper bounds on common neighbors. Isomorphic 27-vertex inputs were grouped while preserving the six signed parts.

| Omitted pairs | Rooted one-support charts | Gluings before grouping | Archived inputs | Rejected by numerical LP | Rejected by integer SAT |
|---|---:|---:|---:|---:|---:|
| Meet | 434 | 2,463 | 1,578 | 1,550 | 28 |
| Disjoint | 616 | 19,416 | 4,487 | 4,313 | 174 |

The [compressed JSON file](cores.json.gz) contains both input lists, in table order. Each graph is a list of 27 row masks. Bit $j$ of row $i$ means that vertices $i,j$ are adjacent. The groups are consecutive blocks of nine, with the first five sites of each block having its first sign.

The [catalogue reconstruction](enumerate_cores.py) starts with nauty's degree-four bipartite graphs on two sets of nine. It filters both parts by the common-neighbor caps, roots them on both sides and tries all orderings of the four designated neighbors. It then enumerates the crossing matrices and compares the full sets of colored canonical graph certificates against the archive. Run `python enumerate_cores.py --genbg /path/to/genbg` with nauty 2.8.9 and pynauty.

## Exterior-contact test

For each possible exterior site enumerate its contacts with the 27 sites. Its number of first-sign contacts minus its number of second-sign contacts must be equal in the three groups, by the two eigenvector equations. An exterior site cannot supply a further common neighbor for a core pair whose quota is full. For each core vertex the number of contacts in its closed core neighborhood is at most two, using the common-neighbor bound for a pair consisting of that vertex and the exterior site.

The unknowns count exterior sites with each allowed contact set. Their sum is 72. Each core vertex must reach degree 14, and each pair must have exactly one common neighbor when adjacent or two otherwise. First solve these linear equations over nonnegative reals with SciPy. For inputs passing this relaxation, encode nonnegative integer counts and impose the additional bound that at most one exterior site can contain any given triple of contacts. Two such sites would already have three common neighbors. The SAT encoding allows empty contact sets to fill unused places.

From this directory run the following commands with NumPy, SciPy and python-sat installed. The first command checks every archived input. The second exercises the integer stage on one graph.

```sh
python replay.py
python replay.py --family 0 --case 159
```

The contact replay starts from the archived graphs. The [exact replay](exclusion.md#replay) reconstructs the input list directly and certifies both rejection stages.
