# Screening two overlapping norm-18 supports

The [exact overlap proof and global counting consequences](exclusion.md) and the [higher-degree identity](higher-moments.md) supersede the preliminary screen below. The degree enumeration reconstructs the two input families, and integer certificates or independently verified DRAT proofs exclude every one of the 6,065 cores.

The [three-label exclusion](panel-heights.md#the-three-label-exclusion-and-the-rank-38-contradiction) rules out the rank-38 alternative with just norm-18 and norm-24 markings. Ranks 36 and 38 both need at least three of the twelve selected unit types. Whenever norms 16 and 20 are absent, all four ranks satisfy $N_{18}\le16,166$. At rank 36, [exactly three types including norm 18 would require at least 694,558 distinct 26-site supports](panel-heights.md#a-rank-36-consequence-if-norm-18-occurs). The [height-three theorem and norm-36 injection](height-three.md) hold at every rank.

## Rank 36 requires at least four selected types

The [Fano square packing and original graph-lattice identity](rank36-four-types.md) force a neutral label of norm 16, 18 or 20 at rank 36. This excludes the final three-type alternative. At every rank, absence of norm 20 implies at most 198 oriented norm-14 labels. The [standard-library checker](rank36_four_types.py) verifies the identity and bounds.

## Nine earlier rank-36 three-type exclusions

The [charge-one packing bound and exact moment identities](affine-triples.md) rule out the alternative consisting of norm 24 and the unit types `(1,21)` and `(3,37)`. A [two-cycle packing bound](rank36-two-cycle.md) rules out the alternative consisting of norm 24, unit norm 26, and type `(1,21)`. A [combined short and scalar moment argument](rank36-third-triple.md) rules out unit norm 26 together with types `(1,25)` and `(1,27)`. A [coclique packing and moment argument](rank36-coclique-tangent.md) rules out norm 18, norm 24, and unit norm 26, the only surviving exactly-three-type alternative with norm 18. A [Sidon bound on compatible cocliques](coclique-sidon-cut.md) rules out norm 24, unit norm 26, and unit type `(1,27)`. A [degree-ten graph-site harmonic certificate](site-degree-ten.md) rules out norm 24 with unit types `(1,27)` and `(3,37)`. A [primal and extension calculation](rank36-primal-local-cuts.md) excludes two more alternatives, and a [graph-wide coclique packing calculation](rank36-primal-global-sidon-cut.md) excludes a third. These nine exclusions left one of the 220 exactly-three-type alternatives at rank 36: unit norm 26 together with types `(2,28)` and `(2,30)`. This does not exclude rank 36 itself or cases with more than three types. Run `python3 rank36_affine_triples.py`, `python3 rank36-third-triple.py`, `python3 rank36-coclique-tangent.py`, `python3 coclique_sidon_cut.py`, `python3 site_degree_ten.py`, and `python3 rank36_primal_sidon.py` to replay the exact identities with python-flint.

Without any three-type assumption, the [unconditional four-family bound](coclique-sidon-global.md) forces at least one of neutral norms 18 or 20, or the unit types `(2,30)` or `(3,37)`, at every remaining rank.

The [unconditional degree-ten site inequality](site-degree-ten-global.md) gives a second all-rank population constraint. In particular it rules out a graph whose selected units are confined to norm 24 and the types `(1,27)`, `(2,28)`, `(3,37)`.

[Global coclique Sidon packing](global-coclique-sidon.md) makes no assumption on residue-class compatibility: among all 22-cocliques, an ordered difference determines the pair.

[Fano difference packing](fano-difference-packing.md) makes the norm-14 bounds quantitative in terms of norms 20 and 24, with no rank restriction.

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
