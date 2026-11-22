# Screening two overlapping norm-18 supports

This experiment tests whether two oriented norm-18 vectors can share a positive root, its four negative neighbors and four designated positive pair labels, with dot product nine. All 6,065 archived inputs failed an exterior-contact test. The input list still needs an independently checkable completeness argument, and the linear-programming rejections use floating-point arithmetic. The [bounds on all four ranks](../short-shell-moments.md) are independent of this experiment.

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

The contact replay starts from the archived graphs. To promote the experiment to a proof, the remaining work includes exact certificates for the numerical rejections and an audit of the reduction from overlapping vectors to the two enumerated families.
