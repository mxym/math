# Root retention and integral pair cores in seven-dimensional kissing configurations

Write a kissing code on the sphere of squared radius two, so that distinct code points have inner product at most one. A root *axis* is a line; a *paired* axis means that both roots on the line occur.

**Theorem.** A seven-dimensional kissing code has at most **126** points if either of the following holds:

1. It contains **at least 109 of the 126 signed roots** of one fixed copy of $E_7$. The omitted signs may be arbitrary, including both signs of several axes.
2. It has **50 paired axes** with pairwise acute line angles $60^\circ$ or $90^\circ$. No conditions are imposed on the remaining points.

For example, a 127-point code representing every axis of a fixed $E_7$ can have at most **45** paired axes: $63+p$ roots are present, and an outsider cannot have its antipode in the code, since every blocker has its opposite sign present. The claims are conditional and do **not** settle the seven-dimensional kissing number.

The [previous guarantee](KissingSevenThirteenArbitraryOmissions.md) required 113 signed roots. Full equatorial sections and rigidity are different conditions: see [Novgorodtsev](https://www.preprints.org/manuscript/202610.0335) and [Cohn, Jiao, Kumar and Torquato](https://arxiv.org/abs/1102.5060). The [replay](verify-kissing-seven-retention-and-integral-core.js) is deterministic Node.js without external packages.

## Finite outer cells, not a discretization of the code

For a nonroot sphere point $x$ write $B(x)=\{r\in E_7:r\cdot x>1\}$. By the [minimum-blocker theorem](KissingExceptionalRootCoverBranch.md) this set has at least six signs. By [strict mask separation](KissingExceptionalMaskSeparation.md) each signed mask has capacity one in a kissing code. These facts concern arbitrary real points, including chamber walls.

The replay reconstructs the same closed outer cells used in that separation proof. In the fundamental chamber $w_i=\alpha_i\cdot x\ge0$, the squared norm is $w^\top G^{-1}w$ and a mask is an upper ideal in the positive-root coefficient order. For each ideal the active-basis vertices of its closed cell are found by exact determinants; high vertices and dyadically clipped high-to-low edges enclose its entire sphere slice. If there are no high vertices, only sphere-level vertices with the actual strict mask survive, and we drop points that are roots. To cover all chambers for a fixed signed mask, close its generators under the stabilizer of the dominant sum of the mask. Details, including the convex-hull argument on the barycentric simplex, are in the linked separation proof.

Each pair of cells is declared incompatible only if **one entire test** works: either every generator pair has physical inner product $>1$, or all have positive dot product and cosine at least $1/2$, with no equality pair whose rays both have the respective actual masks. The linear test extends by convexity. The cosine test extends by the triangle inequality; equality forces all used generators on each side to be positively collinear, contrary to the equality check. In testing whether a pair *could* instead have dot $<-1$, it is necessary that some generator pair has physical inner product $<-1$. All these sign tests, including on equality, use integers.

For a small set of weak axes or missing signs, larger candidate masks are generated from the two formal six-root upper ideals by single-root additions. Intermediate formal ideals are **not** required to meet the sphere. To recognize an extension, move its sum into the dominant chamber and check the transported root set itself against the formal table. This is complete: the dominant sum stabilizer fixes the ideal, as in the separation proof. An extension is dropped when its extra axes already exceed the available budget; later additions cannot repair that.

## I. A trade of missing signs must start at a negative outsider edge

Suppose there is a counterexample with 127 points and at most $m_\max=17$ root signs missing. From a larger counterexample one can retain all its old roots when selecting 127 points. Among such counterexamples maximize the number of roots retained, and let $m$ be its exact number of missing signs. There are $m+1$ outsiders. Every missing sign is in at least **two** outsider masks: otherwise restore that root in place of its sole blocker, or remove an arbitrary outsider if it blocks none. The previous theorem gives $m\ge14$.

Let $z$ original axes lack both signs, so $p=63-m+z$ are paired. There must be two outsiders $x,y$ with $x\cdot y<-1$. Otherwise all $m+1$ outsiders and the $p$ paired axes make $p+m+1=64+z$ distinct projective kissing lines, violating [Anstreicher's bound of 63](https://optimization-online.org/2001/01/248/). Such a negative edge has **disjoint signed masks**: a common blocker $r$ would give $r\cdot(x+y)>2$ whereas $\|x+y\|^2<2$. Opposite signs on the same axis are **allowed**.

Fix one endpoint type by symmetry. Its size and the second size are at least six and sum to at most $m$. Enumerate possible relative placements of the second type modulo the subgroup fixing the first. In the quotient search, from each representative apply reflection in **every root axis** and fold the new mask sum into the chamber of that subgroup using its simple generators. This contains every quotient orbit: conjugation by the subgroup permutes the full set of root reflections, and folding stays in the same subgroup orbit. Compute a transporter and check the signed mask itself whenever a representative is added. Reject a shared signed blocker or a pair whose convex hulls cannot realize a negative edge. Only disjointness of actual **signs**, not axes, is used.

Write $M$ for the pair's mask union, with $e=m-|M|$ signs still free. Build all possible outsider masks that could lie in a completion, keeping also masks that add an opposite sign on an axis already used. The following small search avoids enumerating the entire Boolean cube. At a partial set $M\cup X$, look for a sign already chosen but currently supported by fewer than two masks contained in $M\cup X$. If it cannot attain degree two within budget, stop. Otherwise branch by adjoining every eligible larger mask containing this sign. If all signs chosen so far are supported, branch by adjoining any mask that increases the union and fits the budget. A genuine maximal-overlap solution is preserved: each missing sign is supported twice, and if any sign is still absent from the partial union it belongs to some actual additional mask. Equal partial unions may be merged. A perpendicular $D_6$ section that must lose at most two signs even after spending the entire remaining budget is excluded by the [58-of-60 equator theorem](KissingPartialD5D6Equators.md).

For a complete union, rule it out by a near-full $D_6$ section, fewer than $m+1$ potential sites, a deficient sign degree, or a checked coloring of all its sites: color each site by one of its missing signs, with pairwise incompatible sites whenever their color agrees. At most one actual outsider can take any color, leaving room for only $m$. The checker also has an exhaustive independent-set fallback, not needed in any of these four rows.

| Missing signs | Eligible negative-edge representatives | Complete unions reached by the support search | Near $D_6$ | Few sites | Sign degree | Coloring | Independent-set fallback |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 14 | 76 | 96 | 93 | 0 | 0 | 3 | 0 |
| 15 | 264 | 3,147 | 2,933 | 30 | 137 | 47 | 0 |
| 16 | 1,276 | 16,441 | 12,405 | 310 | 2,270 | 1,456 | 0 |
| 17 | 3,757 | 204,773 | 122,034 | 5,215 | 48,035 | 29,489 | 0 |

Counts are by anchored representative and search, not claimed to be global orbit counts. As a separate coverage check, direct enumeration without the support-search pruning examined 2,215,380 signed completions at $m=15$ (also including opposite signs) and found none admitting 16 outsiders.

## II. Fifty paired axes suffice without any single-sign retention hypothesis

First suppose 50 paired axes are prescribed in a copy of $E_7$. The 13 remaining axes are weak: either, both or neither sign may still be present. If a code exceeded 126 it would have a nonroot point. Fix its signed mask in the chamber, then complete its support to 13 weak axes under its stabilizer. The orbit augmentation chooses the *first* orbit in a fixed ordering met by the remaining set, transports a member to the first label in that orbit, and recurses with its point stabilizer after removing the earlier orbits. This covers all configurations, allowing repetitions; duplicate completed coordinate sets are discarded.

A $D_6$ equator with at most one weak axis loses at most two root signs, hence cannot allow 127. In every other case form all possible outsider sites (their masks live on the weak axes). Inject them into signed blockers by ordinary bipartite matching, or use the stronger verified list coloring above. In **any** realization, each outsider then has a distinct missing root, so the total size is at most 126. The census checks **1,521,201** anchored placements: 406,849 near-equator exclusions, 984,451 ordinary matchings and 129,901 list colorings. The greatest candidate list has 204 sites.

Finally, the reflection closure of 50 pairwise integral unit-root axes, at this normalization, is a simply-laced root system in rank at most seven. Indeed the integral span is a lattice (use a maximal independent subset and its dual), and its norm-two vectors form a finite reflection-stable root system. By the [ADE classification](https://ocw.mit.edu/courses/18-745-lie-groups-and-lie-algebras-i-fall-2020/pages/lecture-notes/), all alternatives to $E_7$ have at most 84 roots: $D_7$ attains 84, $A_7$ has 56, and the largest reducible case is $E_6+A_1$ with 74. Thus the given 50 axes lie in an $E_7$, proving the second assertion.

**Replay.** Use `node verify-kissing-seven-retention-and-integral-core.js core` for the pair-core theorem, and `node verify-kissing-seven-retention-and-integral-core.js signed m` with $m=14,\ldots,17$ for arbitrary omissions. No random points, floating-point cutoffs or external optimization certificates enter these decisions.
