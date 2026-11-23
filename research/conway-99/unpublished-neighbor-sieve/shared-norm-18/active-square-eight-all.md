# At most eight active charge-two squares through any edge

Fix a graph with Conway's parameters, with **no** Seidel-rank, symmetry, or sparsity assumption. Call an induced square active when it carries the [c=0 positive charge-two, cost-26 configuration](u226-positive-pair.md#fixed-positive-pair-when-c0). Every edge lies on at most **eight** active squares. The graph therefore has at most 1,386 active squares and at most 2,772 c=0 fields, counted at charge +2.

In particular the rank-38 support contained in **{018,024,226,228,230,337}** is impossible: the *same global count of oriented norm-18 fields* would have to lie between **12,526 and 12,320**. Neither the remaining rank-38 supports nor the whole existence problem are decided here.

## Exact constraints for candidate rows

Use [the full root-row theorem](u226-full-root-row.md); only its graph-side conclusions are needed. At a true edge pz with triangle cap a, index its twelve remaining p-neighbors by w_i and match them across to the twelve z-neighbors q_i. Let l,r be the wing mate involutions. Regarding p as the root, let L={w_0,…,w_11,z,a}; the 84 sites outside its closed neighborhood are in bijection with nonmate pairs of L, a far site meeting exactly its two parents. Here bar(k)=l(k), bar(z)=a. In particular q_i has pair {z,i}. The squares through pz are precisely its 12 choices i.

For an active i, use the orientation with positives p,q_i, by the diagonal switch. The six zeros on L are S_i={z}∪X_i where X_i is a five-set containing i,l(r(i)),r(l(i)); it contains no l- or r-mates. Write U_i=X_i−{i} and O_i for the omitted p-mate pair in L outside S_i∪bar(S_i). Its far row and its field are subsets of the same 84 pair labels:
* H_i is a perfect matching from S_i to bar(S_i) using no mate pair. The partner of z is r(i); the partner of a is tau(i) where tau is the genuine third-wing return permutation, with tau^−1(i) also in X_i.
* A_i is a perfect matching on the four U_i; E_i consists of four pairs from O_i to bar(U_i), each omitted member used twice, each latter member once. Write C_i={z,i}×U_i for the eight cut pairs.
* R_i=H_i∪A_i∪E_i is the **complete** far-neighbor row of q_i, and F_i=H_i∪A_i∪C_i is the set of sixteen far negatives of the i-field. All displayed constituent unions are disjoint. The other nonzero far site of the i-field is q_i (positive). On L it is zero on S_i and negative everywhere else. Distinct active squares through the same pz have distinct X_i, by the fixed-root matching proposition in the full-root-row theorem.

For an inactive index u the actual twelve-neighbor far row R_u still exists, but no field or matching shape is assumed. If j is active and i≠j, let e=[i=r(j)] and h=[i∈X_j or e]. Then
```
|R_i∩R_j| = 1−e,       |R_i∩F_j| = 3(1−h),       |R_i∩C_j| = 2(1−h).
```
For the first identity q_i,q_j share z and no other near neighbor; they are adjacent precisely when e=1. For the second, the j-field b satisfies Ab=−4b−4·1. At q_i, its near-neighbor values are b(z)=0 and b(w_i)=−[i∉X_j], and its far-neighbor sum is e−|R_i∩F_j|. Also b(q_i)=−h by the description of F_j. Substitution proves the identity in all three possibilities (i∈X_j, i=r(j), neither).

For the third identity, each u in U_j is a nonmate of j and has |R_u∩R_j|=1, |R_u∩F_j|=0. Its shared q_j far neighbor must be one of the four E_j. These four witnesses are distinct: all are exterior to the z-neighborhood, and z already sees q_j and q_u, so no second such q_u can meet the same witness. Thus every E_j site has its entire two-common-neighbor capacity with z exhausted at q_j and its assigned q_u. When h=0 the unique intersection R_i∩R_j is consequently in H_j∪A_j. Subtracting that one from |R_i∩F_j|=3 leaves exactly two in C_j. When h=1, F_j is disjoint from R_i so its subset C_j is disjoint also. The use of all four u's is legitimate even if some are not active.

For two active indices enforce these relations in both directions, distinct X, and the necessary partial permutation constraints tau(i)≠tau(j), tau(i)=j⇒i∈X_j (and conversely exchanging indices). In particular no *restriction* to any particular return or its conjugacy class is made. No differences of two fields and no shell absences enter the enumeration.

## Complete finite check

The two colored perfect matchings split into alternating components of even sizes 2k, including double edges k=1, giving exactly the eleven partitions of 6. In each component number the sites cyclically, taking l to exchange (0,1),(2,3),… and r to exchange (last,0),(1,2),…. At a specified i, enumerate all five-sets X_i, five remaining choices of partners as one permutation for H_i with four forbidden own-mate positions, the three matchings A_i, and the six assignments E_i. Thus every allowed X gives (5!−4·4!+6·3!−4·2!+1)·3·6=954 rows; the generator also checks that the resulting (X,tau,R,F) tuples have no duplicates. For each ordered pair of distinct active indices mark exactly which rows pass the preceding pair equations. These are necessary, not sufficient, conditions.

For a fixed nine-subset, repeatedly delete a row if any other selected domain has no compatible row. On nonempty stable domains, pin one row in the smallest nonsingleton domain and recurse on all possibilities. All domains and every branch are finite; an empty domain certifies exclusion. Relabeling equivalent cases can be reused without assuming any automorphism of the full graph: within a 2k-component the 2k moves x↦t+(−1)^t x preserve both colors. Equal components can be permuted. The code verifies every generator used preserves l and r. When moving an ordered pair to canonical positions, it relabels *all* 84 far labels and checks its permutation of candidate tuples as a literal equality of all eight machine words (X,tau,R,F,C, the last three represented by two words each). Reciprocity when propagating in the reverse direction uses symmetry of the stated pair rules. Initially, when pinning a row, representatives under a subgroup fixing the nine-subset and chosen index suffice. The code verifies these conditions on every used generator and covers the original domain by breadth-first orbits. All later recursive levels try every surviving row. Bitwise counts are integral (all cardinalities ≤84) and there are no floating-point decisions, optimizers, time cutoffs, external data, or unstated completion assumptions.

| Half-length partition | Admissible five-sets by distinct site type in displayed order | Nine-subset orbits |
| --- | --- | ---: |
| 6 | 6 | 19 |
| 5+1 | 7,25 | 20 |
| 4+2 | 6,16 | 17 |
| 4+1+1 | 8,34 | 16 |
| 3+3 | 9 | 8 |
| 3+2+1 | 10,20,26 | 22 |
| 3+1+1+1 | 12,44 | 12 |
| 2+2+2 | 16 | 5 |
| 2+2+1+1 | 24,36 | 11 |
| 2+1+1+1+1 | 32,56 | 8 |
| 1+1+1+1+1+1 | 80 | 2 |

The [exact checker](active_square_eight_all.py) rejects all 140 representatives, covering all 220 labeled nine-subsets in each of the eleven matchings. Run on Linux with Python 3, NumPy ≥2.0, and a few GB of RAM for the largest partition; individual partitions can be replayed independently.
```
for p in 6 5,1 4,2 4,1,1 3,3 3,2,1 3,1,1,1 2,2,2 2,2,1,1 2,1,1,1,1 1,1,1,1,1,1; do
  python active_square_eight_all.py "$p" || exit 1
done
```
No nine-subset exists, and every set of nine or more would contain a nine-subset. This proves the bound of eight.

## Literal populations and the rank-38 contradiction

Each active square has four graph edges. Since there are 693 edges, at most 693·8/4=1,386 squares are active. Each has exactly two c=0 labels: at least one for each positive diagonal by the switch, at most one for each by [unconditional diagonal uniqueness](norm16-height-two-edge.md). Thus n_0≤2,772. The [two disjoint transfers](u226-disjoint-transfers.md) applied to the remaining subtypes give **2G226≤5544+3U127**, or **2G226+3N16≤5544+3U127** graph-wide using the [disjoint norm-16 transfers](u226-norm16-disjoint.md).

At rank 38 suppose now that the twelve selected unit types are contained in {018,024,226,228,230,337}. U127=0 implies all G226 fields are c=0. The [existing fixed-H scalar identity and its graph averaging](u226-global-pressure.md) give
```
6N18 + 9G226 = 291·344 + 344(16F+2S+5M) + 3U228 + U337 ≥ 100104,
```
where F,S,M are the nonnegative indicated averages. Consequently **N18≥(100104−9·2772)/6=12526**. But N16=N20=0, so the [oriented seed bound](norm18-rank36-four-hit.md) gives **9N18+210N14≤110880**, hence N18≤12320. These are incompatible bounds on the very same graph-wide oriented neutral markings. Positive charge-two fields are counted with charge +2 only in G226; this is not a comparison counting candidate graphs.

More generally at rank 38 with N16=N20=0 the very same two inequalities give
```
2U026+34U121+2U125+29U127 ≥ 2472+6U228+2U337+280N14+11008F+1376S+3440M.
```
This quantitative constraint has no further support hypothesis. At rank 36 with N20=U127=0 (which forces N16=0), the analogous substitution in the same scalar identity, using the previously established U121≤29,372, gives U026+U125≥291·2402−9·2772−6·12320−17·29372=100,790. These claims do not eliminate an entire Seidel rank.
