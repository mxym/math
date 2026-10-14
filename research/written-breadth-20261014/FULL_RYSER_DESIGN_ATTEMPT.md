# Ryser's complete design-minimum conjecture: actual binary witness attempt

14 October2026, Asia/Shanghai. Internal agent /root/written_breadth. Active ordinary breadth research, not a new theorem or publication.

## R0. Whole target and clock

Active stage starts at2026-10-13 21:10:15 UTC, after the bounded full-Chollet Gaussian-replacement stage. Service reviews/interruption time is excluded; after45–90 effective minutes without a substantial complete solution, preserve and autonomously change target.

Let Lambda_v^k be ALL v-by-v binary matrices with every row and column sum k. If the class contains symmetric(v,k,lambda) configurations, Ryser's conjecture asserts that at least one configuration attains the global minimum permanent on Lambda_v^k. A configuration means
\[
 AA^T=(k-\lambda)I+\lambda J,\qquad0<\lambda<k<v.
\]
The target is the complete assertion for every eligible(v,k), not a partial positive result at v13. A legal binary matrix whose permanent is strictly below EVERY configuration at its pair is a full counterexample. A matrix below only one nonminimal configuration is not.

## R1. Fresh primary status and first exact negative route

The current primary author report (read14 October2026) lists the full design-minimum conjecture as open and credits all eligible v<=12 cases. Its first remaining pairs are(13,4) and(13,9); configurations at each pair are unique up to row/column permutations: PG(2,3) and its complement, with reported permanents3852 and64803969. These counts will be independently recomputed. Uniqueness will be treated as a precisely matched disclosed classification input, and independently justified through the order-three affine-plane/orthogonal-Latin-square reduction before using it in any negative claim.

The same report already gives exact strict one/two-switch local bounds at v13 and searches through designs of order21. Those existing positive/local results are not re-counted. The proposed discovery instead uses nonlocal actual regular binary starts and alternating-cycle trades, with exact integer permanent/cofactor evaluation. Every absent violation is only finite discovery evidence, not a proof. The budget is bounded.

The 1960 original survey was located by DOI10.1090/S0002-9904-1960-10494-6, but the guessed direct publisher PDF was inaccessible in the browser. The actual whole statement was read in the primary author-maintained Minc entry; the original PDF will be fetched by a supported primary route if needed. No unseen original proof is claimed.

Primary report: https://yair-lavi.com/mincs-list/conjecture-5/index.html .
It explicitly states SOME configuration, not every configuration or unique minimization. This is distinct from Ryser's odd-order Latin-square transversal conjecture and from the Ryser–Woodall lambda-design generation conjecture.

## R2. Required counterexample verification

Any potential witness must have exact0/1 entries, exact row/column margins, and a strict integer permanent below the least configuration permanent. Two independently structured exact calculations (subset matching DP and inclusion–exclusion/Ryser) will check its permanent and the configuration baseline. All finite count recurrences and the configuration classification argument must be written out in an ordinary complete proof. No float solver status, incomplete configuration catalog, or sampled absence statement is an acceptance criterion.

No new Lean module/audit, agent spawn, push, publication, importance score or full-problem claim is authorized by this exploration record.

## R3. Complete ordinary justification of the unique configuration baseline

For a(13,4,1) configuration, any two row-lines meet in exactly one column-point. Each line has4 points and each point lies on4 lines. No pair of points can lie on two lines, since those two lines would meet in at least two points. There are13 binomial(4,2)=78 line-contained point pairs, exactly binomial(13,2)=78, so every point pair lies on one line. Thus the incidence structure is a projective plane of order3.

Choose one line as infinity and remove its4 points. The remaining9 affine points lie in four parallel classes, each partitioning them into three lines of three points. Pick two classes as rows/columns of a3-by-3 array. The other two classes give two orthogonal Latin squares of order3: every line meets each row and each column once, and lines of different classes meet in exactly one affine point.

Relabel rows, columns and symbols of the first Latin square so its first row and column are0,1,2. Its second row is forced to be1,2,0 (the alternative repeats2 in its third column), and the last row is forced; it is L(i,j)=i+j over F3. Relabel only the second square's symbols to make its first row0,1,2. Its second row starts either1 or2. The Latin constraints force M(i,j)=i+j or M(i,j)=j-i. The first is not orthogonal to L; the second is, because(i+j,j-i) is invertible over F3. Thus the complete affine plane is unique up to relabeling, and completing its four infinity points proves the projective plane is PG(2,3), uniquely up to incidence isomorphism. Every configuration at(13,4) therefore has the same permanent.

For a(13,9,6) configuration A, B=J-A has row/column sums4 and
\[
 BB^T=13J-9J-9J+(3I+6J)=3I+J.
\]
Hence its complement is precisely the same unique plane, so configurations at(13,9) are likewise unique. This is the known order-three classification, written out for counterexample completeness; no novelty is claimed for it.

The exact model is generated by the13 one-dimensional subspaces of F3^3, represented by nonzero triples with first nonzero coordinate1. Use the same representatives for line functionals, with incidence dot-product0 modulo3. Every line/point has degree4 and distinct lines meet once, by elementary linear algebra over F3.

The saved baseline verifier computes per PG(2,3)=3852 and per(complement)=64803969 by two independent exact methods:
\[
 d(0)=1,\quad d(S\cup\{j\})\mathrel{+}=d(S)A_{|S|+1,j}
\]
over increasing assigned-column subsets, and
\[
 \operatorname{per}A=\sum_{S\subset[v]}(-1)^{v-|S|}
       \prod_i\sum_{j\in S}A_{ij}.
\]
The first counts partial matchings; the second is inclusion–exclusion on missing columns in all row choices. These finite count identities do not replace any universal positive proof. They supply the complete all-configuration baseline that a strict actual witness would have to beat.

## R4. Preserved bounded discovery and resumed analytic stage

The completed600-second actual-binary search used10695 starts and214726 descent steps, with24 exact delta controls. Best values remain3852 at(13,4) and64803969 at(13,9), both configuration values. The best nonconfiguration values seen were3884 and64839709. These are discovery minima only; neither global minimality nor any universal positive result follows. The separate exact cofactor diagnostic for the plane gives963 on incidence entries and777 on zero entries. All original data are in exploration/ryser-nonlocal-discovery.json and exploration/ryser-design-cofactor-diagnostic.json.

After the original agent disconnected, replacement active work resumed at 2026-10-14T00:42:04.771005+00:00. The completed search will not be repeated. The next route examines exact alternating-trade expansions and large-order regular graph bounds against ALL configuration baselines. No relaxation or finite positive axis is accepted as a major conjecture solution.


## R5. Exact all-order identity and the low-order square gap

This is an ordinary route derivation, not a complete Ryser solution and not
an assertion of novelty for these matching identities. Let E be the all-ones
matrix, let A be any binary n-by-n matrix with all margins k, and put
B=nA-kE. Both the row sums and the column sums of B vanish. For any weighted
matrix B, let r_m(B) be the sum of products of entries over all placements of
m nonattacking rooks, with r_0(B)=1. Multilinearity of the permanent gives

    per[(kE+xB)/n]
      = n^(-n) sum_(m=0)^n (n-m)! k^(n-m) r_m(B) x^m.       (R1)

To see this, choose the m rows whose permanent factors come from B and
the m distinct chosen columns. Every remaining choice is a permutation of
the other n-m columns and contributes k^(n-m). This accounts for every term
exactly once. The whole Ryser problem is the x=1 endpoint for actual binary A;
x<1 is an allowed real-margin interpolation, not an allowed binary witness.

There is also an exact partition-lattice expression. For a partition p of
[m] put mu(p)=product_(C in p) (-1)^(|C|-1)(|C|-1)!. Then m! r_m(B) is

    sum_(p,q partitions of [m]) mu(p) mu(q)
      sum_(row indices constant on p, column indices constant on q)
          product_(h=1)^m b_(i_h,j_h).                         (R2)

The two inner assignments need not be distinct between different blocks.
Indeed sum of mu(p) over partitions refining a prescribed equality pattern
is 1 for the all-singleton pattern and 0 otherwise. Blockwise this follows
by identifying mu(p) with the sum of signs of permutations having cycle
partition p: for a block of size at least two, the sum of all permutation
signs is zero. Thus the two Mobius factors select exactly the distinct row
and column assignments. Division by m! removes the ordering of the rooks.
If p or q has a singleton block, summing that row or column index kills its
term because the corresponding sums of B vanish.

Consequently, writing S=sum_(i,j) b_ij^2 and G=BB^T, we have

    r_1(B)=0,
    r_2(B)=S/2 = n^2 k(n-k)/2,
    r_3(B)=(2/3) sum b_ij^3 = (2/3)n^2 k(n-k)(n-2k),
    r_4(B)=(3/2) sum b_ij^4
            -(3/4)[sum_i(sum_j b_ij^2)^2
                    +sum_j(sum_i b_ij^2)^2]
            +S^2/8+tr(G^2)/4.                               (R3)

For the fourth formula the surviving partition types are 4 and 2+2 on
each side. Type 4/4 contributes 36 sum b_ij^4 before division by 24.
The 4/(2+2) and reverse types contribute -18 times the row and column
energy-square sums. Of the nine (2+2)/(2+2) pairs, three produce two
disconnected double edges, contributing 3S^2, and six produce a four-cycle,
contributing 6 tr(G^2). These are all the possibilities, proving R3.

Suppose the pair admits a configuration C, with lambda=k(k-1)/(n-1).
All terms of R3 except its final trace depend only on n and k, since every
row and column of B consists of k copies of n-k and n-k copies of -k.
Also G=n^2 AA^T-nk^2 E and its configuration value is

    G_0=c(I-E/n),  c=n^2 k(n-k)/(n-1).

Both G and G_0 annihilate the all-ones vector and have trace S. Hence
tr(G G_0)=cS=tr(G_0^2), and

    tr(G^2)-tr(G_0^2)=||G-G_0||_F^2.

The fixed diagonal entries of AA^T equal k, so this gives the exact gap

    r_4(nA-kE)-r_4(nC-kE)
       = (n^4/4) sum_(i != j) [(AA^T)_ij-lambda]^2 >= 0.    (R4)

Equality is precisely the configuration condition. R4 does not settle R1
at x=1: the higher coefficients have not been controlled. In particular,
the saved actual n=13,k=4 nonconfiguration with permanent 3884 has ordered
row-intersection variance 16, so its R4 excess is 114244. Its radial
coefficient differences at orders 7,8,9,11,12 are negative. The coefficient
sum at x=1 is still +32*13^13, agreeing with the integer permanent gap.
Thus termwise positivity of this centered expansion is false even for an
actual regular binary matrix. This is an obstruction to that proof route,
not a counterexample to Ryser. The independent weighted-rook verifier binds
both actual row lists and all saved coefficients.

## R6. A continuous descent is explicitly not a binary counterexample

For rows r,s and columns c,d of a valid switch pattern (1,0;0,1), let H
have -1 in the two occupied slots, +1 in the two empty slots, and zero
elsewhere. If M is the permanent after deleting these two rows and columns,
multilinearity gives the exact identity

    per(A+tH)=per(A)+L t+2M t^2,                           (R5)

where L is the sum of the cofactors in the two empty slots minus those in
the two occupied slots. The only second-degree choices use both changed
rows and both changed columns; their two products are +1, proving the
coefficient 2M. Higher terms are impossible. At t in [0,1] the matrix has
nonnegative entries and the same margins, but is binary only at 0 or 1.

In the actual saved PG(2,3) labeling, choose zero-based rows 0,1 and
columns 1,5. The occupied-slot cofactors are 963 and empty-slot cofactors
777. The two-deleted minor has permanent 214, independently computed by
subset matching DP and inclusion-exclusion. Therefore

    per(A+tH)=3852-372t+428t^2.

The midpoint has permanent 3773, strictly below 3852, but has four entries
1/2 and is not in Lambda_13^4. The legal switched endpoint has permanent
3908, above the design. Exact weighted DP checks the polynomial at 0,1/2,1.
This prevents interpreting a real transport-polytope descent or an optimizer
output with fractional entries as a complete Ryser counterexample.

Original route exposition: Yongxian Zhang, School of Computer Science and
Engineering, South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. No external funding. OpenAI AI assistants assisted.
Original material all rights reserved; known identities and classifications
are not claimed as new major results. No Lean, publication or priority claim.


## R7. A decreasing fourth-order surrogate can increase the permanent

The row-intersection square gap in R4 cannot serve as a permanent-decreasing
switch potential. The exact actual binary matrices in
exploration/ryser-variance-surrogate-obstruction.json both have row and
column sums four. The first is obtained by the valid eight-cycle
(0,1,2,4,3,5,6,9) in the first saved matching representative. Apply the valid
switch at zero-based rows 3,5 and columns 5,0. Its ordered row-intersection
variance decreases from 64 to 60, while its permanent increases from 4208
to 4212. The saved row masks determine every entry; the separate verifier
checks legality, the switch, both variances and both permanents by matching
DP and inclusion-exclusion. Thus the centered fourth coefficient decreases
by 13^4 but the permanent increases by four. Both permanents are above the
configuration baseline 3852: this only refutes that stronger surrogate
route and is not a Ryser counterexample or a solved major conjecture.


## R8. Closed bounded stage and complete-target boundary

The deterministic matching-orbit discovery completed all its represented
length-two through length-seven cells: 1,172,034 actual binary matrices and
their complements, with 60 independent inclusion-exclusion controls. Its
separate 210-second length-eight extension checked 3,248,128 further actual
matrices/complements and 10 controls. Four representative cells completed;
the fifth stopped at 262,761 candidates and is explicitly incomplete.
No strict integer permanent below either all-configuration baseline was
found. Cycles whose removed partial matching does not extend to a saved
full incidence matching, longer cycles and other regular matrices are
outside this discovery. No search-absence statement is a positive proof.

The full Ryser assertion remains unsolved here, and no legal full negative
witness has been obtained. Exact identities, three route obstructions,
source-reading limits and discovery coverage are preserved. The last
mathematical verification completed at 01:25:20 UTC, after approximately
47 effective research minutes; the long disconnected gaps and the
00:57:57-01:03:41 UTC manuscript service were excluded. The confirmed
original interval is 17m05 and the earlier replacement interval was
inherited as approximately eight minutes, so the total is an estimate.
The ensuing preservation and authorized service are charged zero research
seconds. No formalization, publication, priority or major-result claim.

Next complete target after the authorized new-manuscript service: the full
Lih-Wang conjecture for every dimension and every original parameter
alpha in [1/2,1]. Restricted rank, order, normality, root-free conditions
and finite nonviolations are not complete major results.
