# Complete deterministic log-rank written attempt

Author: Yongxian Zhang, South China University of Technology; mxymmxym1@gmail.com; ORCID0009-0000-3864-3536.
All rights reserved. No funding. OpenAI AI assistants assisted this ordinary internal research.

## L0 Complete original target

The sole active breadth target is LR0 in [the map](LOG_RANK_THEOREM_MAP.md): every finite totalBoolean communication matrix, worst-case deterministic protocols, real rank, and uniform global constants. Positive and negative acceptance are explicitly asymptotic and normalized at ranks0/1. Finite exponent violations, promise problems or other communication models are not complete resolutions.

[Current primary scopes](LOG_RANK_SOURCES.json) found no full resolution. HLS2510.02583v3 and Song2608.01812v1 supply current semantics/status; their already proved signed decomposition and existing simulations are attributed inputs. The original1988 paper was not retrieved. No priority or fresh formal audit is claimed.

Map prepared before own mathematics. Source05:02:13-05:04:52UTC contributes159effective seconds. Map/commit preservation is excluded. No new complete result at activation.

## L1 Intended whole-domain mathematical routes

Work directly on actualBoolean matrices and their exact signed primitive decompositions, studying whether all-pair0/1 cancellation forces a quasipolynomial positive partition or a uniformly large monochromatic rectangle. Preserve row and column dependence; a common row-only partition or a one-sided special-function theorem cannot replace the full target. Alternatively any negative family needs an exact rank certificate and superpolynomial-logrank deterministic lowerbound for all fixed exponents. Known polynomial-separation constructions do not suffice.


## L2 Exact Boolean bilinear and quadratic-feature obligations

Choose a minimal real factorization M(x,y)=a_x^T b_y of rank r, so both vector families span R^r. ActualBoolean entries impose the pointwise identity M circle M=M (Hadamard product, not ordinary matrix multiplication). Set
U=span{a_x a_x^T}, V=span{b_y b_y^T}, N=dim Sym_r=r(r+1)/2.
The trace pairing between U,V has rank exactly r: its evaluation matrix is M circle M, and evaluation maps onto the spans preserve that rank. Since its nullspace in U is U intersection V-perpendicular, its rank is at least dim U+dim V-N. Therefore
dim U+dim V<=N+r.
This necessary dimension bound does not give a polylogarithmic communication protocol.

For S=2M-J, let rho=rank_R(S) and use a minimal factorization S(x,y)=u_x^T v_y. Its Hadamard square is J, so the corresponding quadratic spans satisfy
dim U_S+dim V_S<=rho(rho+1)/2+1.
After whitening the uniform row second moment, E_x u_x u_x^T=I, every column vector obeys ||v_y||^2=E_x S(x,y)^2=1 and E_x||u_x||^2=rho. The latter is an average, not a uniform row-norm bound. These exact coupled quadratic conditions retain the actual sign matrix; no low-entropy positive concentration or large rectangle follows here without another proof.

## L3 Known all-domain adjacent-intersection bridge

HLS2510.02583v3 Section3, now actually read, converts each signed rectangle into two positive primitive matrices representing J+R or J-R. A q-term signed decomposition therefore represents M+qJ as a sum of2q primitive matrices, hence as a cross-intersection matrix over2q coordinates whose entries are exactly q or q+1. This is the prior complete equivalence, not a new major result.

Fixing the two family cardinalities by pigeonhole loses at most(2q+1)^2 in rectangle area. It still leaves arbitrary uniform families with the two cross-intersection values; that complete structural question is unproved here. Converting each (q+1)-intersection to its unique (q+1)-subset uses a universe of size binomial(2q,q+1), exponentially large in q. A resulting bound polynomial in this universe does not give quasipolynomial rank control. No reduction to the already easier cross-intersection0/1 domain is adopted without bounding this growth.

## L4 Actual totalBoolean control against a common one-way partition

For every s>=2, define the standard two-index product
K_s[(x,i),(j,y)]=x_j y_i,
where x,y range over all s-bit strings and i,j range over all s coordinates. Its order is s2^s in each direction, and every cross input is defined.

The matrix is the Kronecker product of the bit-table A_s and its transpose, with real rank s^2. Independently, rows(x=e_a,i=b) and columns(j=c,y=e_d) give the identity matrix of order s^2. The s^2 all-one rectangles specified by
i=b,x_a=1 and j=a,y_b=1
are disjoint and reconstruct every1-entry. Thus they also certify rank at most s^2 and signed rectangle rank exactly s^2.

There are s(2^s-1)+1 distinct rows and equally many distinct columns: the zero strings give one shared zero type, all others are different. Alice-to-Bob one-way communication consequently needs at least ceil(log_2(s(2^s-1)+1)) bits, because distinct rows cannot share a message. In contrast, Alice announces i, Bob announces j, Alice announces x_j, and Bob announces the final product, using at most2ceil(log_2 s)+2 bits with a public output. This is an elementary known-family control. It shows that both one-way common partitions can be exponentially larger than the interactive protocol in the log-rank parameter. It is not a new full or restricted-major outcome.

Finite exact controls at s2,3,4,5 check30,336 actual entries, identity minors, disjoint reconstruction, row/column types and protocol outputs. They are auxiliary, not acceptance evidence for all matrices.

## L5 Nonnegative real matrices cannot replace actualBoolean matrices

The familiar real matrix T_n(i,j)=(i-j)^2 has rank3 for every n>=3: the formula i^2+j^2-2ij gives rank<=3, and its first3-by-3 determinant is8. Any nonnegative rank-q factorization has q support rectangles, none containing a diagonal entry. Their row-membership signatures must be different at all n indices; otherwise covering the positive entry(i,j) would also cover(j,j). Therefore q>=ceil(log_2 n).

This yields an unbounded nonnegative-rank gap at fixed real rank, but T_n is not Boolean and is rejected as a log-rank witness. Thresholding its support gives J-I, of real rank n. It does not preserve the small rank. No matrix-domain relaxation enters LR3.

## L6 Known deterministic XOR extraction and failed direct amplification

Iyer–Rao, ECCC TR24-111, Theorem4 and its short entropy proof, are actually read as prior input. Let beta_t be the largest monochromatic-rectangle fraction for the t-fold XOR of a totalBoolean function f. Their theorem gives
beta_t^(1/t)/4<=beta_1,
while tensoring an original monochromatic rectangle gives beta_1^t<=beta_t. Hence
beta_1<=beta_t^(1/t)<=4beta_1.

The sign matrix for the t-fold XOR is S^(tensor t), of exact rank rho^t. Substituting the existing universal rectangle bound gives only
beta_1>=2^[-C rho^(t/2)/t]/4.
For rho>=4 and every integer t>=1, rho^(t/2)/t>=sqrt(rho), because2^(t-1)>=t. Direct amplification thus leaves the root-rank scale. A bound beta_t>=2^[-t polylog(rho)] could complete the route, but has not been proved; known extraction does not supply it. Neither a signed measure nor a quantum amplitude is treated as a nonnegative rectangle probability.

## L7 Safe active checkpoint, no complete solution

No uniform polylogarithmic protocol for every actual totalBoolean matrix, and no admissible superpolynomial-logrank infinite reverse family. The exact coupled moment conditions, all-domain signed bridge and tensor reductions retain LR0 but remain unclosed. L4 is a known-family shortcut control and L5 an inadmissible real matrix. No new major-result count.

At05:21:00UTC, source159seconds plus mathematics05:06:51-05:21:00 give1008effective seconds (16m48). This checkpoint preservation is excluded; the same complete stage continues afterward without reset. No discovery process is running and no authorized manuscript service has paused this phase.

## L8 Explicit user extension, same active target

The user now gives current/future whole-target stages approximately120effective research minutes and permits an earlier switch only on concrete evidence of near-impossibility or an already resolved original domain. The old45-minute stopping trigger is revoked. At05:26:38UTC the existing16m48 checkpoint plus188resumed seconds totals1196seconds (19m56); this is accumulated, not restarted. This policy preservation is excluded. CH closed before the new instruction, so its45m06 historical record remains unchanged. See BREADTH_RESEARCH_POLICY.json. LR0 and complete-result acceptance remain unchanged; no new major solution.


## L9 Duplicate inputs and product-measure scope

Duplicating a row or column preserves real rank, signed/positive partition numbers and deterministic communication complexity: collapse to its local type, or expand a rectangle/protocol back to all copies. Rectangle fractions are instead weighted by those multiplicities; do not silently equate fractions after deduplication.

A uniform whole-matrix rectangle theorem also gives the same guarantee for any product probability measure. For rational row/column masses, duplicate according to common denominators, apply the theorem, and fill out any partial duplicate classes in the resulting monochromatic rectangle. For real masses, approximate and use the finite set of possible original rectangles to pass to a subsequence. Arbitrary joint distributions are not covered by this cloning argument. A Gibbs tilt of all entries may correlate the two parties, so its low relative entropy does not produce an allowed rectangle automatically.

## L10 Actual signed-cancellation entropy can be large in an easy matrix

For s>=2, let r=2s and gamma=(1,...,1,-1,...,-1), with s of each sign.
Take all rows x in {0,1}^r such that gamma*x is0 or1. Use r coordinate columns x_i and r copies of the gamma column. Every input pair is defined and Boolean. There are
m=binomial(2s+1,s)
rows; its gamma-output counts are m0=binomial(2s,s) and m1=binomial(2s,s-1).
The coordinate factorization has rank<=2s; rows e_i (positive coordinates) and e_1+e_j (negative coordinates), with all coordinate columns, give a triangular rank minor of determinant1. Thus its exact rank is2s.

Use s positive rectangles covering coordinate i and gamma copies simultaneously, s positive coordinate rectangles for the negative indices, and s negative gamma rectangles. This is a3s-term signed primitive decomposition, within a factor3/2 of the optimal possible count because signed rank>=real rank=2s. At a gamma column its active-term pattern identifies x exactly. Under uniform rows and columns,
H(active pattern | column)>=0.5 log_2 m,
linear in s. Even after choosing a fixed gamma-output bit, the remaining pattern entropy is log_2 m0 or log_2 m1. Yet Bob can name his coordinate/gamma column type and Alice give the output using at most ceil(log_2(2s+1))+1 bits. The gamma-copy monochromatic rectangles have fractions m0/(2m) and m1/(2m), bounded away from zero.

This is an exact actualBoolean shortcut obstruction, not a log-rank refutation: a fixed near-optimal signed representation can keep high private cancellation entropy even inside an easy monochromatic region. A successful protocol must be free to change the representation after restriction. Finite controls s2 through6 verify52,940 entries, signed reconstruction, identity/triangular rank witnesses, pattern injection and the protocol.

## L11 Standard clique-versus-independent-set mechanism and overlap cap

For a graph on Q vertices, the standard deterministic search protocol for a clique C and independent set I uses O(log^2(Q+1)) bits. On the current vertex set U, if C contains a vertex of degree<= (|U|-1)/2, Alice names it. If it belongs to I, it is their intersection; otherwise all possible intersection vertices lie among its neighbors, a set of at most half the size. If C contains no such vertex, Bob names a vertex of I of degree> (|U|-1)/2, if one exists. If it belongs to C, terminate; otherwise all intersection vertices lie among its other non-neighbors, again at most half. If neither kind exists, C and I are disjoint. Each round costs O(log(Q+1)) and halves U. This reproduced known mechanism is not a new result.

Suppose signed term patterns A_x,B_y over[q] have a universal overlap cap |A_x intersection B_y|<=K on the entire current product domain. Lift them to families of K-subsets over a universe of binomial(q,K) coordinates. Join two different coordinates if they occur together in some row family. Each row gives a clique; every column is independent, because two common distinct K-subsets would imply an overlap of at leastK+1. The above search therefore either identifies the whole K-element intersection, giving its signed sum, or returns a product transcript region whose all cross overlaps are<=K-1. Rebuild and recurse on that region. Worst-case communication is O(K^3 log^2(q+1)); all computation is public and unrestricted, and every transcript region remains a product.

For K1 this recovers the easier positive-disjoint case. At K=q it does not improve the known rank bound. A polylogarithmic essential-overlap cap after cheap restrictions would help, but is unproved; the signed difference0/1 does not itself bound total overlap. Likewise a squared-intersection matrix (1-|A intersection B|)^2 has rank<=1+q+binomial(q,2) but nonBoolean values when intersections exceed2. Product-family restrictions with all intersections<=2 become Boolean but have an exact polylog-q protocol by this overlap mechanism. An arbitrary nonproduct unique-disjointness promise is not a full target witness.

## L12 Whole-target heavy rank-strip reformulation, still unproved

For an actualBoolean matrix of rank r>=5, seek a row strip or column strip occupying at least
delta(r)=2^[-C log_2(r+1)^k]
of that party's inputs and having rank<= (r+3)/2<=4r/5. This quantified existence statement for every matrix is equivalent to LR0 up to polynomial exponents; it is not proved here.

To verify the bridge, a monochromatic rectangle R in a block matrix [R A; B Z] gives
rank(A)+rank(B)<=r+1,
by replacing R with zero and eliminating the two disjoint off-diagonal blocks. Therefore the two complete strips [R A] and [R;B] have ranks summing to at most r+3, so one has the required rank bound. Its mass is at least the rectangle fraction. A complete LR0 protocol supplies a large leaf, establishing this conditional direction.

Conversely assume the strip statement holds uniformly. Initially collapse duplicate row/column types, leaving at most2^r of each. A party sends one bit for membership in the strip. An accepted branch decreases rank by4/5; a rejected branch decreases the input product size by1-delta(r). With the initial rank r0, there are O(log r0) accepted branches and O(r0/delta(r0)) rejected branches on every path. The number of leaves is at most
2^[O(log r0 (log r0+log(1/delta(r0))))],
with ranks<=4 handled by the elementary finite-rank protocol. A deterministic protocol tree with L leaves can be rebalanced to O(log L) bits: choose a subtree containing betweenL/3 and2L/3 leaves, test membership in its rectangle using at most2bits, and restrict to the surviving subtree or to the branch excluding it. Repeat. This standard existing simulation applies to protocol trees, not arbitrary partitions. The resulting full cost is polylog(r0).

Thus the remaining matroid/flat concentration assertion must use both actualBoolean vector configurations. The quadratic-span inequalities in L2 alone do not imply it. No rank-halving assertion is adopted as a theorem.

## L13 Existing norm and single-parity blockers, credited precisely

Balla–Hambardzumyan–Tomon2506.23989v1 Theorem1.4/Section6 is a prior actualBoolean construction with gamma2<=gamma and no square monochromatic submatrix above a relative side scale2^[-gamma+O(1)]. Its full short construction was read, alongside the final2026 primary theorem/status excerpt. It shows that tightening a universal gamma2-only guarantee cannot by itself give a polylog-rank theorem through gamma2<=sqrt(r). Its actual rank is only bounded by its larger ground-set size; no rank~gamma^2 or log-rank counterexample is inferred. Published32-page/full-v1 proof audit is not claimed.

Hatami–Hosseini–Lovett–Ostuni2312.09400v2 already refutes both a universally large single Fourier-folding direction and a frequent-large-folding approach for XOR functions. The actual primary statement and introduction were read; the remainder of the counterexample proof was not audited. These existing failures exclude those stronger greedy assumptions. They do not refute LR0 or the arbitrary full-product rank-strip condition in L12.

## L14 Active two-hour checkpoint

At05:51:05UTC, the prior1196effective seconds plus mathematics05:27:47-05:51:05 give2594seconds (43m14). No uniform whole-matrix solution or legal superpolylog infinite counterfamily. L9-L12 preserve the complete domain and explicit unresolved conditions; actual controls and known blocks remain auxiliary. Under the user's superseding120minute policy this is a preservation checkpoint, not a stage closure. All current scripts ended; no manuscript service or separate review role paused the clock. Resume the same target after preserving these bytes, without reset.

## L15 Exact basis-block representation and bounded finite discovery

Any rank-r actualBoolean matrix has an invertible r-by-r actualBoolean submatrix H. Record every row by its entries x on those r basis columns and every column by its entries y on the r basis rows. Then every actual entry is exactly x^T H^(-1)y. The row family contains the rows of H, the column family contains its columns, and both are binary coordinate patterns. Conversely any such two full families with all cross values in{0,1} give a complete actualBoolean matrix of exact rank r, certified by H. Rank of a complete row or column strip is the linear rank of its coordinate patterns.

A single300.002second discovery run used selected r4..7 invertible binary blocks, exact rational inverse/adjugate, all bit-pattern compatibility and Galois closure. It completed31734starts, skipped11352singular and13089large configurations, and fully enumerated maximal flats in7293selected configurations with both orders<=18. It enumerated all independent k-subsets, k=floor((r+3)/2), and all their spans. RREF modulo1009 is exact for these binary minors of order<=7: Hadamard gives absolute determinant<=7^(7/2)<1009, so a nonzero real minor cannot vanish modulo this prime. Every lower-dimensional sample flat extends to dimension k because the family spans r. Membership uses the same binary-minor certificate.

The smallest observed maximum of the two parties' rank-k strip masses was3/5,7/11,9/17,2/3 at r4,5,6,7 respectively. No selected configuration violated the stronger constant1/2 hypothesis. The selection and small ranks give neither a universal positive proof nor a full counterexample. The process ended normally; no repeat is needed for this control. Source and JSON retain the exact sampled configurations and enumeration scope.

## L16 An actual infinite control against constant-mass half-rank strips

This auxiliary existence proof rejects a stronger greedy claim, not LR0 or L12. For all sufficiently large integers r, set
c=floor((log_2 r)/8), N=floor(r^(3/2)), d=floor((r+3)/2).
There exist finite families A,B of subsets of[r], with all cross intersections0/1, for which the intersection matrix has real rank exactly r and deterministic cost O(log^2 r), yet every complete row or column strip of rank<=d has relative mass O(r^(-1/8)). No priority is claimed for this elementary easy-family control.

First, for any linear subspace F of R^r of dimension<=d, some d coordinates (or fewer, extended to d) give an injective coordinate projection on F. Consequently F contains at most
sum_{j=0}^c binomial(d,j)
binary vectors of Hamming weight c. A uniformly random c-subset thus lies in F with probability at most h_r, this sum divided by binomial(r,c). Since c=O(log r), d=r/2+O(1),
h_r<=(1+o(1))2^(-c)<=3r^(-1/8)=p_r
for all sufficiently large r. Indeed successive lower binomial terms form a geometric upper bound with ratio c/(d-c+1)=o(1), and binomial(d,c)/binomial(r,c)<=[d/(r-c+1)]^c=2^(-c)exp(O(c^2/r)).

Independently sample N uniform c-subsets for each of two labeled families, with replacement. Append the r singleton coordinate vectors to each sample family for the following concentration argument. A subspace spanned by at most d selected points, some deterministic singletons and some sampled points, can be conditioned on those selected samples. All remaining samples in its family stay independent with containment probability<=p_r. A Chernoff bound gives probability<=exp(-p_r N/3) that at least2p_r N of those remaining points lie in the span. There are at most(N+r+1)^(d+1) possible selected subsets of size<=d. Their union probability is o(1), because p_r N is of order r^(11/8), whereas the logarithm of that candidate count is O(r log r).

This bound covers every subspace, including one chosen after seeing the sample: its intersection with the sample/singletons has a basis of at most d selected points, whose span contains exactly that intersection. Thus, with probability1-o(1), each family's every dimension<=d subspace contains at most2p_r N+d+r of its points, counted with sampled multiplicities.

Next call an unordered pair among the combined2N sampled sets bad if its intersection has size>=2. For two independent c-subsets,
Pr(bad)<=binomial(c,2)c(c-1)/(r(r-1))<=c^4/(2r(r-1)).
The expected total bad pairs is O(r c^4). By Markov, with probability1-o(1) there are at most r^(5/4) bad pairs. Delete every sampled set incident to a bad pair. At most2r^(5/4) sets are deleted from the combined sample, so each family keeps at least N-2r^(5/4). All remaining sampled sets are different and pairwise intersect in at most one point, including across the two families. Both this event and the preceding all-flat concentration event hold simultaneously for sufficiently large r.

Append all r singletons again to the two retained families A,B. Every cross inner product is0 or1. Their intersection matrix contains the r-by-r identity on the singleton rows and columns, and its coordinate factorization has rank<=r. Therefore its exact rank is r; both coordinate families span R^r, so row and column strip ranks equal their coordinate-span dimensions. Deleting sets cannot increase a flat's count, and the denominator in either family is at least N-2r^(5/4)+r. Hence every rank<=d strip has mass at most
(2p_r N+d+r)/(N-2r^(5/4)+r)=O(r^(-1/8)).

A deterministic protocol sends Alice's at-most-c elements using c slots over labels0,...,r, padding with0; Bob computes the intersection and broadcasts its bit. Its cost is at most c ceil(log_2(r+1))+1=O(log^2 r). There are also exactly r positive disjoint all-one rectangles, one for each coordinate: overlap<=1 makes their supports disjoint, and rank r gives the matching lower bound. This family is thus especially easy for LR0.

It follows that no fixed positive constant can replace the quasipolynomial mass guarantee in L12 for all actual matrices. The r^(-1/8) upper control is still compatible with that unresolved guarantee. This is an infinite auxiliary obstruction to constant-mass concentration, not a legal log-rank reverse family and not a complete major result.

## L17 Existing two-level geometry is not a new whole-target premise

Kupavskii--Weltge2008.07153v1 already proves |A||B|<=(r+1)2^r for full spanning real configurations with every cross scalar product0/1. Its entire scalar-product theorem proof was actually read; the later polytope application was only partly exposed. Kupavskii--Tsarev2404.17933v1 already proves a sharp stability refinement. Only its introduction/statements/discussion and generalized conjecture were read, not its complete proof. Their cardinality bounds do not imply L12's weighted or uniform half-rank concentration.

Singer--Sudan2101.09592v5 supplies prior full-domain geometric/listability equivalences and explicitly excludes constant incidence density alone as a route. Its introduction, selected Section2 statements and Section5 cross-intersection discussion were actually read, not the full paper. In particular, the cross0/1 positive-overlap class of L16 is already known to have a polylog protocol; adjacent nonzero intersection values retain the still-open core. No existing vertex/facet or stability theorem is counted as our solution.

## L18 Same complete target, third active preservation

At06:13:24UTC the earlier2594effective seconds plus05:53:17-05:58:07(290seconds) and06:01:36-06:13:24(708seconds) total3592seconds,59m52. Preservation05:51:05-05:53:17 and recovery05:58:07-06:01:36 are excluded. This new preservation is excluded too. The explicit120minute same-stage policy remains active, with no authorized review-service pause. LR0 is unresolved here: no all-matrix uniform polylog protocol and no admissible superpolylog reverse family. All discovery processes ended. Continue the remaining effective hour after this safe save, without resetting or substituting the stronger-lemma control for the target.
