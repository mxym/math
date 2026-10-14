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
