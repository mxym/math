# The sharp 60-point threshold for maximum sections of the binary norm circle in dimension 12

Let E=GF(4096), K=GF(64), and let S={0} union {z in E : z^65=1}. Sidon means that all sums of unordered pairs of distinct points are different. Equivalence is affine over GF(2).

**Theorem A.** Every Sidon set of at least 60 points in E containing a copy of a 40-point hyperplane section of S is contained in an affine image of S. For any fixed such input set of at least 60 points, the completion to a circle 66-set is unique. The universal threshold 60 is sharp: the explicit 59-set supplied here contains a maximum 40-section but is not contained in any copy of S.

**Theorem B.** Every Sidon set of at least 66 points containing a copy of any 38-point hyperplane section of S is an affine image of S. The 38 points determine the translation class of the opposite 28-set. Here uniqueness is up to a shear that fixes the section pointwise, not literal uniqueness from the 38 points alone.

Neither result classifies sets avoiding the prescribed sections or determines the unrestricted 12-dimensional maximum. For context, see Nagy's [conic completeness result, Theorem 2](https://doi.org/10.1016/j.jcta.2024.106001) and the [previous exact 40+26 result](https://github.com/mxym/math/commit/20ea96b13dd4ad1623c611e1926dfb15168d0ddf). That latter statement is also enough, together with the 59-point arithmetic below, to separate the 59 witness from every affine image of S.

## Constructing every anchored type

The program constructs GF(64) from X^6+X+1 and its quadratic extension from Y²+Y+32 (absolute trace of 32 is one). The encoding is a+64b for a+bY. It enumerates all 65 nonzero roots of X^65=1, adds zero, and checks all 2145 pair sums. Norm-one multiplication by a generator and Frobenius squaring preserve S and are checked binary-linear bijections on all 4096 elements. Their transposes permute character directions u; the two half sizes are (66±W(u))/2, where W(u)=sum_{x in S}(-1)^(u·x). The largest two half sizes are 40 and 38, and directions giving these sizes partition as follows (the orbit counts sum to 585 and 975 respectively):

| section size | orbit representatives u, signed Walsh values and orbit size |
|---|---|
| 40 | (6,+14,390), (17,-14,195) |
| 38 | (1,+10,390), (12,-10,130), (22,-10,390), (39,+10,65) |

The signs in this table may also be recovered by the verifier directly from S. For each such direction delete the least set bit position of u to identify both affine halves with V11, ordering the larger one first. Call its point set A and the known complement P (on the opposite side). Every A spans its half, and its own points plus its 3-point sums fill all 2048 locations; the verifier checks both facts. Thus no additional Sidon point lies in the anchored half. In the ambient coordinates (x,s) with s in {0,1} standard, the shear (x,s)↦(x+s·t,s) translates the opposite layer alone by any t in V11. In particular all translates of the planted P give actual copies of S.

## What the two exact engines decide

Let D(X) denote unordered distinct pair sums. An opposite layer B is compatible precisely if it is Sidon and D(B) is disjoint from D(A). Every 4-point collision either stays in one half or uses two points per half. Search operates in an additional internal half split V11=V10×{0,1}, labels chosen using a sign of the normal. Write A=(C,T) and B=(L,R). Translation puts the larger side L first. For target n, both solvers cover every k=|L| from ceil(n/2) to n, including empty R. In addition to L,R being Sidon, their internal difference sets must be pairwise disjoint and avoid D(C) union D(T), and (L+R) must avoid (C+T). These are sufficient as well as necessary.

Both solvers place a least internal difference d of L, in their respective orderings, at the unordered pair {0,d} by translation. At least one representation of every translate class survives, even with the side flip. The degree engine sorts vectors by degree in the initial compatibility graph (ties numeric), assigning each pair to its least difference by progressively removing forbidden edges. The other engine chooses the least *numeric* difference and rebuilds the graphs for each d. They take respectively the first and last maximizing internal hyperplane direction, usually different. They grow L while intersecting the available R pool with the complement of each translate of C+T. On adjoining l to L, the old triples u+v+l are forbidden in all later L choices. Greedily proper-colored candidate graphs bound clique sizes from above. The R search never assumes a greedy solution is maximum; it makes every feasible choice with the remaining internal differences and checks compatibility.

For n=20 the target is an **exotic** B, one not contained in any translate of P. Once L (including 0) is fixed, enumerate all possible t with L contained in P+t; t must itself belong to P in the centered coordinates. Two different translates of a Sidon set meet in at most two points (a nonzero t gives at most one unordered pair of that difference). Hence there is at most one such translate when |L|≥3. If every possible R candidate lies there too, prune; when R is complete discard it only if the entire B is actually contained. Applying the index transform to both P and B uses an affine choice of height origin; the family of all translates of P is unchanged by this convention. Both engines certify zero exotic B on each of the two anchors, in all eleven k ranges.

For n=28 with the 38-anchors, do not filter by P. Retain *all* compatible opposite layers, lifting each terminal into V12 and checking its pair sums. Store the lexicographically least sorted representative over translations that contain zero. Each of the four runs in either engine returns exactly the class of the explicitly constructed P, compared entry by entry.

## Deducing the threshold and its sharpness

If B is itself size 20 on a 40-anchor, it lies in one translate of P, and two such translates cannot both contain it. If |B|>20, any two 20-subsets differing in one point have 19 points in common, too many for distinct translates. The graph of 20-subsets joined by single exchanges is connected, so B lies in one P+t. For a set of at least 60, there are indeed at least 20 opposite points as A cannot grow in its own hyperplane. Conversely each eligible P+t gives a circle completion. Any arbitrary copy of S containing A similarly gives a compatible 26-set, so this also proves literal uniqueness of the completion *once the whole input set of at least 60 is fixed*. For n=28 and the 38-anchor, an alleged 29th opposite point would give two distinct 28-subsets intersecting in 27, impossible by the same argument because the planted translates have size 28.

For A indexed by u=17, take the explicit 19 positions in sharp19.txt on the opposite side. The program checks the 1711 pair sums in A union (2048+B) and enumerates all 2048 shifts of P: the largest overlap with B is 17. A circle copy containing the 59-set would provide a compatible 26-set; all such B are planted up to translation by the 20-subset result just proved (or the prior exact 40+26 computation). None contains these 19. This proves sharpness for the universal two-type assertion, not necessarily for each type separately.

## Replay

Python 3.10+; on x86-64 Linux use a GNU-compatible C++17 compiler (CXX or g++). Run `python3 -O run.py --quick` for the field, orbit, span, triple-coverage and sharp witness controls; `python3 -O run.py` compiles four programs from source and checks both full independent search passes. C++ assertions are mandatory; all Python correctness checks remain active even with -O. No network, external catalogue, or size bound in lower dimensions is used.

[Download the exact two-engine replay archive](Norm_circle_sections_sharp_threshold60_v2.zip) (17,793 bytes; SHA-256 `ccb4facb09a26cfb1fb2b581cf4f62d06f8a4fb989b5298c5abf2d1a13229101`). Both engines' twelve endpoint runs were completed in a fresh independent root replay, with the same scope and results. [Thornburgh's September 2026 bound](https://arxiv.org/abs/2609.27731) concerns a different dimension class, and does not address these dimension-12 anchored thresholds.
