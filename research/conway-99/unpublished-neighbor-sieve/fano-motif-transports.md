# Fano translations of edges, triangles, and induced three-site paths

For any Conway graph and signed original seven-class β, write C_{a,t}(β) for the literal fields of that charge and cost in the class (no division by eight). Let F(β)=C_{0,14}(β), and M(β)=C_{2,22}(β) count the signed Fano fields and the negative indicators of Hoffman cocliques, respectively. The following hold without Seidel rank or rootlessness hypotheses:

    C_{2,36}(β) ≥ 693 [β=0] + 70 F(β),
    C_{3,39}(β) ≥ 231 [β=0] + 21 F(β) + 22 M(β),
    C_{3,53}(β) ≥ 8316 [β=0] + 1134 F(β),
    C_{0,42}(β) ≥ 8316 [β=0] + 1050 F(β).

The same formulas hold in each maximal extension with its own signed residual classes. In particular the rank-44 scalar coefficients in the original lattice and each extension separately satisfy

    Y₂ ≥ 462 + 42 F(0) + 44 M(0) + C_{0,28}(0),
    Y₃ ≥ 24948 + 3318 F(0).

At each of these coefficients, (0, t) and (3, t+11) are the actual two charge species; the latter is counted twice because charge signs differ. Only one of the several previously known Y₃ floors is refined here. The inequalities concern true fields; they are not a rank exclusion.

**Mark families and separation.** Write d_i=(3I−A)e_i, and use ordinary unit-coefficient combinations (edge sum, triangle sum, induced-P3 sum, or oriented nonedge difference d_i−d_j). All have trivial seven class, independently of their charge. Their squared norms are 36, 39, 53 and 42, respectively, because for an integer vector λ of total charge a,

    ||Σ λ_i d_i||² = 21Σ_i λ_i² + 2a² − 14Σ_{ij∈E} λ_i λ_j.

Within each of the four families distinct graph labels give marks at squared distance at least 42. For two equal-size additive subsets, cancel their intersection to leave s≤3 sites of each sign. For s=1 the bound is 42, for s=2 it is 84−28=56, and for s=3 the two triangles or paths contribute at most six internal edges, giving 126−84=42. Opposite signs across the two supports only increase the distance. For two different oriented nonedges, cancellation gives either a usual one- or two-site balanced difference, or a repeated coefficient ±2. In the latter case, if λ consists of (2,−1,−1), then the two negative endpoints have at most one edge, so the norm is ≥126−14=112; the pattern (2,−2) is ≥168. The same bounds cover the sign reversals. Thus the four base cardinalities are exactly 693 edges, 231 triangles, 99·(binom(14,2)−7)=8316 induced P3s, and 99·84=8316 oriented nonedges.

**Switch and collision.** For each signed norm-14 field f, and each base mark m whose site-weight sum against f is −1, output m+f; its norm stays unchanged because (m,f)=−7. It has signed seven-class [f], and f·(m+f)=7. No output is a base mark (distance 14 <42). If m+f=m′+g from unequal oriented Fanos, distinct Fano lines have |f·g|≤4 (at most two shared sites in each equal-sign shore by Fano completion; see the Fano palette bound). Then ||m−m′||²=||f−g||²≤36, hence m=m′ and f=g. When g=−f both outputs would have to pair positively with opposite oriented Fanos, impossible. This proves simultaneous injectivity without assuming that roots form an orthogonal set.

**Counts for each fixed oriented f.** Write Fano sign shores P,N (7 each), Z the 15 anticomplete sites and H the 70 other vertices, each seeing one vertex in each sign. The shores are independent, with four opposite-sign neighbors at each signed vertex. There are 70 edges from N to H, all the edges of site-sum −1; no edge sum ±2 is possible. The 28 N-P edges each have their unique cap in H. Of the 70 N-H edges, 28 are in such capped triangles, and the remaining 42 come in pairs in triangles N-H-H; so exactly 21 triangles have sign-sum −1. Reflecting the argument yields symmetric numbers for +1.

No induced P3 has sign-sum ±2 or ±3: two sites of the same Fano sign are nonadjacent and have both common neighbors in the opposite sign of f; three same-sign sites cannot be a P3. The number of paths containing a fixed vertex is 252 (uniformly by regularity and triangle counts); an adjacent pair occurs in 24 paths, and a nonadjacent one in two. Thus the sum of squared P3 sign-sums is

    252·14 + 2(24·(−28)+2·21)=2268,

where Σ_edges f_if_j=−28 and Σ_nonedges f_if_j=21. The total linear sum is 252Σ f_i=0, so exactly 1134 have sum −1. For ordered nonedges with f_i−f_j=−1 the possibilities are i∈N,j∈Z∪H or i∈Z∪H,j∈P, totaling 2(7·85−70)=1050. We omit sign-difference ±2; those do not enter this unit-shift argument.

The additional coclique outputs in C_{3,39} are b+d_i for b=−1_C and i∈C, recognizable by their unique +2 at i. An ordinary triangle mark has no +2. A translated triangle with sign-sum −1 contains no P vertex, so on P the original mark is ≤0 and addition of f cannot make a +2; anywhere else the original mark is ≤1 and f≤0. This gives the claimed disjoint sum. No assertion of additivity with other noncanonical auxiliary families is made.
