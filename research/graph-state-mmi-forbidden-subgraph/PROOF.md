# A forbidden-subgraph theorem for graph-state monogamy

Yongxian Zhang (张永贤)  
School of Computer Science and Engineering, South China University of Technology  
mxymmxym1@gmail.com · ORCID 0009-0000-3864-3536  
9 October 2026

## 1. Exact statements

All graphs below are finite, simple, and undirected. A **claw** is the four-vertex star `K_{1,3}`. Local complementation at `v`, denoted `G*v`, toggles edges between distinct neighbors of `v` and changes no other edges. A vertex-minor is an induced subgraph of a graph obtained by a finite sequence of local complementations. This agrees with allowing local complementations and vertex deletions in any order.

Write `R_1=K_1`, `R_2=K_2`, `R_3=P_3`, `R_4=P_4`, `R_5=C_5`, and `R_6=W_5`, where **`W_5` here has six vertices**, a five-cycle and its universal hub. Equivalence to a representative permits graph isomorphism as well as local complementation.

**Theorem 1 (complete component classification).** A graph has no claw vertex-minor if and only if each nonempty connected component is locally equivalent, up to isomorphism, to one of `R_1,...,R_6`.

**Theorem 2 (forbidden-subgraph implication).** For every qubit graph state and every three pairwise disjoint subsystems `A,B,C`, if

`I_3(A:B:C) = S(A)+S(B)+S(C)-S(AB)-S(AC)-S(BC)+S(ABC) > 0`,

then the graph has a locally equivalent representative containing an **induced** claw. Here `S` is von Neumann entropy in bits. This proves the implication in Fuentes–Keeler–Munizzi–Pollack, arXiv:2511.19585v1, Conjecture 1, without a bound on graph order.

**Corollary 3 (sharp connected-size threshold).** Every connected graph on at least seven vertices has a claw vertex-minor. Six does not suffice, because `W_5` has no claw vertex-minor. For the positive direction one can use at most eight local complementations, whose pivot vertices lie in a connected set of at most seven vertices, and then delete unwanted vertices. In the graph-state interpretation, local Clifford gates followed by local computational-basis measurements and Pauli corrections extract a four-qubit GHZ state on some four vertices. This is not a claim about four prescribed vertices or about general non-Clifford local operations.

The proof has a small finite certificate, **not** a finite-size extrapolation. The sole structural finite step checks all 120 nonempty one-vertex extensions of the six representatives. A connected-graph induction proves that these cases cover arbitrary order.

## 2. Local-complementation lemmas

**Restriction.** If `v` belongs to a vertex subset `U`, then `(G*v)[U] = (G[U])*v`. For two vertices in `U`, whether their edge is toggled depends only on their adjacencies to `v`, all of which are in `G[U]`. Repeating this identity lifts any local-complementation sequence on an induced subgraph to the full graph, with precisely the same restricted result.

Consequently, vertex deletions can be postponed until the end of a sequence: continue applying all later local complementations on the original vertex set, and finally restrict to the vertices that were not deleted. At each step the restriction agrees. In particular, having a claw vertex-minor is inherited upward from induced subgraphs and is invariant under local equivalence and isomorphism.

**Connectedness.** Local complementation preserves each connected component, including its vertex set. It creates no edge between distinct components. Any deleted edge `xy` had both ends adjacent to the pivot `v`, so it is replaced, as a connectivity witness, by the path `x-v-y`; these incident edges are unchanged. The inverse operation is the same local complementation.

**Removable vertex.** A finite connected graph with at least two vertices has a vertex whose deletion leaves a connected graph. Take a spanning tree and delete any leaf of that tree; the remaining tree spans all remaining vertices.

**Relabeling.** Relabeling a graph transports a local complementation at `v` to local complementation at the relabeled vertex. Therefore no relabeling is an extra physical or graph operation in a lifted witness: it only changes how the next witness's vertex names are interpreted.

## 3. The finite extension certificate

Represent a labeled graph on `0,...,m-1` by the integer adjacency rows `a_i`, whose `j`-th bit is one exactly when `i` is adjacent to `j`. The six fixed representatives are:

| m | Representative | Adjacency rows |
|---|---|---|
|1|K_1|0|
|2|K_2|2, 1|
|3|P_3|2, 5, 2|
|4|P_4|2, 5, 10, 4|
|5|C_5|18, 5, 10, 20, 9|
|6|W_5|50, 37, 42, 52, 41, 31|

For every `m=1,...,6` and `1 <= b < 2^m`, add vertex `m` with adjacency set given by the binary digits of `b`. These are **all** nonempty attachment sets. The corresponding entry of `certificate.json` supplies either:

* a list of local-complementation vertices and an ordered tuple `(center,leaf_1,leaf_2,leaf_3)` inducing a claw afterward; or
* a list of local-complementation vertices and an explicit bijection from `R_{m+1}` to the entire resulting graph.

There is no latter outcome at `m=6`. All lists have length at most three.

| Base order | All attachments | Claw endpoints | R_(m+1) endpoints | Maximum LC length to a claw | Maximum LC length to R_(m+1) |
|---|---:|---:|---:|---:|---:|
|1|1|0|1|—|0|
|2|3|0|3|—|1|
|3|7|1|6|0|3|
|4|15|11|4|2|2|
|5|31|30|1|1|0|
|6|63|63|0|2|—|
|Total|120|105|15|2|3|

This table's role is fully specified by the following verifier, expressed mathematically. For each pair `(m,b)` in the indicated range, start with the fixed extension. For each pivot `v`, and each row `i`, replace `a_i` by `a_i XOR (a_v XOR 2^i)` if the `i`-th bit of `a_v` is one; otherwise retain `a_i`. Use the old pivot row throughout a step. At a claw endpoint verify all three center–leaf adjacencies and all three leaf–leaf nonadjacencies. At a representative endpoint verify that the supplied list is a permutation and compare every matrix entry under that permutation. Finally require each pair `(m,b)` exactly once. The scripts use explicit exceptions rather than assertions; optimized Python does not remove checks.

`check_certificate.py` implements this rule with binary rows. `verify_independent.py` implements local complementation using symmetric differences of edge sets, generates attachments as subsets rather than integer intervals, and compares endpoint edge sets. Neither imports the generator or the other verifier. The witness generator is optional and is not a trusted proof input.

## 4. Proof of the classification: the unbounded step

Suppose a connected nonempty graph `G` has no claw vertex-minor. Induct on its number `n` of vertices. The case `n=1` is `R_1`. For `n>=2`, choose a removable vertex `w`, and put `H=G-w`. The graph `H` is connected and has no claw vertex-minor. By induction it is locally equivalent, up to isomorphism, to `R_m` for some `1<=m<=6`; necessarily `m=n-1`.

Lift the sequence for `H` to `G` and relabel the remaining vertices as `0,...,m-1`, with `w` labeled `m`. The resulting full graph is connected, so the attachment set of `w` to `R_m` is nonempty. It is exactly one of the 120 certified extensions. A claw endpoint would contradict the hypothesis. Hence the endpoint is `R_{m+1}`, proving the induction. In particular `m=6` is impossible, and no connected graph of order at least seven avoids a claw vertex-minor.

The converse requires showing that none of the six representatives has a claw in its LC orbit. We give a short spectral proof in Section 6. An independent finite negative certificate is also supplied: `certificate.json` contains LC-closed claw-free sets of sizes `1,1,4,11,132,132`, each containing its representative. Closure entails that every graph in the entire LC orbit is in the certified set. The independent verifier regenerates the full orbits without using their supplied contents and obtains exactly the same sets. There are 281 states and 1511 one-step closure checks in total.

Local complementation acts separately on components. An induced claw is connected, so it cannot use different components. The connected classification therefore gives Theorem 1 for arbitrary graphs, including the empty graph, for which the assertion is vacuous.

For Corollary 3, take a connected induced subgraph on seven vertices, obtained by growing a connected set one vertex at a time. Apply the extension normalization to this graph. The maximum costs for successful normalizations through orders two to six are `0,1,3,2,0`, and the final claw witness costs at most two. The total is at most eight. An earlier claw outcome costs no more. Lift the sequence to the original graph before deleting the unwanted vertices. The negative six-vertex example follows from the converse just proved.

## 5. The graph-state entropy identity, with proof

For a graph `G=(V,E)` on `n` vertices define

`|G> = 2^(-n/2) sum_(x in F_2^V) (-1)^(sum_{uv in E} x_u x_v) |x>`.

For `X subset V`, let `B = Gamma[X,V\X]`, and write `r_G(X)=rank_(F_2)(B)`. Then

`S(X) = r_G(X)`.

To see this, write the exponent as `q_X(x)+q_Y(y)+x^T B y`. The partial trace has entries

`rho_X(x,x') = 2^(-|X|) (-1)^(q_X(x)+q_X(x')) 1_{B^T(x+x')=0}`.

Indeed, the sum of a binary additive character over `F_2^Y` is zero unless that character is trivial. Conjugating by the diagonal matrix with entries `(-1)^{q_X(x)}` removes the signs. If `K=ker(B^T)`, the remaining matrix has one all-ones block for each coset of `K`, each multiplied by `2^(-|X|)`. Every block has size `2^(|X|-r)`. Thus the nonzero eigenvalues are `2^(-r)` with multiplicity `2^r`, proving the identity, also for empty subsystems and zero rank.

Cut rank is invariant under local complementation. If the pivot `v` lies in `X`, its row in `B` stays fixed, and every row indexed by a neighbor of `v` in `X` acquires that fixed row. These elementary binary row additions preserve rank. If the pivot is outside `X`, apply the analogous column operations. Symmetry of the adjacency matrix gives `r_G(X)=r_G(V\X)`.

For completeness, the graph operation really is a local Clifford operation. Let `K_u=X_u product_{w in N(u)} Z_w` be the graph stabilizers and put

`U_v = exp(-i pi X_v/4) product_{u in N(v)} exp(i pi Z_u/4)`.

Conjugation preserves `K_v`; it maps `K_u` for a neighbor `u` to `K'_u K'_v`, where primes denote the stabilizers of `G*v`, and fixes the generators of nonneighbors. These identities follow from `X Z=-iY`, `Z X=iY` and quarter-turn Pauli conjugation. Both sets generate the same stabilizer group after the change of generators. The independent graph stabilizers have a unique joint +1 state, so `U_v|G>` and `|G*v>` differ only by a global phase. This is the standard local-complementation rule; see Van den Nest–Dehaene–De Moor (2004).

## 6. Exact cut profiles and exclusion of the claw

For `P_4`, every one-vertex cut has rank one. The three unordered two-versus-two cuts have ranks `1,2,2`: representatives are `{0,1}`, `{0,2}`, `{0,3}`. The corresponding matrices, with complement columns in increasing order, are respectively

`[[0,0],[1,0]], [[1,0],[1,1]], [[1,0],[0,1]]`.

For `C_5`, every pair has cut rank two. By the cycle symmetries it suffices to check an adjacent pair and a nonadjacent pair, for example `{0,1}` and `{0,2}`. Their matrices are

`[[0,0,1],[1,0,0]]` and `[[1,0,1],[1,1,0]]`.

Together with nonzero single-vertex cuts and complementation, this proves

`r_(C_5)(X)=min(|X|,5-|X|)`.

For `W_5`, every three-vertex cut has rank three. Every such cut has one side consisting of the hub and two cycle vertices. Up to the cycle symmetries, choose `{5,0,1}` or `{5,0,2}`; with hub row first, the matrices are

`[[1,1,1],[0,0,1],[1,0,0]]` and `[[1,1,1],[1,0,1],[1,1,0]]`.

Both have odd determinant. Full row rank of these three-vertex cuts implies full row rank for smaller subsets: extend the subset to three vertices and restrict the independent rows of that three-vertex cut. Complementation gives

`r_(W_5)(X)=min(|X|,6-|X|)`.

The first three representatives cannot contain a four-vertex induced subgraph. A graph locally equivalent to `P_4` cannot be a claw because a claw has rank one at every two-versus-two cut, whereas `P_4` does not.

Now consider any graph locally equivalent to `C_5`. All its two-vertex cut ranks are two. It consequently has minimum degree at least two: if a vertex had degree zero or one, place it with its possible neighbor in a two-vertex subset; its cut row is zero. If an induced claw existed, each of its three leaves would have to be adjacent to the sole vertex outside the claw. Any two leaves would then have identical cut rows, contradicting rank two.

Similarly, every graph locally equivalent to `W_5` has minimum degree at least three: a vertex of degree at most two, together with its neighbors and any needed padding, forms a three-vertex subset with a zero cut row. In an induced claw, every leaf would therefore have to be adjacent to both outside vertices. Again two leaves have identical cut rows, contradicting the rank-two profile. This proves the converse in Theorem 1 without relying on an orbit enumeration.

## 7. All partitions and the monogamy theorem

Let `D=V\(A union B union C)`, and use purity to write

`I_3 = r(A)+r(B)+r(C)+r(D)-r(AB)-r(AC)-r(AD)`.

This expression is symmetric in the four blocks, because complementary cuts have equal rank. If any block is empty, the expression is zero. Thus components on at most three vertices always contribute zero.

For `P_4`, a four-nonempty-block partition has four singleton blocks. The value is `4-(1+2+2)=-1`. For `C_5`, the only possible positive block-size profile is `(2,1,1,1)`, giving `5-(2+2+2)=-1`. For `W_5`, the positive profiles are `(3,1,1,1)` and `(2,2,1,1)`, giving respectively `6-(2+2+2)=0` and `6-(2+3+3)=-2`.

For a disjoint union, every cut matrix is block diagonal after row and column permutations, so ranks, and hence `I_3`, add over components. Therefore a graph with no claw vertex-minor satisfies every MMI inequality. Taking the contrapositive proves Theorem 2.

More precisely, for any claw-vertex-minor-free graph and any four-block partition,

`I_3 = -N_4 - N_5 - 2 N_6`,

where `N_4` counts four-vertex components meeting all four blocks, `N_5` counts five-vertex components meeting all four blocks, and `N_6` counts six-vertex components whose block-size profile is `(2,2,1,1)`. This also completely describes all equality cases **within the classified claw-vertex-minor-free class**. It is not an equality classification of all graph-state MMI instances.

## 8. Scope, provenance, and independent verification

The original conjecture is from Fuentes, Keeler, Munizzi and Pollack, *Monogamy of Mutual Information in Graph States*, arXiv:2511.19585v1, Conjecture 1 (printed p.30). The source discusses a necessary induced four-star somewhere in the local-Clifford orbit, not an induced star in every representative. We prove exactly this implication. Its additional generalized-star partition statement follows explicitly: take I, J and K to be the three singleton leaves of the induced claw and take C to be every other vertex, including the center. The three leaf blocks have no edges between them and each is attached to C, as required by the source definition.

The converse is not claimed. Claw vertex-minors concern what can be obtained after deletions/measurements; those operations do not preserve the original entropy vector. Nor do these results characterize all MMI-satisfying graph states, handle arbitrary mixed or non-stabilizer states, extend to odd-prime qudit graphs, or solve other holographic entropy inequalities.

The finite LC and cut-rank tables for small graph states overlap the established graph-state classification literature; those small states themselves are not new. Our proof uses a complete extension induction and explicit small witnesses rather than assuming an unrestricted conclusion from a finite catalog. A bounded literature search did not locate this exact implication's resolution, but this is **not** evidence sufficient to assert historical priority. The separate 2026 paper on edgeless vertex-minor Ramsey numbers concerns a different target graph and is not an input to this proof.

Both exact checkers pass all 120 extensions. They also check all 5460 assignments of representative vertices to four labeled blocks, including empty blocks. The independent checker recomputes every orbit and independently constructs the graph-state amplitudes: for all 126 representative cuts it verifies, by integer matrix multiplication, the reduced-density numerator identity `M^2=2^(n-r) M` and `tr(M)=2^n`. These finite quantum checks supplement, rather than replace, the all-order entropy proof in Section 5.

This is AI-assisted research. No external funding was received. No external human peer review is claimed. Lean coverage, if supplied in a later companion, must be stated separately; the present theorem is a complete written proof with exact independently replayable finite certificates, not a claim of complete Lean verification.

## References

1. J. Fuentes, C. Keeler, W. Munizzi and J. Pollack, *Monogamy of Mutual Information in Graph States*, arXiv:2511.19585v1 (2025), especially Conjecture 1.
2. M. Van den Nest, J. Dehaene and B. De Moor, *Graphical description of the action of local Clifford transformations on graph states*, Physical Review A **69**, 022316 (2004), DOI 10.1103/PhysRevA.69.022316.
3. M. Hein, J. Eisert and H. J. Briegel, *Multiparty entanglement in graph states*, Physical Review A **69**, 062311 (2004), DOI 10.1103/PhysRevA.69.062311.
4. J. de Jong, F. Hahn, N. Tcholtchev, M. Hauswirth and A. Pappa, *Extracting GHZ states from linear cluster states*, Physical Review Research **6**, 013330 (2024), DOI 10.1103/PhysRevResearch.6.013330. This is prior work on the path family, not an input to our arbitrary-connected-graph classification.
5. J. H. Bae, *Vertex-minor Ramsey numbers: exact values and extremal structure*, arXiv:2604.13434v1 (2026). Its edgeless target is distinct from our connected claw target; none of its computational claims is assumed here.
