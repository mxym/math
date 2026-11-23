# A parity-reversing cyclic return cannot support nine active Conway squares

The [stronger eigen-equation test](active-square-nine-cycle.md) now excludes **every** return permutation in the one-cycle case. The shift-four control below survives only the weaker pairwise row tests in this note.

Use the [full root row](u226-full-root-row.md) at an edge of a hypothetical Conway graph. A square is active if it supports a true positive-charge (2,26) field of subtype c=0. The edge-chart exclusion below is independent of rank; the population corollary is for the specified rank-38 support only.

The live rank-38 support contained in \(\{018,024,226,230\}\) requires at least 2,910 positive-charge (2,26) fields and hence at least 1,455 active literal squares. Its latest published reduction forces an edge in at least nine active squares. I excluded a family of such edge charts. If the two mate matchings \(l,r\) on that edge's left and right wing indices form one alternating 12-cycle, the left-to-right-to-third return permutation \(\tau\) cannot be a parity-reversing automorphism of the index cycle. No assumptions on the third wing's mate matching or on automorphisms of the full graph are needed. This excludes a chart family, not the four-type support.

Number cycle positions modulo 12, with \(l\) pairing \(0,1\), \(2,3\), etc., and \(r\) pairing \(11,0\), \(1,2\), etc. Use the published shared-edge description for edge \(pz\) with cap \(a\). Index its square by \(i\), with other vertices \(w_i\) in the left wing and \(q_i\) in the right wing. The zero set at \(p\) is \(S_i=\{z\}\cup X_i\), where \(X_i\) is independent on the alternating cycle and contains \(i,i-2,i+2,\tau(i),\tau^{-1}(i)\). Once the first three are included, the remaining two sites must be distinct nonconsecutive choices in the five-site path \(i+4,\dots,i+8\). There are only six such pairs before the \(\tau\) constraints.

For a parity-reversing reflection \(\tau(i)=c-i\) with \(c\) odd, an active \(i\) requires \(c-2i\equiv\pm5\pmod{12}\), as those are the only allowed relative odd positions. At most four sites meet that requirement. For odd cyclic return shifts \(\pm1,\pm3\), no index is allowed. The two shifts \(\pm5\) are equivalent under reflecting indices by \(i\mapsto1-i\), which preserves each mate matching. With shift \(+5\), every active index has the uniquely prescribed \(X_i=\{i,i\pm2,i\pm5\}\). The simultaneous row check below then excludes nine indices.

### Exact row check excludes return shift five and has a shift-four control

Root at \(p\). Far sites have labels given by the 84 nonmate pairs of \(N(p)=\{z,a,w_0,\ldots,w_{11}\}\), where \(z,a\) are mates. The complete far-neighbor row of \(q_i\) for an active square is the union of the following three sets from the published charge-two dictionary.

- A perfect matching from \(S_i\) to its mate image, omitting any mate edge. Two of its pairs are fixed. They are \(\{z,w_{r(i)}\}\) and \(\{a,w_{\tau(i)}\}\), the literal near tags of the right-wing mate and third-wing cross neighbor.
- A two-edge perfect matching on \(X_i\setminus\{i\}\).
- Four pairs matching the mates of those four sites, two each, to the two sites in the omitted physical mate pair.

The first matching's four unspecified edges, three possibilities for the second matching and six allocations for the final four pairs generate all rows. For shift five this gives 198 candidate rows at each index. For distinct \(i,j\), the vertices \(q_i,q_j\) share exactly the near parent \(z\) among \(N(p)\). They are adjacent precisely when \(j=r(i)\). Thus two selected full far rows must intersect in zero labels for matched indices and exactly one otherwise.

The exact checker canonically lists nine selected indices up to the six even index rotations, which preserve \(l,r,\tau\) and all row tests. The quotient is of the necessary labeled row system and assumes no graph symmetry. Enforce pair compatibility by deleting any row without a compatible option at another selected index. Branch over every remaining choice for one index and repeat, with no cutoff. All 38 nine-index subsets are rejected for shift five, using 4,192 recursive nodes. Any larger compatible set would have a nine-index subset. For a control, shift four has the unique \(X_i=\{i,i\pm2,i\pm4\}\). The same check finds compatible rows at indices \(0,1,2,4,5,6,8,9,10\). That witness satisfies only the stated row constraints, so a subsequent proof must use new information to exclude that chart.

Run `node active_square_cyclic_wing_row_check.js 5` to verify the exclusion, or pass `4` for the pairwise-compatible control. The checker uses exact BigInt incidence masks. The control is not a graph completion.

### The live branch forces many heavily active edge and triangle charts

The same rank-38 population floor gives at least 5,820 square–edge incidences. Every edge has twelve possible square positions and belongs to a unique triangle. An edge with fewer than nine active squares contributes at most eight, so at least \((5820-8\cdot693)/4=69\) distinct edges have at least nine. Likewise triangle totals are at most 36, and their sum is at least 5,820. At least five triangles have total at least 26 since \(\lceil(5820-25\cdot231)/(36-25)\rceil=5\). At least 23 have total at least 25. These counts give multiple charts to which any eventual global geometry cap can apply. They do not force any of the charts to have the cyclic return treated above.

The population hypothesis is the [exact four-type window](norm18-rank38-four-window.md). Neither it nor the cyclic-return obstruction alone excludes the live support.
