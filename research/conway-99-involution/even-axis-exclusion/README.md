# A computer-assisted exclusion of involutions in Conway's 99-graph

**Theorem.** If a strongly regular graph with parameters (99,14,1,2) exists, it has no automorphism of order two. This does **not** settle Conway's 99-graph existence problem. The result uses earlier work, including the signed 7-rank bound and unsigned simplex/Hamming representation, followed by a finite search whose inputs, sources and exhaustive computation records are supplied here. See Prior.md and Reduction.md for prerequisites and attribution.

At least one vertex of an auxiliary graph on seven vertices has even degree. A putative involution therefore gives an even-degree central chart. All **3,156** high-rank chart/parity/mode alternatives fail directly, without transferring results between parities. The lower ranks are covered by a separately frozen proof (88 live lower-rank chart-parities of even degree). No maximum-degree theorem is used.

| Degree of chosen axis | Direct high-rank jobs | Remaining |
|---:|---:|---:|
| 0 | 2 | 0 |
| 2 | 4 | 0 |
| 4 | 72 | 0 |
| 6 | 3,078 | 0 |

The 3,156 entries include two global residual-anchor modes at local rank 10, one at rank 11. EvenCoverage.tsv covers all raw even charts in both parities (6,414 orientation entries before this mode split), whether rejected by physical caps, the unary 12-word stage, the lower-rank theorem, or exhaustive high-rank search. The standalone audit.py recomputes the mod-7 rank of all 3,580 ordered-matching charts independently, rebuilds each 39-point graph literally, and checks all terminal records. Audit.txt is its concise output.

## Verification

GCC 14.2, C++17 and Python 3.10+; no solver, download or network. From this directory:

    python3 -B replay.py audit
    JOBS=2 python3 -B replay.py quick
    FULL_LOW=1 JOBS=4 python3 -B replay.py full
    JOBS=4 python3 -B replay.py uniform

- **audit** verifies checksums, the inputs and every scope, including the lower-rank archive ledger; it does not rerun the searches.
- **quick** independently regenerates the catalogue, GL(4,2) action, all finite-field first-vector orbits and Boolean dot masks, literal graph checks and the final six direct searches (924 normalized stars). It compares every one of the 1,166,592 raw star embeddings of the six final chart-parities with the union of the full orbits of those 924 representatives: #0 422,400 raw to 42 representatives per parity; #1 and #11 each 80,448 raw to 210 per parity. Finally it exercises a separately written scalar terminal solver with no first-vector symmetry, no bitset products, and common neighbors counted in the literal 43-vertex graph. A real chart survives this weaker test at depths 1 and 2, failing at 3 and 8.
- **full** reproduces every archived base and stronger search, including all 3,050 original baseline rows with the guard removed, plus all 286 contiguous strong blocks directly closing the other 106 jobs. No timeout counts. Set FULL_LOW=1 to recompute all previous lower-rank cases too. Recorded CPU seconds are informational only; all arithmetic decisions are integral.
- **uniform** repeats all 3,156 high-rank cases under one stronger algorithm, without a nonzero node limit, a parity transfer, or the archival ranges as a stopping point. This is an alternate replay, not a claim of an entirely independent solver.

Each strong log has half-open range [lo,hi) and checked=outer−lo. A limited block checks hi−lo assignments, but cannot close a chart. A valid chain starts at zero, consists of contiguous limited blocks, and ends with limited=0 (natural exhaustion), open=0, truncated=0. Initial searches that exhausted before their optional 20,000-node guard have open=0 and truncated=0; full replay removes the guard and compares every non-timing field.

Prerequisites: [signed 7-adic restriction](https://github.com/mxym/math/tree/main/research/conway-99-involution/seven), [unsigned simplex/Hamming representation](https://github.com/mxym/math/tree/main/research/conway-99-involution/unsigned-simplex). The low-rank algorithm, controls and full search traces are in prerequisites/Conway99_Involution_SimplexLowRanks.zip (SHA-256 9469414f1d94d6a55f3071a226873c44691f91eb82bd27a65c022c6f54783eb8). [Makhnev–Minakova Theorem 1](https://doi.org/10.4213/dm144) reduces an arbitrary involution to the one-fixed-vertex case.

For restartable uniform verification, run python3 -B uniform-shards.py prepare OUT N with a fresh output directory. For each j=0,…,N−1 run python3 -B uniform-shards.py run OUT j; these can run in parallel. Finally, python3 -B uniform-shards.py check OUT verifies the union of all 3,156 required keys. Recorded CPU timings only influence load balancing, never eligibility or pruning.

Optional stronger cross-check: JOBS=2 python3 -B replay.py terminal runs all 924 final stars using the alternate scalar implementation, with every F7 vector retained on the first outside label, literal 43-point common neighbors, and no real-pair Cauchy constraint. This command is available independently of whether a particular release includes a finished alternate transcript. The main proof uses the exhaustive direct searches recorded in the archive plus verified orbit coverage.


## Download

[Exact replay archive](Conway99_NoInvolution_EvenAxis_Exact.zip) (302,052 bytes). SHA-256: `d1e96df2669067e103d2c82d7345b1c3f2c3d9666eb1b8c5ea45292005b8b07a`.

[Completed alternate terminal transcript](AlternateTerminal.tsv): a second scalar implementation, with no first-outside-vector symmetry or real pairwise Cauchy cut and with literal common-neighbor counts, has now rejected all 924 normalized stars in the six degree-0 and degree-2 scopes. The 62 rows are contiguous half-open blocks within each chart/parity; the last block in each scope exhausts naturally. This supplements the exact direct search and full-orbit coverage already in the archive. It is not an independent rerun of all 3,156 high-rank cases.

[Completed uniform high-rank replay](Conway99_NoInvolution_UniformReplay.zip) (37,540 bytes, SHA-256 `01fdafd039c9b1fe39d464fce9492c83c6faa5745cd95bee50ec5921d4de8f2a`): all 3,156 required keys reran from the first candidate under one uncapped algorithm, without using the archived split ranges. The three shards exhausted all 446,227 normalized anchors and returned zero relaxed cliques. This is a separate completed execution with one uniform search procedure, not an independently designed solver for all 3,156 cases. To check the transcript, use the proof archive's `uniform-shards.py prepare OUT 3`, unpack these three TSVs into `OUT`, and run `uniform-shards.py check OUT`.
