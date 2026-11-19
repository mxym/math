# Which numbers occur as cycle counts of simple 2-connected cubic graphs?

There are exactly **41** missing positive counts without a planarity restriction, the largest 115. Requiring planarity excludes **15 more**, the largest 131. The [proof](PROOF.md) lists all exceptions.

This is a computer-assisted completion of the analytic [construction for every count ≥2679](../simple-cubic-prescribed-cycle-count/README.md). It does not rely on the published finite occurrence tables. Against the literal lists of McCulloch, McKay, Salahshoori and Zaslavsky (§6), the general list gains 16 through 21; the planar list gains 42. The published Theorem 1 already excludes 16. Here the unique general graph with 42 cycles has ten vertices and contains a subdivision of K₃,₃. No conclusion is asserted for 3-connected graphs.

## Why the computation covers graphs of every order

Every simple 2-connected cubic graph can be built from a theta multigraph by inserting one ear at a time. Counts strictly increase. Exhausting every insertion that stays within a budget of 131, retaining intermediate parallel edges, eventually leaves no next generation. The run finishes at 28 vertices; 28 is an output, **not a postulated search cutoff**.

The census finds 351 simple representatives. Each has either a sphere-embedding certificate or explicit K₃,₃-subdivision certificate. Separately, 2,547 explicit planar graphs fill every count from 132 to 2678. A verifier checks all 2,898 graphs directly by traversing their binary cycle spaces and checking their complete edge lists and certificates. The largest middle-range witness has 26 vertices.

## Replay

On Linux with g++ (or clang++), Python 3.8+ and standard shell tools:

    sha256sum -c SHA256SUMS
    sh reproduce.sh

The script builds in a fresh temporary directory whose name it prints. The six small expected outputs are compared byte-for-byte. `GENERATED-SHA256SUMS` verifies the simple graphs, planarity certificates, middle-range recipes and full materialized witnesses, which are generated locally rather than bundled. The checker requires no third-party graph library. The two C++ sources use the GNU/Clang integer bit-count intrinsics.

Optional independent small-budget replay: `python3 check42.py`. This alternate search handles the range through 42, including the two places where the printed data differ; it does not certify larger counts by itself.

See [source comparisons](SOURCES.md) and the [independent internal review](REVIEW.md). This note was developed and audited with AI assistance. An internal audit is not external peer review; no publication-priority guarantee is made.
