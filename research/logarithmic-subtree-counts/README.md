# A subcubic tree with a prescribed number of subtrees in logarithmic order

For every sufficiently large integer $k$, there is a connected tree of maximum degree three having exactly $k$ nonempty subtrees and at most $298\log_{17}k$ vertices. The logarithmic order is necessary; neither the factor 298 nor the enormous explicit sufficient cutoff is claimed to be best. The result does not classify small values for subcubic trees.

The main construction strings together blocks on a path. Each block carries a digit and one of two interchangeable branches. Switching the branch changes the total count by one, without changing how many subtrees can extend into the rest of the graph. A bound on gaps between digit words makes those one-unit changes sufficient to realize every target in consecutive intervals. This strengthens the polylogarithmic-size planar realization asked for in Chan–Pak's Conjecture 6.5, whose literal disconnected case also has a short star-forest proof. The earlier inverse theorem of Czabarka–Székely–Wagner already determines which counts occur in unrestricted trees.

* [Proof and explicit sufficient threshold](PROOF.md)
* [Consequence of the published cycle correspondence, including the multigraph convention](CYCLES.md)
* [Original formulations, previous results and search limits](SOURCES.md)
* [Independent internal review of the main proof](REVIEW.md)

To replay the checks with standard Python 3:

    python construct.py
    python replay.py
    sha256sum -c SHA256SUMS

The constructor produces a compact digit-and-switch description for a 191,233-bit test target at the first proven length, and checks its count exactly. It does not materialize a six-million-vertex graph. The separate replay does materialize and count 6,174 smaller graphs and checks exact carry identities. Expected outputs: [constructor](CONSTRUCT-CHECKS.txt), [independent replay](REPLAY-CHECKS.txt). None of the finite runs substitutes for the proof at unbounded word lengths.

Research note developed with AI assistance, including proof development, source checking and a separate internal proof and implementation review. Not externally peer reviewed; no claim of certified priority. The authors of prior results retain their attribution and third-party source rights.
