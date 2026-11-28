# Exact randomness support for unicyclic multi-secret sharing

For every connected simple unicyclic graph \(G\ne C_3\) and every nonempty
binary input domain \(D\), this gives necessary and sufficient conditions
for a pointwise correct and individually perfectly private graph-CMSS
scheme, and its exact minimum dealer support. The support is
\(1,2,3,4\), or no scheme exists.

After the deterministic and one-bit tests, every cycle edge must touch a
degree-two active vertex whose secret is not already determined by a
neighbor's. Three dealer states are possible exactly when affine maps of
the three-element field, one possible switch per cycle vertex, close at
each input, with nonidentity translations at those degree-two vertices.
The test uses parity constraints and linear equations over
\(\mathbb F_3\) after a choice of reflection positions. A six-cycle with
three attached leaves shows that the reflection part cannot generally be
discarded. If the test fails, two uniform bits always suffice whenever
a scheme exists.

This extends the cycle case of the larger-graph direction in Piotr
Marszalik, arXiv:2610.10002v1 §V. The deterministic and one-bit criteria
specialize his known arbitrary-graph theorem; the new part is the
three-state classification and four-state bound for the unicyclic
family. It is not a classification of general cactus graphs, coalition
privacy, statistical privacy or minimum Shannon entropy.

Run **bash replay.sh** with Python 3 and sha256sum. The exact view-law
tests and independent group-product tests are finite checks of an
analytic proof.
