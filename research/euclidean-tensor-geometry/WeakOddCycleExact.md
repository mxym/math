# Exact graph-tensor exponents for odd cycles with a weak edge

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

For a log-weighted odd cycle of any length, suppose one edge has weight \(t\) and every other edge has weight at least \(2t\). Over any field, the asymptotic rank exponent is exactly the sum of the weights of all other edges. In particular a weighted five-cycle with four unit edges and one edge of weight at most \(1/2\) has exponent 4. This does not settle the unweighted five-cycle.

More generally let a weighted graph have a cut \(S\mid T\). Suppose each internal edge \(uv\), of weight \(w_{uv}\), can have that amount of demand routed along one or more paths from \(u\) to \(v\), all of whose edges cross \(S\mid T\). Assume the total amount routed on every crossing edge \(e\) is at most \(w_e/2\). Then the asymptotic rank exponent equals the cut weight; the cut is consequently a maximum cut. The statement uses the log-weight model of Zhou; rational weights can always be realized after common scaling.

## Proof

The flattening gives the cut lower bound. For the upper bound use [Zhou, Theorem 5.6](https://arxiv.org/html/2610.34273v3#S5.SS3): its upper program ranges over nonnegative symmetric zero-diagonal \(P\), with \(J-2P\) copositive and \(P\) satisfying triangle inequalities. The two-point test with equal weights gives \(P_{uv}\le1\). The three-point test on \(u,v,w\) with weights \((1,2,1)\) gives
\[
 2P_{uv}+2P_{vw}+P_{uw}\le4,\qquad
 P_{uw}\le2[(1-P_{uv})+(1-P_{vw})].
\]
An internal edge has endpoints on the same side, so its route has even length. Chain the triangle inequalities along its consecutive two-edge segments. Its \(P_{uv}\) is at most \(2\sum_{e\text{ along route}}(1-P_e)\). Multiply by the routed amount and add across every route. The half-capacity hypothesis and \(1-P_e\ge0\) bound the total internal-edge objective by \(\sum_{e\text{ crossing}}w_e(1-P_e)\). Adding the crossing objective leaves at most \(\sum_{e\text{ crossing}}w_e\), giving equality.

For the odd cycle, the complementary path of the distinguished edge has even length. Take the alternating cut along that path and route the entire demand \(t\) around it. The hypothesis is exactly the stated half-capacity condition.

The [workbench](../../tools/tensor-bounds/) encodes and replays this upper certificate; its greedy routing is only a sufficient search procedure, not a decision algorithm for exact rank.
