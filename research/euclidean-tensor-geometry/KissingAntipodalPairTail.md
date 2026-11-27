# One more pair deficit by controlling the two rows of a near-antipode

**Theorem.** A six-dimensional kissing configuration with at least 28 antipodal pairs has at most 72 points. A seven-dimensional kissing configuration with at least 55 antipodal pairs has at most 126 points. This extends the [previous pair-deficit bounds](KissingAntipodalPairsSixSeven.md) by one and does not improve the unrestricted upper bounds. In particular a larger code must have at least 19 unpaired points.

Use the notation in the preceding note: \(P=36\) or \(63\), \(p\) true antipodal pairs, and a graph on singletons with an edge for an inner product below \(-1/2\). Only \(p=P-8\) remains, since the previous theorem deals with higher pair counts. In a hypothetical larger code, retain \(q=17\) singletons together with the true pairs. The singleton graph is triangle-free and has independence number at most eight, hence maximum degree eight. The minimum degree is at least two: adding the antipode of a degree-zero or degree-one vertex and dropping its negative neighbor, if present, would retain at least \(2P+1\) points and yield \(P-7\) true pairs, contradicting the previous theorem.

Use the same odd-corrected positive kernel used there for deficit seven,
\[
 F(u)=u^4-u^2/4+(49/100)u(u^2-1/4)+(9/500)u .
\]
The weighted harmonic inequality (weight one half for each member of a true antipodal pair, and \(8/17\) for each singleton) requires average ordered off-diagonal singleton row energy at least
\[
 T=\tfrac34(1+1/8-49/100)-9/500=1833/4000.
\]
The nonedge bound \(F(u)\le9/1000\) for \(|u|\le1/2\) is unchanged.

## Match the strongly negative edges

For adjacent singleton vertices \(x,y\) write \(a=-x\cdot y\). Call the edge high if \(a\ge978/1000\). High edges form a matching: if \(x\) had two such neighbors, \((-x)\cdot(y+z)\ge 2(978/1000)>\sqrt3\), but \(\|y+z\|\le\sqrt3\) follows from the kissing inequality. A high edge is medium when \(a<985/1000\), and strong otherwise.

The companion [verify-kissing-antipodal-pair-tail.js](verify-kissing-antipodal-pair-tail.js) gives the following upper bounds on the sum of \(F(x\cdot y)\) over graph neighbors of one vertex, in units of \(1/1000\):

| Degree | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|---:|---:|
| No restriction | 356 | 347 | 350 | 358 | 367 | 377 | 386 |
| No high edge | 332 | 340 | 350 | 358 | 367 | 377 | 386 |
| Medium high edge | 340 | 347 | 350 | 358 | 367 | 377 | 386 |

These are the exact Gram box verifications from the preceding note, with upper endpoints rounded *up* on the dyadic grid for the two capped cases. Thus every unmatched vertex has row upper bound strictly below \(T\) after adding \(9/1000\) for each nonedge.

For a matched high edge \(xy\), consider a vertex \(z\) that is nonadjacent to both endpoints. If \(t=x\cdot z,u=y\cdot z\), then \(|t|,|u|\le1/2\) and
\[
 |t+u|\le\|x+y\|=\sqrt{2(1-a)}
 \le \begin{cases}21/100&\text{medium},\\7/40&\text{strong}.\end{cases}
\]
An exact two-variable dyadic check gives \(F(t)+F(u)\le157/10000\) in the medium band and \(F(t)+F(u)\le140/10000\) in the strong band. Relative to \(2(9/1000)\) this saves \(23/10000\) or \(40/10000\) on the two rows for each common nonneighbor. The check branches over \([-1/2,1/2]^2\), rejects boxes disjoint from the indicated strip, and bounds each scalar polynomial by the smaller of the uniform nonedge upper bound and either endpoint plus twice the interval width. Indeed \(|F'|\le2\) on this interval, as follows directly from its four terms. The visits are 253,359 and 331,699; every remaining box passes.

If the degrees of the matched endpoints are \(d,e\), there are at least \(17-d-e\) common nonneighbors, by excluding each endpoint and all other endpoints of incident edges. The exact two-row upper bound is the sum of their table entries divided by 1000, plus \((32-d-e)9/1000\), minus \((17-d-e)\) times the applicable savings. For every pair \(2\le d,e\le8\) this is strictly less than \(2T\), as the verifier checks. This groups the ordered off-diagonal rows, so no saving is counted twice. Summing over unmatched vertices and matching edges contradicts the weighted harmonic lower bound. The stated thresholds follow.
