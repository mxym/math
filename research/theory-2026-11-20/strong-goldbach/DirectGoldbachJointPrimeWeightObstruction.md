# A joint prime-weight obstruction for the fixed-target Chen and direct inputs

The [root-band model](DirectGoldbachGRHRootBandModel.md) and [Chen-core saturation](DirectGoldbachChenCoreSaturation.md) can occur in the **same** model at the **same** target. This tests numerical inputs, not the exact arithmetic of the prime indicator. In particular it does not show that any actual even integer has no representation.

Write \(S_N=\mathfrak S(N)N/\log^2N\). There exist one function \(u\) with values in \(\{0,1,2\}\) on genuine primes and a sparse sequence of multiples of four \(N_j\) such that:
1. The full modeled binary count \(\sum_{p+p'=N_j}u(p)u(p')\) is zero.
2. For both core weights \(c\) of the saturation note, \(\sum_{p+sr=N_j,\ s<r}u(p)u(s)u(r)c(\log_{N_j}s)=(I_c+o(1))S_{N_j}\), with \(I_c=1.421763588\ldots\) or \(1.394166883\ldots\). Both are above their proposed caps even when the modeled binary count vanishes.
3. The perturbation preserves the character, progression and local nonzero-offset numerical estimates specified below. Those results are perturbation statements; actual prime distribution estimates remain the base input.

## Construction

Fix \(0<\delta<\alpha=.087\), for example \(\delta=1/40\). Select \(N_j\equiv0\bmod4\) from the common saturation set, with \(N_{j-1}<N_j^\delta/2\). Such a sequence exists by the density result. This choice does not assert saturation on powers of two. At a target \(N=N_j\) the genuine prime pairs form a matching on the primes below \(N\), with no midpoint prime for large \(N\). On each pair whose smaller endpoint is \(\le N^\delta\), set the larger endpoint to zero and leave the smaller endpoint unchanged. The deterministic edits lie in \([N-N^\delta,N]\). On every other pair give one endpoint weight \(2\) and the other zero, using an independent fair sign. All edited positions at one stage exceed the earlier target, and all later edits are above this target. A smaller endpoint left unchanged may itself have an earlier weight, but its larger endpoint is zero regardless. This proves the full binary vanishing.

## Preservation of the exact composite rows

Here is a more general comparison that includes both semiprime core sums. Consider any bounded deterministic test on rows \(p+m=N\), where \(p\) is prime and \(m\) is squarefree composite with every prime divisor at least \(N^\alpha\). Multiply each row by \(u(p)\prod_{t\mid m} u(t)\), over prime \(t\). The absolute weights are at most \(2^{1+\lfloor1/\alpha\rfloor}\), a fixed constant. A polynomial-size family of tests with common bounded sup norms may be specified in advance at each selected target.

Every factor of \(m\) is at most \(N^{1-\alpha}\), so misses earlier edits and the current deterministic interval. Remove the \(O(N^\delta)\) rows with \(p\le N^\delta\). If \(p\) is deterministically zeroed at the current stage then \(N-p\) is prime, so this gives no composite row. A repetition between \(p\) and a factor of \(m\) implies \(p\mid N\), removing at most \(O(\log N)\) more rows. Among the remaining labels, \(p+t<N\) for any factor \(t\) since \(t<m\), and the sum of two distinct prime factors is smaller than or equal to \(m<N\). Thus no two labels are on the same matched edge. The expected product weight on every remaining row is \(1\).

Flipping a sign affects only rows containing one of its two endpoints. A prime \(t\) is an outer label in at most one row. As a factor it occurs in at most \(N/t\) rows, since distinct multiples \(m\le N\) are counted once. Squarefree factorization and bounded rank ensure the change per affected row is bounded by a fixed constant. The sum of squared Lipschitz bounds over all matched edges is therefore
\[
 O_\alpha\!\left(N+N^2\sum_{t\ge N^\alpha}t^{-2}\right)=O_\alpha(N^{2-\alpha}).
\]
The bounded-differences inequality gives exponentially small failure probability at \(N^{1-\alpha/3}\), so the comparison holds simultaneously for every specified test and all large selected \(N\) in one realization. The absolute error, including removals, is \(o(N/\log^2 N)\). Taking the two core tests proves assertion 2. One may also prescribe a bounded number of marks, with multiplicity absorbed into the test as the rank is bounded. This assertion is for **composite** complements, not the mixed Chen score including its prime-complement term.

## Analytical perturbation bounds

Use the log-weight perturbation \((u(p)-1)\log p\). For a fixed interval inside \([1,2X]\) and arithmetic progression \(a\bmod q\), the squared signed-coefficient sum is \(O((X/q+1)\log^2 X)\), since there are \(O(X/q+1)\) eligible positions and each edge contains at most two. The deterministic intervals contribute \(O((X^\delta/q+\log X)\log X)\): lengths sum geometrically, and each intersecting shell costs one rounding error. Hoeffding and a polynomial union over progressions and intervals, followed by summation over \(q\le Q\le X\), give a uniform interval-maximal perturbation bound
\[
 \sum_{q\le Q}\max_{I,a}
 \left|\sum_{\substack{p\in I\\ p\equiv a\bmod q}}(u(p)-1)\log p\right|
 \ll \sqrt{XQ}\log^3 X.
\]
Indeed the sum of the square-root terms is \(O(\sqrt{XQ})\) before log factors, and the deterministic contribution is \(O(X^\delta\log^2 X+Q\log^2 X)\). Centering a residue by the reduced total divided by \(\varphi(q)\) costs at most the same bound, by the full prefix estimate and \(\sum_{q\le X}\varphi(q)^{-1}\ll\log X\). For character/additive Fourier tests of any fixed polynomial modulus range, the squared random coefficient bound is \(O(X\log^2 X)\); the polynomial frequency grid and interval union of the root-band model give \(O(\sqrt X\log^{3/2}X)\). Dyadic scales make the failure probabilities summable, and partial summation gives the fixed smooth tests. After division by \(\varphi(q)\) in character Parseval, the centered short-frequency perturbation is \(O(Xb\log^3 X)\) at width \(b\).

At the selected target, the fixed interior windows of the root-band note exclude both the earlier edits and the deterministic edits at this stage. All off-target local binary sums \(p+p'=M\ne N_j\) thus satisfy the same bounded-differences comparison as in that note. Using only \(O(N_j)\) matching edges gives error \(O(\sqrt{N_j}\log^{5/2}N_j)\) uniformly on the \(O(N_j)\) relevant shifts, already sufficient. The divisor-harmonic comparison in that note, with the extra fixed log factors here, still gives \(O(X\log^{-K+O(1)}X)=o(XT/Q)\) for the aggregate nonzero-offset and mixed changes for sufficiently large fixed \(K\). No new claim about a signed lower bound for real primes follows.

Consequently, an implication from **only** these numerical inputs, zero modeled binary mass and the exact additive composite rows to either lowered core cap cannot hold uniformly. An actual argument can still use structure lost by the reweighting, including the normalization of the prime indicator and exact identities incorporating the prime-complement rows. In particular this comparison does not transfer every hypothesis of a Chen rearrangement with that exact normalization.
