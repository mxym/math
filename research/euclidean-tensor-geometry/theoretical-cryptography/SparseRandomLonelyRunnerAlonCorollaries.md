# An Alon-lemma formulation of the sparse random window threshold

**Attribution clarification for [the sparse threshold note](SparseRandomLonelyRunnerThreshold.md).** Its conclusions are also consequences of [Noga Alon, *The chromatic number of random Cayley graphs*, European J. Combin. 34 (2013), Lemma 3.1](https://doi.org/10.1016/j.ejc.2013.05.007); see the [author's full text](https://web.math.princeton.edu/~nalon/PDFS/colcayley6.pdf). Alon applies the random-dilation lemma to a middle third and related longer intervals in Theorems 3.2–3.3. With a subpower choice of its tolerance, it applies to the full two-sided sparse threshold, not just a special lower bound. The short-dual argument in the previous note is a different proof, rather than a claim that the threshold is far removed from earlier methods. [Beck–Everett v3, §4](https://arxiv.org/pdf/2609.06259v3) uses the same uniform distinct-speed subset model on a choice of exponential scales to get a coarse upper bound for a different theorem; their sample law is not a different model.

The direct Alon argument also gives the following more local formulation. Let \(I_N\) be a deterministic closed time arc of length \(\ell_N=N^{\rho-1+o(1)}\) on the circle, with fixed \(0<\rho\le1\). Put \(m=N^{o(1)}\), \(m\ge1\), sample \(S\) uniformly of size \(m\) from \([N]\), and let \(L_I(S)=\sup_{t\in I_N}\min_{v\in S}\|vt\|\). Then
\[
       \frac{L_I(S)}{(1-N^{-\rho/m})/2}\ \longrightarrow\ 1
                                  \quad\text{in probability}.
\tag{1}
\]
It is uniform in the deterministic location of the arc for a fixed length sequence, not simultaneous for all arcs and not for an arc selected after seeing \(S\).

In fact let \(0<\delta=\delta_N\le\delta_*<1/2\), with \(\delta^{-1}=N^{o(1)}\), write \(w=1-2\delta\), and \(\sigma_N=-m\log w/\log N\). Below threshold, \(\limsup\sigma_N<\rho\), the successful time measure in \(I_N\) divided by \(\ell_N w^m\) tends to 1 in probability. Above threshold, \(\liminf\sigma_N>\rho\), with probability tending to 1 there is no successful time in \(I_N\). These are applications of the published dilation lemma with an explicit entropy scale.

## 1. Sequential intersection on prime grids

We use the following consequence of Alon's lemma. If \(A\subseteq\mathbb F_p\) is nonempty, \(J\) is a cyclic interval of relative cardinality \(b\), and \(b>2\mu\), then at most a fraction \(O(\mu^{-3}/|A|)\) of multipliers \(v\in\mathbb F_p\) have
\[
                 |\{a\in A:va\in J\}|<(b-2\mu)|A|.
\tag{2}
\]
The constant can be chosen absolute, using the explicit numerator in his bound. If \(v\) is sampled from \([N]\subset\mathbb F_p\), where \(p>N\), the failure probability is at most \(p/N\) times as large. This follows by retaining the same bad set of multipliers, without invoking any approximation to a uniform full-field probability.

Take a prime \(p=N^{1+\tau+o(1)}\) with a fixed \(\tau\ge0\), \(p>N\), and a deterministic set \(A_0\) of grid numerators of cardinality \(M=N^{\rho+\tau+o(1)}\). For each step, retain exactly the numerators whose gap to the newly sampled speed is at least \(\delta\). In residues the allowed set is one interval \(J\) of relative cardinality \(b=w+O(1/p)\), and its complement is another cyclic interval. Applying (2) to both intervals shows that the count after a step lies between \((b-2\mu)|A|\) and \((b+2\mu)|A|\) except with probability \(O((p/N)\mu^{-3}/|A|)\). Choose \(\mu=N^{-\eta}\) with sufficiently small fixed \(\eta>0\); both interval lengths exceed \(2\mu\).

First sample the speeds independently. Condition on the successful count bounds for earlier steps so the current set \(A\) is fixed given the previous draws. If \(\sigma_N\le\sigma_0<\rho\), the lower count after up to \(m\) steps is at least
\[
    M(b-2\mu)^m=(1+o(1))M w^m\ge N^{\rho+\tau-\sigma_0+o(1)}.
\]
The relative comparison follows from \(m\mu+m/p=o(1)\) and \(w\) bounded below. With \(3\eta<\rho-\sigma_0\), the conditional failure probability per step is \(O(N^{3\eta-\rho+\sigma_0+o(1)})\). Its sum over \(m=N^{o(1)}\) steps tends to zero. The upper count after the \(m\)-th step is at most \(M(b+2\mu)^m=(1+o(1))M w^m\). Thus the final count is \((1+o(1))M w^m\) with probability tending to one. The probability of any repeated draw is \(O(m^2/N)=o(1)\), so conditioning on all speeds distinct transfers the result to the uniform fixed-size subset law.

To pass to successful time measure on \(I_N\), take any fixed \(\tau>0\) and \(p\asymp N^{1+\tau}/\delta\), which still has exponent \(1+\tau+o(1)\). Apply the grid count to cells fully contained in \(I_N\) at threshold \(\delta+N/(2p)\), and to cells meeting \(I_N\) at threshold \(\delta-N/(2p)\). A cell of a grid point at the higher successful threshold consists of successful times, by the Lipschitz bound; a successful time must belong to a cell counted at the lower threshold. Both collections of cells have cardinality \((1+o(1))p\ell_N\). The change in \(w^m\) caused by either threshold adjustment is a relative \(o(1)\), since \(mN/p=o(1)\) and \(w\) is bounded below; the strict lower-bound margin in \(\sigma_N\) still holds. Dividing the two grid counts by \(p\) gives the claimed time-measure concentration.

## 2. Upper threshold on a coarser grid

If \(\liminf\sigma_N>\rho\), choose \(0<\gamma<1/2\) small so \(\delta'=(1-\gamma)\delta\) still has \(\liminf\sigma_N(\delta')>\rho\); the logarithmic loss is bounded on \((0,\delta_*]\) as in the sparse note. Take \(p\asymp N/(\gamma\delta)>N\) with \(N/(2p)\le\gamma\delta\). It suffices to test the nearest grid points to \(I_N\) at threshold \(\delta'\); the test count is \(N^{\rho+o(1)}\), even when the arc wraps through zero.

Use (2) with \(A=[N]\) and the *forbidden* interval of residues (near zero). The exceptional numerators may lie anywhere on the grid, but their absolute number is \(O((p/N)\mu^{-3})=N^{3\eta+o(1)}\). Each nonexceptional test has forbidden fraction at least \(2\delta'-O(\mu+1/p)\), hence succeeds with probability at most \((1-2\delta')^m(1+o(1))\), by sampling without replacement and \(m\mu+m/p=o(1)\). Union over \(N^{\rho+o(1)}\) tests gives \(o(1)\). For the exceptional points the [uniform pigeonhole bound](SparseRandomLonelyRunnerThreshold.md#3-upper-bound-on-the-same-kind-of-prime-grid) gives \(|B_{\delta'}(t)|\ge N\delta'/12\). Since \(m\delta'/\log N\ge (1-2\delta_*)\rho/2+o(1)\), each succeeds with probability at most \(N^{-c_\rho}\) for a fixed \(c_\rho>0\). Choose \(\eta<c_\rho/3\); their total success probability is \(o(1)\) too.

Finally \(D_{N,\rho}=(1-N^{-\rho/m})/2\) is exactly the solution of \(m[-\log(1-2D_{N,\rho})]=\rho\log N\). Thresholds by fixed relative factors just below and above it fall on the two sides of the strict margin by convexity. For the upper comparison when the inflated threshold reaches \(1/2\) use the trivial bound; on remaining indices insert a halfway inflated threshold bounded away from \(1/2\). This is the same endpoint argument as in the sparse note and proves (1) for oscillating \(m/\log N\) as well.
