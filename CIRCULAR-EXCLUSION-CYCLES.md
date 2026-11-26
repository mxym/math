# Shortest cycle partitions and magnetic endpoints for circular exclusion

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review or priority claim.

Let \(N\ge3\) and \(1\le k<N\). Configurations are binary words on the physical cycle, with exactly \(k\) particles. A directed arc is one permitted clockwise hop \(10\to01\). This is the configuration graph of homogeneous periodic TASEP. Its directed arcs split into \(\binom{N-2}{k-1}\) directed simple \(N\)-cycles, each using each physical bond once. That all directed closed walks have lengths divisible by \(N\) is a known grading observation (increment the sum of the occupied positions modulo \(N\)); see [Nakerst, Prosen and Haque, §VI](https://arxiv.org/abs/2402.00662). [Altaner et al., §IX](https://arxiv.org/abs/1105.2178) give a small example of cycle decomposition on four sites. Below is a uniform partition and two exact consequences.

## Construct the partition by splitting a site

At \(N=3\), both contents are directed triangles using all three bonds. In a partition at length \(N\), split a fixed site \(s\) into consecutive sites \(a,b\) in clockwise order. Each old cycle traverses the bond departing \(s\) exactly once. It has two lifts.
 
* To add zero particles, ordinarily encode the old site bit \(s\) as \((s,0)\). Immediately **before** the old exit, insert \(a\to b\) to turn \(10\) into \(01\). The exit now departs \(b\) and leaves \(00\).
* To add one particle, ordinarily encode \(s\) as \((s,1)\). The old exit departs \(b\), leaving \(10\) rather than the ordinary \(01\) for an empty old site. Immediately **after** the exit, insert \(a\to b\) to restore \(01\).

All other moves retain their bonds except that an incoming hop now arrives at \(a\). Each cycle has length \(N+1\), uses each physical bond once, closes, and has distinct vertices by the position-sum grading.

To check that every new arc appears exactly once, reconstruct its old arc and lift. For any arc other than \(a\to b\) and the exit from \(b\), the pre-hop bit at \(b\) tells which lift and the bit at \(a\) gives the old status. The two transient states occur only between the adjacent inserted and exit hops, hence cannot interfere with such arcs. For an exit from \(b\), the bit at \(a\) gives the lift and the old departure site is occupied. For an inserted arc \(10\to01\), look at the site immediately after \(b\). If empty, this is the zero lift just before the exit; if occupied, this is the one lift just after the exit. In each case it determines the old exit arc uniquely: before that old hop the old split site is occupied and its next site is vacant, with all other sites fixed. By induction that old arc selects one old cycle. This argument also verifies coverage of the extreme contents. Finally, a fixed new physical bond occurs as a legal departure in exactly \(\binom{N-1}{k-1}\) configurations at length \(N+1\); every cycle counts it once. This proves the stated count at each length. [An exact supplementary checker](verify-circular-exclusion-cycles.js) tests the induction against direct arc enumeration for every content through \(N=14\).

## Magnetic Laplacian

Give each clockwise move the phase \(e^{i\phi_j}\) of its physical bond, and let \(\theta=\sum_j\phi_j\bmod 2\pi\). Normalize \(\theta\) to \(\theta_0\in[-\pi,\pi]\). Use the convention
\[
\langle f,L_\theta f\rangle=\sum_{x\to y}|f(x)-e^{i\phi_j} f(y)|^2,
\]
and write \(D_{\rm out}\) for the diagonal of clockwise outdegrees. The partition proves
\[
L_\theta\succeq 2(1-\cos(\theta_0/N))D_{\rm out}.
\]
Each constituent \(N\)-cycle has flux \(\theta\), so a diagonal gauge and the Fourier modes show its lowest eigenvalue is \(2(1-\cos(\theta_0/N))\). Summing its quadratic form inequality over the partition counts each state exactly its outdegree times. A gauge at the physical sites induces a gauge on configurations by multiplying the phases of their occupied sites, and can redistribute the physical flux uniformly as \(\theta_0/N\). In that gauge the constant vector attains equality. Since indegree and outdegree agree in each configuration, the underlying magnetic Laplacian degree diagonal is \(2D_{\rm out}\); its ordinary degree-normalized bottom is exactly \(1-\cos(\theta_0/N)\), independent of \(k\). For \(|\theta_0|<\pi\), the minimizing vector on each constituent cycle is constant in this gauge, so equality on all cycles and connectivity of the underlying graph prove simplicity. The same lower bound argument works with positive weights per physical bond: replace the leading factor by the smallest unnormalized eigenvalue of the physical weighted magnetic cycle and still multiply by \(D_{\rm out}\). Exact equality is asserted here only in the homogeneous case.

## Numerical range of the jump chain

Let \(P f(x)\) be the average of \(f\) over permitted clockwise hops from \(x\). Outdegrees are positive and balance indegrees, so \(D_{\rm out}\) defines a stationary inner product. In that inner product the numerical range \(\{\langle f,Pf\rangle_D/\langle f,f\rangle_D:f\ne0\}\) is exactly the regular \(N\)-gon with vertices the \(N\)-th roots of unity. Each directed cycle contributes the numerator of a cyclic shift quotient, and its denominator is the sum of \(|f|^2\) on the cycle. The graph quotient is a weighted average of the nonzero-denominator quotients, hence lies in the polygon. Each vertex is attained by the wave \(f(x)=\exp(2\pi i j\sum_{h:x_h=1}h/N)\), since every hop increments the sum modulo \(N\). The numerical range is convex, so contains the polygon. This is an exact statement for the jump operator and the stated inner product, not a claim about the ordinary spectrum or the continuous-time generator.

## Consequence for the odd \(\pi\)-twisted deformed \(t\)–\(J\) chain

The [gap analysis](ODD-PI-TJ-GAP.md) uses \(t=\zeta^2-1>0\), \(c=t+2\). With no holes, the bond direction fields telescope. In each mixed content block each word has \(2D_{\rm out}(x)\) unlike bonds. Its diagonal energy is \(2cD_{\rm out}\); its off-diagonal energy is \(+t\) along each allowed unoriented swap. Thus the Hamiltonian equals \(4D_{\rm out}+tL_\pi\) when \(N\) is odd: every arc phase is \(-1\), with total flux \(\pi\). Since \(D_{\rm out}\ge I\), every no-hole excitation is at least \(P_N(t)=4+2t(1-\cos(\pi/N))\), and the one flipped particle attains this bound. A pure-background one-hole state also attains \(P_N\). The two-hole and higher blocks cost at least \(8\), while the one-hole trial already has energy at most \(8-4/(N-1)\). The exact full gap for every \(t>0\) is therefore the least energy within the one-hole sectors. Their intermediate-coupling comparison remains open.
