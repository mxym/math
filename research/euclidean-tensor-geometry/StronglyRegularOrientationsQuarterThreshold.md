# The sharp large-order directed triangle threshold for strongly regular graphs

**Yongxian Zhang.** AI-assisted proof development and internal verification.

**Theorem.** Every orientation of a strongly regular graph on \(n\ge254\) vertices with minimum outdegree \(d>n/4\) has a directed triangle. The constant \(1/4\) cannot be improved uniformly, even at large orders: for \(n=4m\), split each part of \(K_{2m,2m}\) into two equal groups and direct edges cyclically around the four groups. The resulting orientation has minimum outdegree \(n/4\) and no directed triangle. This does not settle the threshold at all small orders or the unrestricted Caccetta–Häggkvist conjecture. The [previous all-order \(11n/40\) proof](StronglyRegularOrientationsTriangle.md) remains available.

## A spectral estimate for any regular host

Let the host have order \(n\), degree \(k>0\), adjacency \(S\), and largest absolute nonprincipal eigenvalue \(\theta\). The orientation has adjacency \(A\), skew part \(K=A-A^{\mathsf T}\), minimum outdegree \(d\), and imbalance variance \(V=n^{-1}\sum_v(2d_v^+-k)^2\). If there is no directed triangle then
\(\operatorname{tr}(S^3)=3\operatorname{tr}(SKK^{\mathsf T})\), by the trace expansion of \((S+K)^3\). A column of \(K\) has squared norm \(k\) and coordinate sum with absolute value \(|2d_v^+-k|\). The principal spectral projection gives \(\operatorname{tr}(SKK^{\mathsf T})\le kV+n k\theta\). Also \(\operatorname{tr}(S^3)\ge k^3-\theta k(n-k)\). Thus
\[
V \ge k^2/3-\theta(4n-k)/3.
\]

Sort outdegrees in decreasing order. Their first \(i\) terms sum to at most \(ki-e(S_i)\), where \(S_i\) is the set of the first \(i\) vertices. Mixing on its indicator gives \(2e(S_i)\ge k i^2/n-\theta i(1-i/n)\). A second bound comes from the remaining vertices' minimum degree. The sorted degree sequence is therefore majorized by the successive differences of the concave function
\[
H(x)=\min\{ kx - kx^2/(2n)+\theta x(1-x/n)/2,\ nk/2-d(n-x)\}.
\]
The prefix totals agree at \(x=0,n\). The minimum of the two concave branches is concave and the endpoints are the actual prefix totals. Majorization and Jensen over each unit interval bound the squared degree mean by \(n^{-1}\int_0^n H'(x)^2 dx\). The two branches switch at \(x=n(k-2d)/(k+\theta)\). The slope decreases linearly from \(k+\theta/2\) to \(2d+\theta/2\), then equals \(d\). Evaluating the integral gives
\[
V\le \frac{k^2}{3}
+\frac{2k^2\theta+3k\theta^2-8d^3-12d^2\theta-6d\theta^2}{3(k+\theta)}.
\]
For a finite check the upper bound uses only \(-t\), the least eigenvalue, so replace \(\theta\) by \(t\) in this direction. The lower bound for strongly regular hosts also sharpens to \(V\ge n\lambda/3-nr\) by using the exact trace \(nk\lambda\) and only the positive nonprincipal eigenvalue \(r\) in the column estimate.

Together the general regular-host bounds imply \(2 d^3 \le \theta(kn+k^2/4)+\theta^2(n+k/2)\). In particular for primitive strongly regular graphs the absolute multiplicity bounds for both nonprincipal eigenvalues give \(\theta=O(n^{3/4})\), hence every directed-triangle-free orientation has \(d=O(n^{11/12})\). [Brouwer–Van Maldeghem, Proposition 1.3.14](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf)

### Effective cutoff and exact check

At \(n\ge19306\), both multiplicities are at least 196 by the absolute bound \(n\le f(f+3)/2\). Hence \(\theta/n\le\sqrt{x(1-x)}/14\) for \(x=k/n\). Using \(x\sqrt{x(1-x)}\le3\sqrt3/16\), the cubic bound gives \(d^3/n^3\le105/7168+3/3136<1/64\), using \(\sqrt3<7/4\). The final inequality was checked by an exact integer cross multiplication.

## Disconnected hosts or complements

An imprimitive strongly regular graph is a disjoint union of cliques or a complete multipartite graph. The former has minimum outdegree zero if it has no directed triangle, since a triangle-free tournament is transitive. In the latter case take a sink strongly connected component. By [Bondy's theorem](https://doi.org/10.1112/jlms/s2-14.2.277) it meets at most two parts. Inside the component there are either no arcs, or the underlying graph is complete bipartite with parts of sizes \(a,b\). The average outdegree is then \(ab/(a+b)\le(a+b)/4\le n/4\). Since the component is a sink this also bounds the original minimum outdegree.

## Exact finite reduction for primitive hosts

A putative violation has minimum outdegree at least \(d_0=\lfloor n/4\rfloor+1\), and \(k\ge2d_0>n/2\). The two nonprincipal eigenvalues are integers: if they were irrational conjugates, their multiplicities would be equal, and zero trace would give \(\mu-\lambda=2k/(n-1)\), strictly between 1 and 2. Write them \(r,-t\). Let \(\ell=n-k-1\). The strongly regular identity \(\ell\mu=k(k-1-\lambda)=k(r+1)(t-1)\) forces \(t\ge2\). Using \(k=rt+\mu\) implies \(\mu\mid rt(r+1)(t-1)\); enumerating these positive divisors and setting \(\ell=(r+1)(t-1)(1+rt/\mu)\) covers all parameter sets. The two classical Krein inequalities and both absolute multiplicity bounds are used as in [Brouwer–Van Maldeghem](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf).

The search uses a slightly stronger local bound than the earlier result. In the outneighborhood of any vertex \(v\), choose a vertex \(w\) with internal outdegree less than \(c d_v^+\), where \(c=693/2000\) by [Hladký–Král’–Norin](https://arxiv.org/abs/0908.2791). The arc \(v\to w\) implies no outarc from \(w\) goes back to \(v\) or to an inneighbor of \(v\). Exactly \(k-1-\lambda\) host neighbors of \(w\) are outside \(N(v)\cup\{v\}\). Thus
\[
 d\ge d_1=\max\!\left(d_0,1+\left\lfloor\frac{d_0-(k-1-\lambda)}{c}\right\rfloor\right)
\]
for the actual minimum outdegree. The closed-form upper estimate for \(V\) above is nonincreasing in \(d\), hence applicable with \(d_1\). Also put \(a=k-2d_1\); the mean-zero imbalance in \([-a,k]\) has \(V\le ak\). By the local cubic trace estimate in the earlier proof, for \(\lambda>r\) one also needs
\[
 \lambda\le 3r+\frac{3(\lambda-r)V}{k^2}.
\]
For an additional exact variance bound, on the decreasingly sorted excesses \(d_v^+-d_1\) take the discrete prefix majorant
\[
 U_i=\min\!\left(\frac{na}{2},(k-d_1)i,\ (k-d_1+t/2)i-\frac{k+t}{2n}i^2\right).
\]
Then \(V\le4\sum_i(U_i-U_{i-1})^2/n-a^2\), by the same prefix comparison, with no rounding of the \(U_i\). Substituting the upper bounds into the global and local necessary trace inequalities gives an exact integer check.

The [Node.js replay](verify_srg_quarter_threshold.js) for \(n\le19305\) leaves exactly twenty tuples at orders 10, 15, 27, 35, 75, 81, 95, 96, 105, 112, 120, 125, 126, 154, 162, 175, 176, 243, 253, and 275. Intermediate counts (through the degree and elementary parameter tests, multiplicity, Krein, global continuous trace, local continuous trace, local elementary variance, and discrete variance) are \(698197,33482,32419,27,20,20,20\). This is a list of surviving *parameters*, not a claim that each is realizable or has an orientation avoiding directed triangles.

## Last large tuple and two smaller exclusions

At order 275 the tuple is \((275,162,105,81)\). Its complement is uniquely the McLaughlin graph, and its neighborhood graph is the complement of the second subconstituent \(\operatorname{srg}(162,56,10,24)\); see [Brouwer–Van Maldeghem, §10.48 and §10.61](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf). The latter graph has nonprincipal eigenvalues \(2,-16\), so the largest nonprincipal eigenvalue of every host neighborhood is \(15\). The local trace inequality holds with this neighborhood eigenvalue in place of \(r\) (apply Rayleigh to the mean-zero part of each column on its support). Here \(d_1\ge69\) implies \(a\le24\). It would give
\[
105\le 3\left(15+\frac{(105-15)24}{162}\right)=85,
\]
a contradiction. The remaining tuples all have order at most 253, proving the sharp uniform threshold at \(n\ge254\).

At order 10 the previous proof applies because \(d_1=3\) (a balanced orientation). At order 27 the local graph is the halved five-cube with nonprincipal top eigenvalue 2, proved in the earlier proof. As \(d_1\ge7,\ k=16,\ \lambda=10\), the same local trace upper bound would give \(10\le3(2+(10-2)2/16)=9\). These two smaller exclusions leave 17 candidate parameter sets. They are not excluded merely by this note.

The [November 2026 paper on minimum outdegree forcing directed cycles](https://arxiv.org/abs/2611.22909) addresses general host conditions, distinct from this strongly regular result. No exhaustive priority claim is made.
