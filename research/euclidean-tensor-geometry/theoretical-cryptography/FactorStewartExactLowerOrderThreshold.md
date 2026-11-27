# The exact lower-order threshold in the Stewart construction

Research supplement, 27 November 2026. This refines the [all-starts endpoint count](FactorStewartAllStartsEndpoint.md) for the existing two-sign square–cube–fifth-power construction. It does not improve the leading constant \(1/\sqrt5\), rule out a fourth power in arbitrary intervals, or claim a globally optimal interval length. All intervals below are closed.

Put \(d=1/\sqrt5\), \(v=N^{1/3}\), \(b_0=81/(200\sqrt5)\), and
\[
 \mathcal L_*(N)
   =d(v+7/25)\sqrt{v+1/4}-\frac3{10}v-\frac3{50}.
\]
The negative-sign pair consists of a cube \(C=(3125n^{10}-125n^5+1)^3\) and a fifth power \(F=(125n^6-3n)^5\), with \(C<F\). Its gap is *exactly* \(\mathcal L_*(C)\). The interval \([C,F]\) contains exactly three distinct perfect powers in the order cube, square, fifth power for
\[
        \left(\frac1{10}+o(1)\right)X^{1/30}
\]
of these starts \(C\le X\). For an arbitrary integer start \(N\) containing this fixed cube/fifth-power pair, length \(\mathcal L_*(N)\) suffices only at \(N=C\).

The expansion at the threshold is
\[
 \mathcal L_*(N)
 =d\sqrt N-\frac3{10}N^{1/3}+b_0N^{1/6}-\frac3{50}
   +\frac{87}{3200\sqrt5}N^{-1/6}+O(N^{-1/2}).
 \tag{1}
\]
The following table gives the number of integer starts \(N\le X\) for which the indicated length contains a distinct triple from either sign of the original construction and contains exactly three distinct perfect powers. All auxiliary real parameters are fixed as \(X\to\infty\).

| Length | Parameter range | Number of starts |
|---|---|---:|
| \(\mathcal L_*(N)+\eta\) | \(\eta<0\) | \(O(1)\) |
| \(\mathcal L_*(N)+\eta\) | \(\eta=0\) | \((1/10+o(1))X^{1/30}\) |
| \(\mathcal L_*(N)+\eta\) | \(\eta>0\) | \((\lceil\eta\rceil/10+o(1))X^{1/30}\) |
| \(d\sqrt N-aN^{1/3}\) | \(0\le a<3/10\) | \(((3-10a)/1100+o(1))X^{11/30}\) |
| \(d\sqrt N-aN^{1/3}\) | \(a\ge3/10\) | \(O(1)\) |
| \(d\sqrt N-\frac3{10}N^{1/3}+bN^{1/6}\) | \(b>b_0\) | \(((b-b_0)/60+o(1))X^{1/5}\) |
| \(d\sqrt N-\frac3{10}N^{1/3}+bN^{1/6}\) | \(b<b_0\) | \(O(1)\) |
| \(d\sqrt N-\frac3{10}N^{1/3}+b_0N^{1/6}+c\) | \(c>-3/50\) | \((\lceil c+3/50\rceil/10+o(1))X^{1/30}\) |
| \(d\sqrt N-\frac3{10}N^{1/3}+b_0N^{1/6}+c\) | \(c\le-3/50\) | \(O(1)\) |

The \(a=0\) row is the previously proved endpoint. The \(b=b_0\) case is the \(c=0\) row.

## 1. Exact curve and integer starts

Write \(u=n^5\), \(V=3125u^2-125u+1\), and \(G=F-C\). Binomial expansion and substitution give
\[
\begin{aligned}
 G&=78125u^3-5625u^2+132u-1,\\
 4V+1&=5(50u-1)^2,\\
 50G+15V+3&=(25V+7)(50u-1).
\end{aligned}
\]
Since \(u\ge1\), \(d\sqrt{V+1/4}=(50u-1)/2\), which proves \(G=\mathcal L_*(C)\) exactly. Expanding \((v+7/25)\sqrt{v+1/4}\) through its \(v^{-1/2}\) term gives (1).

All the length functions in the table are increasing for sufficiently large \(N\), since their common leading derivative is \(d/(2\sqrt N)\), with lower-order corrections. For \(\mathcal L_*(N)\) one has \(0<\mathcal L_*'(N)<1/\sqrt N\) for \(N\ge1\): differentiate with respect to \(v\), dividing the result by \(3v^2\). The positive bracket
\[
 d\left(\sqrt{v+1/4}+\frac{v+7/25}{2\sqrt{v+1/4}}\right)-\frac3{10}
\]
is bounded above by \((3/2+16/25)\sqrt v\). A pair-containing start must have \(N=C-k\) for \(k\) a nonnegative integer. At length \(L(N)\) the condition is exactly
\[
 k\le [L(C)-G]+L(C-k)-L(C).
 \tag{2}
\]
In particular \(\mathcal L_*(N)\) spans this pair only at \(k=0\). At \(L=\mathcal L_*+\eta\), negative \(\eta\) eventually excludes the pair; \(\eta=0\) gives \(k=0\); and positive \(\eta\) gives precisely \(0\le k<\eta\) eventually. Indeed the correction term in (2) is negative for \(k>0\) and tends to zero for each fixed \(k\). Thus an integer \(\eta>0\) does not admit its boundary start \(k=\eta\).

For the two growing-slack ranges, (1) at \(N=C\) gives
\[
 L(C)-G=
 \begin{cases}
 3125(\frac3{10}-a)n^{10}+O(n^5),&0\le a<3/10,\\
 25\sqrt5\,(b-b_0)n^5+O(1),&b>b_0 .
 \end{cases}
\]
By (2), monotonicity, and the derivative bound \(L'(N)=O(N^{-1/2})\), the error \(L(C-k)-L(C)\) is \(o(1)\) throughout the possible start range, and the number of permissible \(k\)'s is \(L(C)-G+O(1)\). In the constant-\(c\) range the slack approaches \(c+3/50\) strictly from below, with leading difference \(-87 C^{-1/6}/(3200\sqrt5)\). This excludes \(c=-3/50\) itself and yields exactly \(\lceil c+3/50\rceil\) starts eventually if \(c>-3/50\). The other failing cases in the table have strictly negative eventual slack. The positive-sign pair is eventually impossible for all lengths listed: even \(d\sqrt N\) misses it by order \(n^{10}\) as in the endpoint note; each listed length is at most \(d\sqrt N\) eventually (identically at \(a=0\)).

## 2. The square phase and counting starts

As proved in the endpoint note, \(\{\sqrt F\}\) is equidistributed: \(\sqrt F\) is a polynomial in \(n\) with irrational leading coefficient plus \(O(n^{-5})\). The lower square is strictly internal to \([C,F]\) for a set of parameters of density \(d/2\), because the normalized gap \((F-C)/\sqrt F\) tends to \(d\) and the normalized offset of the lower square is \(-2\{\sqrt F\}+o(1)\). For each such parameter, all pair-containing starts in (2) contain that square. If a square lies outside the pair, it can enter the interval only within \(O(n^{10})=o(\sqrt F)\) of a pair endpoint, uniformly in all the table ranges. The associated phases, including equality, concentrate at finitely many boundary values and occur on \(o(T)\) parameters through \(n\le T\). Those exceptional parameters give \(o(T^{r+1})\) starts when the per-parameter bound is \(O(n^r)\), \(r=10,5,0\).

Near \(F\) a window of the stated length has room for at most one square, one cube, and one fifth power. As in the endpoint note, an additional distinct power therefore has a prime exponent \(p\ge7\). All windows for a fixed large \(n\) lie in a radius-\(O(\sqrt F)\) cluster. For each prime \(7\le p\le29\), an extra \(p\)-th power in this cluster forces \(\|F^{1/p}\|=o(1)\), while \(F^{1/p}=5^{15/p}n^{30/p}+o(1)\) has equidistributed fractional part by the nonintegral-power argument in the [exactly-three note](FactorStewartExactlyThree.md). For \(p\ge31\) together there are \(O(T^{30/31}\log(2T))=o(T)\) powers in the entire size range for \(n\le T\). The clusters are eventually disjoint, so excluding these parameters also changes the count by \(o(T^{r+1})\). No conjecture about the distribution of fourth powers in all integer intervals is being used.

Finally \(C\sim5^{15}n^{30}\), so the cutoff is \(T=(5^{-1/2}+o(1))X^{1/30}\). Replacing \(C\le X\) by the condition \(N\le X\) changes the count by at most a fixed number of boundary clusters, each contributing only \(O(T^r)\). With an internal-square density \(d/2\), a constant multiplicity \(m\) gives main term \(m(d/2)T\sim(m/10)X^{1/30}\). Partial summation gives \((d/2)T^{r+1}/(r+1)\) for total weight \(n^r\); multiplying by the two displayed slack coefficients gives \((3-10a)/1100\) and \((b-b_0)/60\) in the table. This proves the counts.

The [exact integer check](verify_factor_stewart_exact_threshold.js) tests the gap identities, constant-term comparisons, and fixed-slack integer-start arithmetic through \(n=20000\). It is a sanity check rather than a substitute for equidistribution. This supplement concerns the existence side of [Stewart, Section 4](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/aa133-2-01.pdf) and does not modify the earlier release.
