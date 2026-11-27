# Counting all starts in the Stewart construction, including the endpoint

The [original proof](FactorStewartSquareCubeFifth.md) counts square starts for a polynomial construction of Stewart's square–cube–fifth-power triples. The [exactly-three supplement](FactorStewartExactlyThree.md) removes fourth powers from almost all of those successful examples. Here we count every integer start containing one of the constructed triples, use both signs of the polynomial parameter, and reach the endpoint length \(\sqrt{N/5}\).

**Theorem.** Write \(d=1/\sqrt5\). For each fixed \(d<\lambda\le1\), the number of distinct positive integers \(N\le X\) for which \([N,N+\lambda\sqrt N]\) contains a triple from the two-sign construction below and exactly three distinct perfect powers is
\[
 \left(\frac{\lambda(\lambda-d)}{16\sqrt5}+o(1)\right)X^{8/15}.
 \tag{1}
\]
Each of the six possible orders of the square, cube, and fifth power has positive asymptotic frequency within this count. For a given ordering, the coefficient is \((\lambda-d)^2/(64\sqrt5)\) if the square is first or last, and \(d(\lambda-d)/(32\sqrt5)\) if it is in the middle.

At \(\lambda=d\), the corresponding count is
\[
 \left(\frac{3}{1100}+o(1)\right)X^{11/30}.
 \tag{2}
\]
Its main term has the order cube, square, fifth power. For any fixed \(\lambda<d\) these two families eventually give no triples. These asymptotics are for the specified construction, and provide lower bounds for the unrestricted interval counts.

## 1. The two families and their square phase

For \(\sigma\in\{-1,1\}\), put
\[
 F_{n,\sigma}=(125n^6+3\sigma n)^5,\qquad
 C_{n,\sigma}=(3125n^{10}+125\sigma n^5+1)^3,\qquad
 R_{n,\sigma}=\sqrt{F_{n,\sigma}}.
\]
Substituting \(-n\) for \(n\) in the original identity gives both signs:
\[
 C_{n,\sigma}-F_{n,\sigma}
 =78125\sigma n^{15}+5625n^{10}+132\sigma n^5+1.
 \tag{3}
\]
Both \(F_{n,\sigma}\sim5^{15}n^{30}\) and \(R_{n,\sigma}\sim5^{15/2}n^{15}\). Expanding
\[
 R_{n,\sigma}=5^{15/2}n^{15}(1+3\sigma/(125n^5))^{5/2}
\]
through the constant term gives a polynomial with irrational leading coefficient \(5^{15/2}\), plus \(O(n^{-5})\). Weyl's polynomial theorem shows that \(\alpha_{n,\sigma}=\{R_{n,\sigma}\}\) is equidistributed for each sign.

Use \(F=F_{n,\sigma}\), \(R=\sqrt F\), and normalize offsets by \(R\). The fifth power's offset is 0, the cube's is \(\sigma d+O(n^{-5})\), and the two neighboring squares \(\lfloor R\rfloor^2\) and \((\lfloor R\rfloor+1)^2\) have offsets
\[
 -2\alpha_{n,\sigma}+O(R^{-1}),\qquad
 2(1-\alpha_{n,\sigma})+O(R^{-1}).
 \tag{4}
\]
If a square is within the desired interval, it is one of these: since the interval contains \(F\), has \(N\le F\), and has length at most \(R\), its squares are within \(R\) of \(F\), whereas squares farther than the two neighboring ones differ from \(F\) by \(2R-O(1)\) or more. A square coinciding with \(F\) or \(C\) can occur only at a phase converging to one of the finitely many boundary phases in (4), and thus occurs for \(o(T)\) parameters up to \(T\). We always count distinct triples.

For a fixed distinct triple write \(m\) for its minimum and \(B\) for its maximum. Its integer starts must satisfy \(N\le m\) and \(N+\lambda\sqrt N\ge B\). The latter is a monotone inequality whose positive real threshold is \(B-\lambda R+O(1)\): the threshold is \(F+O(R)\), so its square root differs from \(R\) by \(O(1)\). Hence the number of starts is
\[
 \big(\lambda R-(B-m)\big)_++O(1).
 \tag{5}
\]
All assertions about error terms here concern fixed \(\lambda\).

## 2. Above the endpoint

For \(\sigma=1\), the limiting normalized cube/fifth-power pair lies at \(0,d\), while the square positions have the uniform phase of (4), of period 2. By (5), the mean normalized count for a square before both powers is
\[
 \frac12\int_{d-\lambda}^{0}\big(\lambda-(d-s)\big)\,ds
 =\frac{(\lambda-d)^2}{4}.
\]
For a square between the powers it is \(\tfrac12\int_0^d(\lambda-d)\,ds=d(\lambda-d)/2\); for a square after both powers it is again \((\lambda-d)^2/4\). Outside these square positions the limiting count is zero. This gives total mean \(\lambda(\lambda-d)/2\). Perturbations in (3)–(5) tend to zero after normalization, and phase boundaries occupy a set of measure zero. For \(\sigma=-1\) the limiting picture is the reflection, with the same three means for the reversed orders. All six are positive if \(\lambda>d\).

Equidistribution and partial summation justify using these means with weight \(R_{n,\sigma}\): if \(\sum_{n\le T} f(\alpha_{n,\sigma})=\bar fT+o(T)\), then
\(\sum_{n\le T}n^{15} f(\alpha_{n,\sigma})=\bar f T^{16}/16+o(T^{16})\). From \(F_{n,\sigma}\le X\) the parameter cutoff is \(T=(5^{-1/2}+o(1))X^{1/30}\); thus the sum of \(R_{n,\sigma}\) contributes \(X^{8/15}/(16\sqrt5)\) for each sign. Multiplying by the means gives (1) and the coefficients for each order, before excluding fourth powers.

There is no double counting for large \(n\). Both signs at the same \(n\) have centers separated by \(\asymp n^{25}\), and the centers from \(n\) to \(n+1\) have separation \(\asymp n^{29}\), by the leading and next terms of the fifth-power polynomial. All candidate starts and their interval contents are in clusters of radius \(O(R_{n,\sigma})=O(n^{15})\) around their centers. These clusters are eventually pairwise disjoint. A single start cannot contain two distinct neighboring squares by the square spacing. Replacing the cutoff \(F\le X\) by \(N\le X\) only affects a bounded number of clusters straddling \(X\), contributing \(O(X^{1/2})\) possible starts, a smaller order than \(X^{8/15}\).

## 3. At the endpoint

From (3) and the binomial expansion,
\[
\begin{aligned}
 d R_{n,\sigma}
 &=78125n^{15}+\sigma\frac{9375}{2}n^{10}+O(n^5),\\
 |C_{n,\sigma}-F_{n,\sigma}|
 &=78125n^{15}+\sigma\,5625n^{10}+O(n^5).
\end{aligned}
\]
Consequently the slack \(dR_{n,\sigma}-|C_{n,\sigma}-F_{n,\sigma}|\) is \(-\sigma(1875/2)n^{10}+O(n^5)\). This is eventually negative for \(\sigma=1\), which excludes all possible starts because \(N\le F_{n,1}\). For \(\sigma=-1\) the slack is positive. The lower square lies strictly between the cube and fifth power at a set of parameters of density \(d/2\), by (4) and equidistribution. For each such parameter the span of the triple equals the cube/fifth-power gap, so by (5) the number of starts is
\[
 \frac{1875}{2}n^{10}+O(n^5).
\]
A square outside the pair can fit only within \(O(n^{10})\) of one endpoint, which on the normalized scale is \(O(n^{-5})\); its phase is accordingly at vanishing distance from one of two boundary phases. Equidistribution makes these parameters \(o(T)\), and all endpoint parameters have \(O(n^{10})\) starts by (5). Thus the outside squares contribute \(o(T^{11})\), as do any equality phases. Weighted summation gives
\[
 \frac{1875}{2}\cdot\frac{d}{2}\cdot\frac1{11}
     \left(5^{-1/2}\right)^{11} X^{11/30}
 =\frac3{1100}X^{11/30}.
\]
The cutoff error is now \(O(X^{1/3})\), because each affected cluster has only \(O(n^{10})\) starts. For fixed \(\lambda<d\) the normalized pair gap tends to \(d>\lambda\) for both signs, which excludes all large parameters.

## 4. Excluding every fourth perfect power

Uniformly over the candidate starts, an interval of length at most \(\sqrt N\) near \(F\) can include at most one square, one cube, and one fifth power. Thus an extra distinct perfect power must have a prime exponent \(p\ge7\). Apply the argument in the [exactly-three proof](FactorStewartExactlyThree.md) to the enlarged clusters of radius \(O(R)\), as follows.

For every fixed prime \(7\le p\le29\), a \(p\)-th power in a cluster forces \(\|F_{n,\sigma}^{1/p}\|=O_p(n^{30/p-15})=o(1)\); whereas
\[
 F_{n,\sigma}^{1/p}=5^{15/p}n^{30/p}+O_p(n^{30/p-5}).
\]
The error tends to zero and the leading exponent \(30/p\) is nonintegral. The nonintegral-power equidistribution argument in the exactly-three proof applies to both signs. Hence the cluster can have a \(p\)-th power only for \(o(T)\) of the parameters \(n\le T\). For all exponents \(p\ge31\) together, there are only \(O(T^{30/31}\log(2T))=o(T)\) powers below \(O(T^{30})\). Disjointness of the clusters again gives only \(o(T)\) exceptional parameters. Removing all these parameters changes the ordinary count by \(o(T^{16})\) and the endpoint count by \(o(T^{11})\), using the respective per-parameter bounds. This proves (1)–(2) and the ordering assertions with exactly three powers.

## Scope

These statements quantify the construction answering the **existence** part of [Stewart's 2008 conjecture, Section 4](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/aa133-2-01.pdf). They refine the [frozen square-start release](https://github.com/mxym/math/releases/tag/stewart-three-perfect-powers-v1.0.0) without modifying it. [Beukers–Stewart, *Neighboring powers*](https://doi.org/10.1016/j.jnt.2009.09.006) studies separations of pairs of powers; [Zhu's prime-base setting, Section 8](https://aixiv.online/pdf/2611.00013) discusses a related pattern for prime powers. The fifth-power base here is composite for every \(n\ge2\), so this does not resolve the prime-base problem. It also does not give an upper bound on the unrestricted interval counts, exclude all four-power intervals, or establish that \(1/\sqrt5\) is the best possible constant among all constructions.

The [finite checker](verify_factor_stewart_all_starts_endpoint.js) compares exact integer inequalities for the first 10,000 parameters, including both signs and every ordering. The asymptotics and the fourth-power exclusion follow from the proof, not from the finite counts.
