# Limits of centered rational-secant certificates on integer boards

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review or priority claim.

This addresses a particular proof architecture, not Dudeney's unrestricted no-three-in-line maximum. On the centered board \([-N,N]^2\cap\mathbb Z^2\), consider only lines having primitive integer direction \(d\), \(h(d)=\|d\|_\infty\le L\), and \(|\det(d,P)|\le B=\lceil N/L\rceil\) for points \(P\) on the line. Assume \(L\to\infty\) and \(L=o(N)\). A centered certificate consists of chosen sites such that every unchosen board site lies on one of these lines through at least two chosen sites. Its smallest unrestricted size is
\[
\Theta(L^2+B\log L).
\]
Optimizing over \(L\) gives order \((N\log N)^{2/3}\) in this single-center short/small-intercept architecture. Moreover, for any set with at most two chosen points per row, this architecture can cover only \(O(N^2/\sqrt L)\) board sites. The latter estimate holds for any center in the board, not just the origin. Thus a no-three-in-line set cannot use it to certify maximality unless it uses at least \(\Omega(\sqrt L)\) different centers, or admits lines outside the specified cutoffs.

The hyperbolic construction using one center, and a different recursive approach bypassing its logarithm in the unrestricted geometric domination problem, are documented in [this first-hand rStation report](https://rstation.ai/r/no_three_in_line/posts/135). The result here is a lower bound for the single-center architecture, even if the chosen sites and the allowed secants are selected arbitrarily, together with the row-cap obstruction. It is not a new bound on unrestricted geometric domination, and it does not prove \(D(n)<2n\) for the classical maximum. For the continuing classical gap see [Ghosal–Goenka–Grebennikov–Keevash–Kwan–Pham](https://arxiv.org/abs/2607.05255).

## Many lines are forced by a determinant comparison

Orient primitive directions consistently to avoid duplicates. For every such \(d\) of height \(\le L/32\) and every integer \(c\in[B/64,B/32]\), the line \(\det(d,P)=c\) contains several integer targets \(P\) with \(\|P\|_\infty\ge N/4\). Indeed primitivity gives an integer solution; all integer solutions then differ by integer multiples of \(d\). In a dominant coordinate of \(d\), choose values in \([N/4,N/3]\) in its residue class modulo \(h(d)\). There are at least three for large \(N\) because \(L=o(N)\); the other coordinate has absolute value at most \(N/3+B/(32h(d))<N\).

A permitted direction \(d'\) for such a target has \(|\det(d',P)|\le B\). The two-dimensional determinant identity yields
\[
|\det(d,d')|\|P\|_\infty
\le h(d)|\det(d',P)|+h(d')|\det(d,P)|
\le LB/16<N/4.
\]
A nonzero \(\det(d,d')\) would be an integer of absolute value at least 1, impossible. Thus every permitted line through the target is the same ordinary line. If the forced line had fewer than two chosen sites, it has an unchosen test target, not covered. Thus every such line must have a pair of chosen sites.

For a dyadic scale \(H\le h(d)<2H\) below \(L/32\) there are \(\Omega(H^2)\) primitive orientations for all large \(H\): count \((a,b)\) with \(H\le a<2H\), \(1\le b\le H\) and \(\gcd(a,b)=1\) by Möbius inversion, giving \(6H^2/\pi^2+O(H\log H)\). There are \(\Omega(B)\) intercepts per direction since \(B\to\infty\). Give each site-line incidence weight \(H^{-2}\) within that shell. Every shell therefore requires total weight \(\Omega(B)\).

At a site \(X\) with radius \(\rho=\|X\|_\infty\), a forced incidence requires \(\rho\ge B/(256H)\) by the lower bound on \(c\) and \(|\det(d,X)|\le 4H\rho\). The signed intercept bound confines the direction to angular intervals of length \(O(B/(H\rho))\) about the radial line. Distinct primitive directions in the shell have angular separation \(\Omega(H^{-2})\), because their integer determinant has absolute value at least 1. Consequently the weighted incidence cost at that site is \(O(H^{-2}+B/(H\rho))\); the origin has no forced incidences. Summing dyadically over \(H\) satisfying the radial lower bound costs \(O(1)\) per site. Since there are \(\Omega(\log L)\) forced shells, the chosen set has size \(\Omega(B\log L)\).

On the top forced shell \(H\asymp L\), any two distinct integer points on a line of primitive direction \(d\) are at sup-distance at least \(h(d)\ge H\). At least one of its two chosen sites therefore has radius \(\rho\ge H/2\). Charge only that incidence. Its cost per site is \(O(B/H^2)\), while the demand is \(\Omega(B)\), giving the second lower bound \(\Omega(L^2)\).

## The matching centered construction

Include the integer sites with \(|x|\le L,\ |y|\le L+B/\max(1,|x|)\) and their transposes, intersected with the board. Summing their row widths gives \(O(L^2+B\log L)\). For a target with \(|X|\ge |Y|\) and \(X\ne0\), Dirichlet approximation to \(Y/X\) gives a primitive slope \((b,a)\), \(1\le b\le L,\ |a|\le b\), with \(|bY-aX|\le B\); reducing a not-yet-primitive pair only lowers the intercept bound. The origin uses any horizontal secant. Write \(c=bY-aX\). The integer solutions \(b y-a x=c\) include distinct representatives with abscissas \(u,u-b\) for \(0\le u<b\), and at either representative the ordinate obeys \(|y|\le |x|+B/b\). Thus both are in the displayed hyperbolic region and on the board for large \(N\), since \(L+B=o(N)\). For steep directions transpose the coordinates. This attains the stated order. The minimizing order of \(L\) is \((N\log N)^{1/3}\); for a lower bound, \(L\le N^{1/4}\) already makes \(B\) too large, and for \(L>N^{1/4}\) one may replace \(\log L\) by a constant fraction of \(\log N\) before balancing.

## With two points per row, the covered fraction tends to zero

Allow a center \(O\) anywhere on the board; an eligible line then has \(|\det(d,P-O)|\le B\). At a direction shell \(H\le h(d)<2H\), there are \(O(BH^2)\) eligible lines even before demanding two chosen sites, because a fixed primitive orientation has \(O(B)\) possible integer intercepts in the translated interval. Each can cover only \(O(N/H)\) board sites.

A better line count in large shells follows by charging any secant to its chosen endpoint of larger radius around \(O\), which has \(\rho\ge H/2\). With \(\rho\le B/H\) there are \(O(B/H)\) such sites by the row cap (if this range exists), and at most \(O(H^2)\) directions per site. With \(\rho>B/H\) each charged site contributes at most \(O(1+BH/\rho)\) directions by the angular separation argument. There are \(O(N)\) chosen sites, and the sum of \(1/\rho\) in the charged range is \(O(\log L)\): every radius-\(R\) box about \(O\) contains \(O(R+1)\) chosen sites, and the ratio of the largest radius to \(\max(1,B/H)\) is \(O(L^2)\). Thus the line count in this shell is \(O(N+BH\log L)\).

For \(H\le\sqrt L\) use the first line bound, giving a summed cover \(\sum O(BNH)=O(N^2/\sqrt L)\). For \(H>\sqrt L\) use the second, giving \(\sum O(N^2/H+BN\log L)=O(N^2/\sqrt L)\), since \((\log L)^2/\sqrt L\) is bounded. The estimates are uniform in \(O\). Even if every chosen site is exempted from coverage, a maximal cap requires certifying all but \(O(N)\) of the \(\Theta(N^2)\) board sites. A union of centered certificates for \(k\) centers with the same cutoffs covers at most \(O(kN^2/\sqrt L)\), forcing \(k=\Omega(\sqrt L)\) to certify all of them.


## Sharpness under row and column caps alone

The \(O(N^2/\sqrt L)\) coverage bound is sharp already with one chosen point per row **and** per column, if no restriction on other lines through the chosen sites is imposed. Set \(H=\lfloor\sqrt L\rfloor\). Take all primitive \(d=(a,b)\) with \(H\le a,b<2H\) and intercepts \(c\in[B/64,B/32]\). There are \(\Theta(BH^2)=\Theta(N)\) such lines; each has \(\Theta(N/H)\) integer targets in each of the two strips with \(x\in[N/8,N/6]\) or \(x\in[-N/6,-N/8]\), respectively. They are on the board with \(y\) of the same sign as \(x\), since the slope is between \(1/2\) and 2 and the intercept correction is \(o(N)\).

Use a three-partite hypergraph whose nodes are lines, rows and columns, with one hyperedge for an available line-site incidence in the positive strip. A line has degree \(O(N/H)\). For a fixed row \(y\) and a fixed \(b\in[H,2H)\), a direction \(a\in[H,2H)\) and intercept \(c\) must obey \(ay\equiv c\bmod b\). With \(g=\gcd(y,b)\), only multiples of \(g\) are eligible \(c>0\); there are at most \(B/g\) of them, and each has at most \(g\) preimages \(a\) in an interval of length \(H\le b\). Thus a row has degree \(O(BH)=O(N/H)\); the same argument for columns exchanges the variables. Since the number of hyperedges is \(\Omega(N\cdot N/H)\), a greedy matching of size \(\Omega(N)\) follows by charging at most three times the maximum degree per matched edge. It chooses distinct positive endpoints on \(\Omega(N)\) lines. Repeat on those lines in the negative strip; it retains \(\Omega(N)\) lines with two endpoints and no shared row or column, including across strips.

The resulting lines cover disjoint sets of targets in the positive strip. If two distinct nonparallel directions met there, the determinant comparison would give \(\|P\|_\infty\le O(HB)=o(N)\), contradicting \(x\ge N/8\); parallel distinct lines cannot meet. So the covered count is \(\Omega(N\cdot N/H)=\Omega(N^2/\sqrt L)\), matching the upper bound for all admissible \(L\). This sharpness construction is for the row/column-cap relaxation, not for general-position caps.
