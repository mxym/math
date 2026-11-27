# The sharp lower-limit versus upper-limit curve for consecutive LCMs

Let \(A=\{a_1<a_2<\cdots\}\) be an infinite subset of the positive integers, and put
\[
G_A(X)=\#\{i:\operatorname{lcm}(a_i,a_{i+1})\le X\},\qquad
\alpha=\liminf_{X\to\infty}\frac{G_A(X)}{\sqrt X},\qquad
\beta=\limsup_{X\to\infty}\frac{G_A(X)}{\sqrt X}.
\]
For \(t>0\), let \(w(t)=1/\lceil t^2\rceil\). Define
\[
\Gamma=\int_0^\infty w(t)\,dt
=\sum_{j\ge1}\frac{\sqrt j-\sqrt{j-1}}j
=\sum_{j\ge1}\frac1{\sqrt j\,(j+1)}.
\]

**Theorem.** Every such sequence has \(0\le\alpha\le1,\ \alpha\le\beta\le\Gamma\). If \(\alpha>0\), it satisfies
\[
\boxed{\qquad \beta+\alpha\int_{\beta/\alpha}^{\infty}w(t)\,dt\ \le\ \Gamma .\qquad} \tag{1}
\]
For every fixed \(\alpha_0\in(0,1]\), the unique \(b\in[\alpha_0,\Gamma]\) for which (1) is an equality at \((\alpha_0,b)\) is attained by a **single infinite** \(A\) with \((\alpha,\beta)=(\alpha_0,b)\). At \(\alpha_0=0\) the maximum upper limit is \(\Gamma\), also attained. Thus (1) gives the exact upper boundary for prescribed lower limit, not just an estimate in either endpoint regime.

Equivalently, the boundary is parametrized by \(r\in[1,\infty)\):
\[
(\alpha,\beta)=
\left(\frac{\Gamma}{r+\int_r^\infty w(t)\,dt},
\frac{\Gamma r}{r+\int_r^\infty w(t)\,dt}\right).
\]
It is piecewise linear, with knots at \(r=\sqrt j\). For example, along the optimal boundary \(\Gamma-\beta\sim\alpha^2/\Gamma\) as \(\alpha\downarrow0\), and its first segment is \(\beta=2\Gamma-(2\Gamma-1)\alpha\) when \(1\le\beta/\alpha\le\sqrt2\).

[Erdős and Szemerédi, Mat. Lapok 28 (1980), Theorems I and II](https://www.renyi.hu/~p_erdos/1980-15.pdf) study the individual limits and show, in particular, that attaining the largest possible upper limit forces zero lower limit. See also [van Doorn's note on the upper estimate](https://github.com/Woett/Mathematical-shorts/blob/main/Sequences%20with%20bounded%20lcm%20for%20consecutive%20elements.pdf) and [Erdős problem 440](https://www.erdosproblems.com/440). The contribution here is the sharp simultaneous inequality and its attainment at every prescribed lower limit. This does not address the open larger-window problem [#873](https://www.erdosproblems.com/873).

## 1. Allocating gap lengths across thresholds

Fix \(T>1\). Consider an edge \((u,v)=(a_i,a_{i+1})\), its integer gap \(g=v-u\), and its threshold \(z=\operatorname{lcm}(u,v)/T^2\). The elementary estimate
\[
g z\ \ge\ uv/T^2 \tag{2}
\]
follows from \(\gcd(u,v)\mid(v-u)\). When the edge lies entirely in the band \([\sqrt{j-1}T,\sqrt j T]\), we have \(uv/T^2>j-1\) (also for \(j=1\), since \(u>0\)). Thus \(j\le\lceil gz\rceil\le g\lceil z\rceil\). On its interval, the edge uses normalized capacity
\[
\int_u^v w(x/T)\,dx=\frac gj\ \ge\ \frac1{\lceil z\rceil}. \tag{3}
\]
A band endpoint has measure zero and has no effect on this calculation. In particular an internal edge with \(z\le1\) uses at least one unit of capacity. All edge intervals have disjoint interiors, so their total capacity is at most \(T\Gamma\).

For any fixed positive integer \(K\), this gives the simultaneous estimate
\[
G_A(T^2)+\sum_{k=1}^K
\frac{G_A(kT^2)-G_A(T^2)}{k(k+1)}
\ \le\ \Gamma T+o_K(T), \tag{4}
\]
with the error uniform in \(A\). Here is the boundary control needed to apply (3). Keep edges inside one of the first \(J=\lfloor T^{1/3}\rfloor\) bands. At most \(2J\) excluded edges meet one of the first \(J\) positive band boundaries. To bound the rest with \(u\ge\sqrt J T\) and \(\operatorname{lcm}(u,v)\le KT^2\), divide starting values into dyadic intervals \([U,2U)\). Formula (2) gives a minimum gap \(U^2/(KT^2)\). Disjointness of the intervals, allowing one that exits the dyadic interval to the right, gives at most \(1+KT^2/U\) starts in that interval. All starts are at most \(KT^2\), so the total is \(O_K(\log T+T/\sqrt J)=o_K(T)\). Each excluded edge contributes at most one to the left of (4). For an included edge with \(z\le1\), the left side charges one unit. For one with \(z>1\), it charges
\[
\sum_{\substack{k\le K\\ k\ge z}}\frac1{k(k+1)}
\ \le\ \sum_{k\ge\lceil z\rceil}\frac1{k(k+1)}
=\frac1{\lceil z\rceil};
\]
this is covered by (3).

## 2. The upper boundary

Formula (4) gives \(\beta\le\Gamma\). Let \(T\to\infty\) on a sequence along which \(G_A(T^2)/T\to\beta\). For each fixed \(k\ge1\) the nonnegative difference in (4), divided by \(T\), has lower limit at least \((\alpha\sqrt k-\beta)_+\), by the definition of \(\alpha\). For fixed \(K\) take the limit inequality, then let \(K\to\infty\). This proves
\[
\Gamma-\beta
\ \ge\ \sum_{k\ge1}\frac{(\alpha\sqrt k-\beta)_+}{k(k+1)}
\ =\ \alpha\int_{\beta/\alpha}^\infty w(t)\,dt
 \qquad(\alpha>0).
\]
The equality follows by integrating the nonnegative terms of
\(w(t)=\sum_{k\ge1}\mathbf 1_{t\le\sqrt k}/(k(k+1))\).
Since \(r=\beta/\alpha\ge1\) and \(r+\int_r^\infty w(t)\,dt\) equals \(\Gamma\) at \(r=1\) and is strictly increasing on \([1,\infty)\), it follows that \(\alpha\le1\). If \(\alpha=1\) then \(\beta=1\).

For fixed \(a\in(0,1]\) the map \(y\mapsto y+a\int_{y/a}^\infty w(t)\,dt\) is continuous and strictly increasing on \([a,\Gamma]\), since \(w(t)\le1/2\) for \(t>1\). Its value at \(a\) is \(a\Gamma\), and its value at \(\Gamma\) exceeds \(\Gamma\). The unique equality point \(b\) therefore exists. At a fixed \(y\), the map \(a\mapsto a\int_{y/a}^\infty w(t)\,dt\) is strictly increasing for positive \(a\): increasing \(a\) increases the leading factor and extends the interval of a positive integral. Thus an actual sequence with \(\alpha\ge a\) and \(\beta\ge b\) must have equality in both.

## 3. Attaining the boundary with one infinite set

Take any \(a\in(0,1)\), let \(b\) be the unique equality point, and put \(r=b/a>1\). Fix integers \(R_m\to\infty\), all \(>r\). Choose integers \(T_m\to\infty\) rapidly enough that
\[
B_{m-1}=R_{m-1}T_{m-1}=o(T_m),\qquad R_m^2=o(\sqrt{T_m}),\qquad B_m=R_mT_m<T_{m+1}.
\]
Set \(B_0=0\). Include all integers outside the disjoint intervals \((T_m,B_m]\). Within each of these intervals, the construction uses only the following two kinds of pieces.

1. Partition the integer positions first into bands \((\sqrt{j-1}T_m,\sqrt j T_m]\), \(2\le j\le R_m^2\), and split any band at \(rT_m\). Partition each resulting integer segment into consecutive cells of length \(H_m=\lfloor\sqrt{T_m}\rfloor\), except possibly a final shorter cell.
2. In a cell below or at \(rT_m\), include only the multiples of its band index \(j\). In a cell above \(rT_m\) of length \(d\), include all integers in its first \(\lfloor a d\rfloor\) positions and include only multiples of \(j\) on the remaining positions.

Every pair of successive multiples of \(j\) **within a sparse piece** is consecutive in \(A\), and has least common multiple \(uv/j\le T_m^2\) because \(v\le\sqrt j T_m\). A sparse subinterval with integer length \(d'\) contributes at least \(d'/j-O(1)\) such pairs. Every pair of consecutive integers within a dense piece is also consecutive in \(A\); it has least common multiple \(uv\), so gets counted at \(q^2T_m^2\) whenever \(v\le qT_m\).

There are \(L_m=O(R_m T_m/H_m+R_m^2)\) cells in the \(m\)-th active interval. Integer and cell-end errors in the following estimates are \(O(L_m+H_m+1)=o(T_m)\), uniformly for the cutoff \(q\). In detail, rounding each band or split endpoint changes its length by at most two, and each cell contributes an \(O(1)\) error to its sparse or dense pair count. When taking only dense integers with \(v\le qT_m\), at most one cell is partially included, so omitting it costs at most \(H_m\).

The pairs from the initial dense stretch \((B_{m-1},T_m]\) and all sparse pieces of stage \(m\) are counted at \(T_m^2\); their number is at least
\[
T_m\left[1+\int_1^{R_m}\big(1-a\,\mathbf 1_{t>r}\big)w(t)\,dt\right]
-O(B_{m-1}+L_m+1)
=(b-o(1))T_m. \tag{5}
\]
The equality uses \(1+\int_1^\infty w=\Gamma\), the equation for \(b\), and the vanishing integral tail beyond \(R_m\). No pairs crossing between pieces are needed. In particular \(\beta\ge b\). For \(1\le q\le R_m\), the dense pieces inside the active interval contribute at least
\[
a(q-r)_+T_m-O(L_m+H_m+1)
\]
additional pairs at \(q^2T_m^2\), disjoint from those counted in (5). Consequently
\[
G_A(q^2T_m^2)\ \ge\ \big(b+a(q-r)_+-o(1)\big)T_m
\ \ge\ (a q-o(1))T_m,
\]
uniformly on this whole range. If \(B_m\le\sqrt X\le T_{m+1}\), the dense stretch after \(B_m\) adds at least \(\sqrt X-B_m-O(1)\) disjoint pairs to the preceding bound at \(X=B_m^2\). Since \(a\le1\), this still gives \(G_A(X)\ge a\sqrt X-o(T_m)\). The two ranges cover every sufficiently large \(X\), so \(\alpha\ge a\). Section 2 now forces \((\alpha,\beta)=(a,b)\).

For \(a=1\) take \(A=\mathbb N\). For \(a=0\), use the same stages with all active cells sparse (no \(r\) cutoff or dense fraction); the lower bound (5) then gives \(\beta\ge\Gamma\). Formula (4) gives \(\beta=\Gamma\), and any positive \(\alpha\) would contradict (1), so \(\alpha=0\).

## 4. Shape near the endpoints

On a band where \(\sqrt{j-1}\le r\le\sqrt j\), the integral from \(r\) to infinity is affine in \(r\) with slope \(-1/j\); this gives the piecewise-linear description in the theorem. On the first nontrivial band \(1\le r\le\sqrt2\), it equals \(\Gamma-1-(r-1)/2\), giving \(\beta=2\Gamma-(2\Gamma-1)\alpha\). At the other end, \(w(t)=t^{-2}+O(t^{-4})\) for \(t\ge1\). Hence \(\int_r^\infty w(t)\,dt=1/r+O(r^{-3})\) and the equality curve has \(\Gamma-\beta\sim\alpha^2/\Gamma\). In particular the loss from maximal upper limit is quadratically small, but not smaller, when a small positive lower limit is imposed.

The [companion checker](verify_erdos440_lcm_tradeoff.js) tests the finite weighted inequalities, band and threshold rounding, dyadic tail packing, dense-versus-sparse block counts and disjointness. The asymptotic theorem rests on the proof above, not on the finite tests.
