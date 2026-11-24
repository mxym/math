# Dense coprime slope cliques survive true sieve normalization: a one-coordinate completion obstruction

Research note, 2026-11-24. This does **not** construct a multiplicative function or a counterexample involving the actual Liouville function. It shows that the genuine dense coprime target graph has a direction which is invisible to standard independent one-coordinate Fourier and progression bounds, even with the exact actual prime slopes and both rough constraints. One cannot expect to complete the actual double-slope parity estimate using only such bounds on the reflected sequence.

## 1. A dense family of disjoint cliques on actual reflected integers

Use the fixed-target \(G_{23}\) setting: \(P\) large even, \(L=\log P\), \(\operatorname{rad}(P)\le L^B\), \(I=[uP,vP]=PJ\) for fixed \(0<u<v<1\), \(y=e^{L^\delta}\) with \(0<\delta<.1\), \(z=e^{L^{.24}}\). Write \(R_t(n)=1_{P^-(n)>t}\), \(\kappa_z=\prod_{\ell\le z}(1-1/\ell)\), and the usual \(V_y=V_y(P)\). The full real prime slope set is \(\mathcal P=\{P^\sigma<p\le D:\ p\text{ prime}\}\), \(0<\sigma<1/4\), \(D=P^{1/2}e^{-L^{3/5}}\). Let \(W(p,k)=1_{pk\in I}\log(pk)/L\). Work after the already verified exact total deletion of the translated mark; the graph still retains both rough masks and the actual \(I\).

Take the fixed width-positive angular window
\[
a_0=2/5,\qquad b_0=9/20,\qquad
\mathcal P_0=\{P^{a_0}<p\le P^{b_0}:\ p\text{ prime}\}\subset\mathcal P.
\]
Choose
\[
\mathcal K=\big\{vP/P^{b_0}\le k\le uP/P^{a_0}:\ R_z(k)=1,\ 
  \text{no prime in }\mathcal P_0\text{ divides }k\big\}.
\]
For each \(k\in\mathcal K\), define the clique of actual reflected vertices
\[
\mathcal C_k=\{P-pk:\ p\in\mathcal P_0,\ pk\in I,\ R_y(P-pk)=1\}.
\tag{1}
\]
These sets are **pairwise disjoint**: if \(m\) has a representation in (1), then \(n=P-m=pk\) has exactly one prime divisor from \(\mathcal P_0\), because the rest \(k\) contains none. That prime is determined by \(m\), and \(k=n/p\) is then determined. This uses the true factorization and not an approximate disjointness assumption. Each clique size is \(O_J(P/k)=O(P^{b_0})\). The window has fixed exponent width \(b_0-a_0=1/20\), not a single shrinking angular box.

We compute its genuine unsigned square-weight before analyzing signs. Put \(B_0(k)=\sum_{p\in\mathcal P_0}W(p,k)R_y(P-pk)\). For each \(k\) in the stipulated interval, the full physical \(I/k\) lies in \([P^{a_0},P^{b_0}]\). If \(R_z(k)=1\), [the earlier real prime BV argument](SmallRadicalWeightedCoprimeDispersion.md) for the unsigned slope normalization applies verbatim: each \(\ell\le y\), \(\ell\nmid P\), excludes exactly the one reduced residue \(Pk^{-1}\bmod\ell\). Open these classes by factorial Bonferroni at modulus \(P^{o(1)}\), apply maximal prime BV on the true \(P/k\) scale, and retain \(\log(pk)/L\) by partial summation. Thus uniformly,
\[
B_0(k)=\frac{P |J|V_y}{k L(1-\log k/L)}(1+O(1/L))
       +O_A((P/k)L^{-A})
\tag{2}
\]
on this interior \(k\)-range.

The extra condition no factor in \(\mathcal P_0\) has a substantial **constant** retention, not a vanishing rate. For \(x\) in the same polynomial range, there can be at most one \(\mathcal P_0\)-prime factor of any \(k\le x\) (even its square exceeds \(x\), since \(2a_0>1-a_0\)). As every such prime exceeds \(z\), the exact unsigned rough prefix with this exclusion is
\[
\sum_{k\le x}R_z(k)
-\sum_{r\in\mathcal P_0}\sum_{t\le x/r}R_z(t)
=\kappa_z x\left(1-\sum_{r\in\mathcal P_0}\frac1r\right)
 +O_A(x L^{-A}).
\tag{3}
\]
Every quotient endpoint \(x/r\gg P^{1-2b_0}=P^{1/10}\) is polynomial, so the ordinary integer rough density with arbitrary-log error applies uniformly; sum by reciprocals of the real \(r\)'s. Mertens gives \(\sum_{r\in\mathcal P_0}1/r=\log(b_0/a_0)+o(1)=\log(9/8)+o(1)<1\). Taking partial sums in (3), substituting (2), gives
\[
\mathcal U_0:=\sum_{k\in\mathcal K} k B_0(k)^2
\sim |J|^2\bigl(1-\log(b_0/a_0)\bigr)
          \left(\frac1{a_0}-\frac1{b_0}\right)
          \frac{P^2\kappa_z V_y^2}{L}.
\tag{4}
\]
Indeed put \(x=P^t\); the limiting integral is \(\int_{1-b_0}^{1-a_0}(1-t)^{-2}dt=1/a_0-1/b_0\), and the two fixed-factor interval edges shift \(t\) by only \(O(1/L)\). The actual squared count has power-small diagonal, by \(\sum_p(P/p)^2\ll P^{2-\sigma}\). The old genuine shared-gcd bound \(O(P^2 L/y)\) also applies to this subset; all these proofs only use absolute weights on the real rows. Thus (4) is of the same order on **coprime unequal** pairs within the cliques, and is a nonzero constant portion of the full unsigned \(G_{23}\) second-moment normalization.

## 2. One fixed-target bounded sign model with both one-coordinate smallness and large global coprime dispersion

Give each nonempty clique \(\mathcal C_k\) one independent Rademacher sign, and give each remaining \(y\)-rough integer in \([1,P]\) its own independent singleton sign. Define \(H(m)\) to be that sign on these groups and zero on nonrough integers (and outside \([1,P]\)). Thus \(|H(m)|=R_y(m)\) on the actual range. Only the signs have been replaced; the prime slopes, support masks, target and intersections are not synthetic.

Let \(M_*=\max(1,\max_k|\mathcal C_k|)\ll P^{b_0}\). For any deterministic bounded real or complex linear test on a set \(E\subset[1,P]\), with coefficients of absolute size at most one, write its sum against \(H\) as the sum over independent group signs. For real and imaginary parts the sum of squares of the group coefficients is at most
\[
\sum_{\mathcal C} |\mathcal C\cap E|^2
\le M_* |E|.
\tag{5}
\]
Hoeffding consequently gives \(O(\sqrt{M_*|E|L})\) simultaneously for every test in any given polynomial-sized family, by choosing the absolute constant in the bound sufficiently large. Each test has random expected centered sum zero. The following families can all be imposed on the same deterministic choice of signs.

* **Full additive frequency.** Take prefix endpoints \(X\in\{0,1,\ldots,\lfloor P\rfloor\}\) and a mesh of spacing at most \(P^{-3}\) on the full frequency torus. This is a polynomial family; (5) gives \(O(P^{(1+b_0)/2}\sqrt L)\) on it. The derivative in \(\alpha\) of \(\sum_{m\le X}H(m)e(m\alpha)\) is \(O(P^2)\) by the absolute coefficient bound, so the mesh extends to every real \(\alpha\) at additive error \(O(P^{-1})\). Differences cover all real interval endpoints, which reduce to integer endpoints anyway. This is smaller than \(PL^{-A}\) for any fixed \(A\), though not asserted to be of square-root size.
* **All ordinary progression endpoints and BV.** Take every integer \(q\le\sqrt P\), every residue \(a\bmod q\) (including nonunits), and every integer endpoint \(X\le P\). The family is polynomial in size, and \(E\) in (5) has at most \(P/q+1\) elements. Thus
\[
\max_{X\le P}\max_{a\bmod q}\left|\sum_{\substack{m\le X\\m\equiv a\bmod q}}H(m)\right|
\ll \sqrt{P^{b_0}(P/q+1)L}.
\]
Summing over the actual \(q\le\sqrt P\) gives \(O(P^{3/4+b_0/2}\sqrt L)=O(P^{39/40}\sqrt L)\), an arbitrary-log improvement over \(P\). These are **uncentered** bounds around zero. In the conventional reduced-class BV definition, subtracting the deterministic coprime mean \( \varphi(q)^{-1}\sum_{m\le X,(m,q)=1}H(m)\) at each actual endpoint preserves the bound with factor two, since this mean is an average of the already bounded reduced residue sums. There is no use of an unsigned rough density as a signed progression mean.
* **Full slope square despite extra slopes outside the window.** For each \(k\in\mathcal K\) and a real \(p\in\mathcal P\setminus\mathcal P_0\) with \(pk\in I\), \(pk\) has no \(\mathcal P_0\)-prime factor at all. Therefore \(m=P-pk\) is outside **every** chosen clique; if it is rough its sign is an independent singleton. As distinct \(p\)'s at this \(k\) give distinct \(m\)'s, the extra full-marker sum has true independent singleton variance \(O(P/k)\) (weights \(W(p,k)\) are bounded). Hoeffding and a union over all \(k\le P\) give
\[
\left|\sum_{p\in\mathcal P\setminus\mathcal P_0} W(p,k)H(P-pk)\right|
 \ll \sqrt{(P/k)L}
=o(B_0(k))
\]
uniformly in \(k\in\mathcal K\), by (2) and \(P/k\gg P^{a_0}\). The signs of these tests across different \(k\)'s need not be independent for the union bound.

Take a realization satisfying all these properties. For every \(k\in\mathcal K\) the \(\mathcal P_0\)-contribution is exactly the clique sign times \(B_0(k)\), and the remaining true slopes are \(o(B_0(k))\). Thus the **full** (not just window-restricted) slope moment with reflected sign replaced by \(H\) is at least
\[
\sum_k k R_z(k)\left|\sum_{p\in\mathcal P} W(p,k)H(P-pk)\right|^2
\ \ge (1-o(1))\mathcal U_0 .
\]
Removing its power-small diagonal and the absolute \(O(P^2L/y)\) shared-gcd bill leaves a positive dense coprime off-diagonal of order at least \(P^2\kappa_z V_y^2/L\). The full unsigned normalization is an upper bound on this order. No signed cancellation of a negative slice was assumed. Therefore one-sided additive Fourier and ordinary BV controls, even quantitative with power savings as above, cannot by themselves enforce the desired normalized \(o(L^{-88/25})\) coprime upper in this exact sampling graph.

## 3. Optional strengthening: true small-coefficient affine probes also miss the model

One can impose at the same time two-point cancellation for all distinct affine forms \(L_i(t)=a_i t+b_i\) with positive integer slopes and \(|a_i|,|b_i|\le P^{1/20}\), for integers \(1\le t\le X\le P\) with both images in \([1,P]\) (equivalently keep the zero extension of \(H\)). This does not assert the same with large growing slopes or intercept \(P\).

Indeed a pair of distinct images in the same **non-singleton** clique must satisfy \(k\mid P-L_i(t)\) for both \(i\). Hence
\[
k\ \mid\ a_2(P-b_1)-a_1(P-b_2).
\]
This integer is nonzero for all large \(P\): for unequal slopes its leading term has magnitude \(\ge P\), against error \(O(P^{1/10})\); for equal nonzero slopes the intercept difference is nonzero. Its magnitude is \(O(P^{1+1/20})\), so it has \(P^{o(1)}\) possible divisors. Each eligible \(k\gg P^{1-b_0}\) gives at most \(O(P \gcd(a_1,k)/k+1)\ll P^{b_0+1/20}\) choices of \(t\). Coincident images of distinct forms occur at most once. The expected two-point sum is therefore \(O(P^{b_0+1/20+o(1)})\): its summands have expectation zero unless the images share a sign group, and magnitude at most one otherwise.

Flipping one group sign changes at most \(2|\mathcal C|\) actual summands, because each map \(L_i\) is injective, and each summand changes in magnitude by at most two. The bounded-differences variance proxy is then \(O(\sum_{\mathcal C}|\mathcal C|^2)\ll P M_*\). The family of all these integer coefficient and endpoint probes is polynomial in size, so the same choice of signs can also have all their sums \(O(P^{(1+b_0)/2}\sqrt L)\); the expectation just bounded is smaller. This illustrates exactly why fixed or modestly growing affine probes do not reach the present common-intercept \(P\) with true slopes of size \(P^{a_0}\) or larger. It is a claim only about the explicitly constructed nonmultiplicative sign model, not about \(\lambda\).

The surviving arithmetic task is to show that the **actual completely multiplicative** \(\lambda\) has small conditional prime-slope means across these cliques, or to find a different sign argument avoiding their square. The model does not preserve multiplicativity, the actual values on primes, or arbitrary stronger mixed estimates; it is not a candidate counterexample to the Liouville bound itself.