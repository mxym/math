# Exact packing density of the permutation pattern 21354

Let $\beta$ be the real root of $40\beta^3-32\beta^2+9\beta-1=0$. The packing density (the limiting maximum fraction of five-subsets inducing the pattern) is exactly
\[
p(21354)=\frac{15}{2}\,\beta^2(1-2\beta)(8\beta^2-4\beta+1).
\]
The four decreasing layers of masses $(\beta,1/2-\beta,1/2-\beta,\beta)$ and this *lower bound* are precisely those of Sliačan and Stromquist (2018, Table 2). We prove the matching upper bound, with a small exact rational computer-assisted step. No characterization of all maximizing permutons or finite permutations is asserted.

**1. Finite-dimensional reduction.** The pattern is layered, of type $[2,1,2]$. By the classical layered packing reduction (Stromquist; Albert–Atkinson–Handley–Holton–Stromquist, 2002, Theorem 2.2), some maximizing permutation at each order is layered. The associated Price polynomial, before multiplication by $5!/(2!2!)=30$, is
\[
F(x)=\sum_{i<j<k} x_i^2 x_j x_k^2,\qquad x_i\ge0,\quad \sum x_i=1.
\]
For block lengths $n_i$, the exact number of copies is $\sum_{i<j<k}\binom{n_i}2 n_j\binom{n_k}2$. Bounding the binomials by $n_i^2/2$ shows the normalized pattern density is at most $30 n^5/(n)_5$ times the supremum of $F$ over all finite partitions. Conversely any fixed finite partition is realized in the limit by rounding the layer sizes. Thus it suffices to optimize $F$ over all **finite** layer caps; no separate bounded-type assertion is assumed.

For each cap $M\ge4$, choose a maximizer of $F$ on the compact $M$-simplex with minimal positive support, and discard zero entries; write $s$ for its support size. Its density $30F$ exceeds $33/200$ by testing $(19/50,3/25,3/25,19/50)$. In particular $s\ge4$: for $s=3$, $F=x_1^2x_2 x_3^2\le(2/5)^4(1/5)$ by weighted AM–GM. The two endpoints $u=x_1$, $v=x_s$ are each at most $2/5$. Indeed, fixing the relative sizes of all other layers makes $F=u^2(1-u)^3 A+(1-u)^5 B$ for nonnegative $A,B$, with $A>0$; it decreases for $u>2/5$. Reverse to get the other bound.

**2. Local necessary conditions.** For an adjacent pair $a=x_i,b=x_{i+1}$ let $L,R$ be the sums of squares strictly to the left and strictly to the right, respectively. Let $C$ be the sum of $x_h^2x_j$ over $h<j$ both strictly to the left plus the sum of $x_jx_k^2$ over $j<k$ both strictly to the right. With $a+b$ fixed, the part of $F$ depending on the split, up to a constant, is
\[
(a^2+b^2)C+a^2bR+ab^2L .
\]
This gives three tests:
\[
2C<aR+bL,\qquad (a-b)(R-L)\ge0,\qquad
2(a-b)C+(2ab-a^2)R+(b^2-2ab)L=0.\tag{1}
\]
They follow by comparison with merging (strict since minimal support), swapping, and first variation, respectively. These observations and the next shape restrictions follow the layer-merging method of Hästö (2002, §4, especially Lemma 4.1). The second test implies a valley shape $x_1\ge\cdots\ge x_t\le\cdots\le x_s$: as the pair moves right the quantity $R-L$ strictly decreases, and its possible single zero allows only one freely ordered pair. At the first pair $L=0$ and $R>0$, so $a\ge b$ and the last test implies $a\ge2b$; reversing gives $x_s\ge2x_{s-1}$. Thus every interior size is at most $\max(u,v)/2$.

**3. A uniform ten-layer bound.** Suppose $s\ge5$. Choose a minimum $a=x_t$ and orient the list so its smaller neighbor $b=x_{t+1}$ is on the right. Both neighbors exist by the endpoint bounds. We can require $L\ge R$ for this pair: if $a<b$ this follows from (1). If $a=b$ but $L<R$, reverse the list and designate the old $b$ as the new minimum; the new right neighbor equals it, the left neighbor is no smaller, and the square sums are swapped. All left layers are at least $b$ by the valley shape and choice of side. The merge test gives $C<bL$. If $t\ge4$, the left part of $C$ alone is at least
\[
b\sum_{h=1}^{t-2}(t-1-h)x_h^2\ \ge\ b\bigl(2x_1^2+\sum_{h=2}^{t-2}x_h^2\bigr)\ \ge\ bL,
\]
the last step using $x_1\ge x_{t-1}$. Therefore $t\le3$. In particular $v$ lies strictly right of the pair, and
\[
v^2\le R\le L\le 5u^2/4.
\]
Here $L$ contains at most two terms and $x_2\le u/2$. Since $a,b\le\max(u,v)/2$, the total square mass is at most $2L+2\max(u,v)^2/4\le25u^2/8$.

Apply the strict merge test to the last two layers. Its right sum vanishes; its left contribution to $C$ includes $u^2(1-u-v-x_{s-1})$. Hence
\[
(25/8)u^2 v>2u^2(1-u-v-x_{s-1})\ge 2u^2(1-u-3v/2).
\]
In particular $v>16(1-u)/49\ge48/245$, so $u/v<49/24$. Return to the chosen minimum pair. The right part of $C$ includes all terms with $k=s$, giving at least $(s-t-2)b v^2$, since each of the $s-t-2$ preceding right layers is at least $b$. Using $C<bL$ yields
\[
s<t+2+\frac54(49/24)^2<11 .
\]
These estimates hold uniformly for each cap $M$. The fact that zero coordinates were discarded matters: the strict merge test is only used on **positive** layers.

**4. Short exact cover.** The rest is an integer box certificate in [cert.py](cert.py). It concerns at most 10 layers, and does not assume the maximizing list is symmetric. Here are the full covering and exclusion rules. Reverse the list if necessary to make $x_1$ its larger endpoint. Rescale it to $K=1024$. By §2 the interiors are in $[0,K/2]$, and the last layer in $[0,K]$. The total is at least $5K/2$ by §1. For $s=4,\ldots,10$, try each possible interior valley position and cover the resulting real box. All three tests (1) are homogeneous individually, so they remain valid after rescaling. The benchmark condition is $6000F\ge33(\sum x_i)^5$. Given a closed box of integer endpoints $l_i,h_i$:
1. Intersect with valley and endpoint order restrictions, rounding tightened half-bounds **outward**. Reject empty boxes, insufficient maximum total or $6000F(h)<33(\sum l_i)^5$.
2. For each adjacent pair, evaluate $L,R,C$ on $l$ and $h$ to enclose these nonnegative polynomials. Reject if the strict merge inequality or weak swap inequality is impossible. To enclose the derivative, the range of $x(2y-x)$ for nonnegative $x\in[a,A],y\in[b,B]$ is bounded by taking its minimum at $y=b$ and $x\in\{a,A\}$, and maximum at $y=B$, $x\in\{a,A\}$ or $x=B$ if admissible. Combine these intervals by signed interval arithmetic and reject if zero is excluded.
3. For $s=4$ retain a box, without further splitting, if it lies entirely in the following root neighborhood after division by $K$: for $(x_1,x_2,x_3,x_4)/K=(1,b,c,d)$,
\[
\mathcal B=[300/1024,326/1024]^2\times[1010/1024,1].
\]
Else split the widest interval into two **closed overlapping at their common endpoint** subintervals with integer midpoint rounded down (choose the first coordinate in a tie). The program fails explicitly if it encounters an undecided box of width at most one. Real variables are never rounded to a grid.

Visiting respectively 622, 7303, 478, 541, 846, 1299 and 1840 boxes for $s=4,\ldots,10$, these rules discard everything except fourteen boxes inside $\mathcal B$ when $s=4$. See [CHECKS.txt](CHECKS.txt). The lists were finite global maximizers, so possible local stationary points with less than the benchmark need not be classified.

**5. Unique stationary solution in the retained box.** For four positive layers $(a,b,c,d)$, $F=a^2d^2(b+c)+a^2bc^2+b^2cd^2$. Define $G_i=(\partial_iF-\partial_{i+1}F)|_{a=1}$, $i=1,2,3$, with variables $b,c,d$, and let $J=DG$. Homogeneity and stationarity give $G=0$. Use the fixed matrix
\[
B=\frac1{1000}\begin{pmatrix}461&-627&94\\185&822&-181\\905&629&905\end{pmatrix}.
\]
Expanding each entry of $I-BJ$ into monomials and evaluating its positive and negative coefficients separately at the corners of $\mathcal B$ gives the upper bounds
\[
1414554361/4194304000,\quad18454510611/67108864000,\quad27713441227/67108864000
\]
on its three absolute row sums. Each is $<1$. The checker forms these polynomials by differentiating the four-layer objective; no floating point arithmetic is involved. The map $y\mapsto y-BG(y)$ is thus Lipschitz with constant $<1$ on this convex box, so it cannot have two fixed points there (we need no self-mapping assertion). This proves uniqueness of a root if one is found.

On the symmetric slice $(a,b,c,d)=(1,r,r,1)$ the components of $G$ are $g(r),0,-g(r)$ with $g(r)=2r^3-3r^2+4r-1$. This cubic is strictly increasing, and has opposite signs at $300/1024$ and $326/1024$. Its root gives the only possible maximizer after rescaling. Set $\beta=1/(2+2r)$ to get the stated masses and defining cubic; substitution in $30F$ gives the displayed density. This completes the proof.
