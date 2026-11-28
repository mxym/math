# The sharp heptagonal obstruction for mixed quartic kissing energy

Set $f(t)=t^4-t^2/4$. For a finite $60^\circ$ unit-vector code, its capacity is the minimum of $\sum_{ij}p_ip_j f(x_i\cdot x_j)$ over probability weights. This note determines the maximum capacity among **all vertex-transitive seven-point codes**, in arbitrary dimension, and the maximum mean edge strength for a seven-cycle **without any symmetry assumption**. The same rank-four configuration is the unique maximizer of both problems.

Put $a=\cos(2\pi/7)$, $b=\cos(4\pi/7)$, $c=\cos(6\pi/7)$ and
\[
 w=(a-1/2)/(a-c),\qquad x=c+(b-c)w,\qquad z=b+(a-b)w .
\]
The sharp capacity is $[3/4+2f(x)+2f(z)]/7=0.200850277798\ldots$ (the omitted cost $f(1/2)$ is zero). Thus even the unrestricted seven-point upper bound cannot be lowered to $1/5$. For any seven cyclically ordered code points, the mean of $-x_i\cdot x_{i+1}$ is at most $-x=0.84601073\ldots$; this remains sharp if “mean” is replaced by “minimum.” Both conclusions are statements about seven **points**, not the seven-dimensional kissing number.

## The Fourier simplex and its exposed vertex

By averaging a Gram matrix over its seven cyclic shifts one obtains a PSD circulant matrix with the same mean products $g_j$ at lags $j=1,2,3$. Diagonalizing on the seven characters gives a convex combination with weights $p_0,p_1,p_2,p_3$ of the columns
\[
 (1,1,1),\quad (a,b,c),\quad (b,c,a),\quad(c,a,b).
\]
Conversely every such circulant matrix is realizable; its points are distinct if its off-diagonal entries are at most $1/2$. The combination $p=(0,0,w,1-w)$ has lags $(x,1/2,z)$ and rank four. It is realized by taking the two Fourier circles at frequencies 2 and 3 with radii $\sqrt w,\sqrt{1-w}$. The Fourier reduction itself is standard; compare [the earlier cycle-strength calculation, including the distinct sharp 15-cycle problem](KissingAntipodalCycleExtremal.md).

Let $u=(p_0,p_1,1/2-g_2)\ge0$, $r=(b-c)/(a-c)$ and $s=(a-b)/(a-c)$. Eliminating $p_2$ gives $g_1-x=A\cdot u$, $g_3-z=B\cdot u$, with
\[
 A=(1-c+r(1-a),\,a-c+r(b-a),\,r),\qquad
 B=(1-b+s(1-a),\,c-b+s(b-a),\,s).
\]
Each $A_i>0$ and $|B_i|<2A_i$, as checked by [the short rational scalar verifier](verify-kissing-heptagon-extrema.py), using the three disjoint root intervals of $8t^3+4t^2-4t-1$. In particular $g_1\ge x$ and $|g_3-z|\le2(g_1-x)$. Equality in the first bound forces $p=(0,0,w,1-w)$. This proves the mean bound already, since $g_2\le1/2$ for every ordered code.

**Rigidity before averaging.** At equality every individual lag-two entry is $1/2$. The averaged PSD matrix is supported on the complex characters $K=\{2,3,4,5\}$ modulo seven, so the original PSD matrix is also supported there: any vector in the kernel of the average lies in the kernel of every summand. The diagonal and lag-two diagonal uniquely specify every symmetric matrix on this Fourier support. Indeed, expand in symmetric pairs of characters with frequencies $(k,l)$. For each $h=k+l\bmod7$ at most two unordered pairs occur. The two given diagonals determine the sums of their coefficients with multipliers $1$ and $(\zeta^{2k}+\zeta^{2l})/2$, respectively, for $\zeta=e^{2\pi i/7}$ (absorbing multiplicity into the coefficients). Distinct pairs at fixed $h$ have distinct second multipliers: equal sums and the common product $\zeta^{2h}$ would identify both roots, and doubling permutes residues modulo seven. These systems therefore have full column rank. The original matrix equals its cyclic average. This proof does not assume that the seven individual edge products are already equal.

## The nonlinear capacity

A transitive permutation group of seven code points has a seven-cycle, by orbit–stabilizer and Cauchy's theorem. Its Gram matrix is already circulant in an appropriate order. The matrix $F_{ij}=f(x_i\cdot x_j)$ is positive semidefinite: embed the code in $\mathbb R^7$ and expand $f$ in normalized dimension-seven Gegenbauer polynomials of degrees $0,2,4$, with positive coefficients: $f=P_0/84+(39/154)P_2+(16/33)P_4$. Thus the mass energy is convex; averaging any probability vector over the cyclic action shows that uniform weights minimize. The capacity is $[3/4+2\sum_j f(g_j)]/7$.

At most one lag is strictly below $-1/2$: the strong graph has no triangle by the squared norm of a sum of three vectors, and two strong lags would give a four-regular graph on seven vertices, contradicting Mantel's bound of twelve edges. If none is strong the uniform cost is at most $3/28$. Otherwise an automorphism of the cyclic group makes the strong lag lag one. For $x\le t=g_1\le-1/2$,
\[
 f(t)-f(x)=(t-x)(t+x)(t^2+x^2-1/4)\le-\tfrac9{10}(t-x),
\]
since $x<-.84$. On $[-1/2,1/2]$, $|f'|\le1/4$ and $f\le0$. Consequently $f(g_2)\le f(1/2)=0$ and $f(g_3)-f(z)\le(g_1-x)/2$. The capacity is therefore strictly smaller off the stated vertex, and that vertex attains the displayed maximum. No averaging of a general nonlinear capacity is asserted: the unrestricted maximum is bounded **below**, not determined, by this example.

Run `python3 verify-kissing-heptagon-extrema.py` to check the rational inequalities.
