# Sharp quartic star energies and a one-variable reduction for spherical cap potentials

For unit vectors $x,y_1,\ldots,y_k$, suppose $y_i\cdot y_j\le1/2$ for $i\ne j$ and $a_i=-x\cdot y_i\ge1/2$. Put $f(t)=t^4-t^2/4$. These are precisely the local constraints on any chosen set of strong or threshold neighbors of a vertex of a $60^\circ$ code.

**Sharp star theorem.** Over all ambient dimensions,
\[
 \max\sum_{i=1}^k f(a_i)=
 \begin{cases}
 3/4 & k=1,\\
 49/64 & k=2,\\
 (k+1)(k+2)/(8k)&k\ge3.
 \end{cases}
\]
For $k\ge3$ equality has $y_i\cdot y_j=1/2$ for every distinct pair, and $-x$ is the unit vector in the direction $\sum_i y_i$. In particular the $k$ strengths are all $\sqrt{(k+1)/(2k)}$. For $k=2$ the equal-strength choice is **not** optimal: the two strengths are $(\sqrt{21}\pm1)/(4\sqrt2)$, again with $y_1\cdot y_2=1/2$. These configurations are unique up to isometry and permutation, attain the stated bound already in dimension $k$, and satisfy the strict inequalities $a_i>1/2$. In smaller fixed dimension the universal upper bound remains true, but the indicated equality configuration does not fit.

This is an exact extremum for a star and a particular potential, not a kissing number. The local cap-sum method itself is classical: see [Musin, especially §§5–6](https://annals.math.princeton.edu/wp-content/uploads/annals-v168-n1-p01.pdf) and [Barg–Musin on codes in caps](https://www.aimsciences.org/article/doi/10.3934/amc.2007.1.131). Musin treats more general fixed-dimension geometry and different kernels; we do not claim to replace those results. Here both the optimization over the cap center and the multipoint configuration reduce to one scalar for the potential class below.

## The one-variable cap maximum

More generally let $0<s<1$, $s\le\tau\le1$, $y_i\cdot y_j\le s$, and $a_i=e\cdot y_i\ge\tau$ for a unit vector $e$. Let $\phi$ be nondecreasing and $C^3$ on $[\tau,1]$, with $\phi'''\ge0$ there. Assume the cap admits $k\ge2$ points. Put $\theta=s/(1-s)$ and, for $0\le t\le1$, define
\[
 m(t)=\sqrt{\frac{1-s}{\theta+[1+(k-1)t^2]/k}},\qquad
 a_+(t)=m(t)\!\left(\theta+\frac{1+(k-1)t}{k}\right),\quad
 a_-(t)=m(t)\!\left(\theta+\frac{1-t}{k}\right).
\]
Then the exact maximum over ambient dimension at least $k$ equals
\[
 \max_{\substack{0\le t\le1\\ a_-(t)\ge\tau}}
 \{\phi(a_+(t))+(k-1)\phi(a_-(t))\}.
\]
In dimensions below $k$ this expression is an upper bound. Nonemptiness is equivalent in dimension at least $k$ to $\tau\le\sqrt{[1+(k-1)s]/k}$: use equal weights in the Gram bound below and the $t=0$ construction.

**Proof.** Choose the unique threshold $\mu>0$ for which $w_i=(a_i-\mu)_+$ satisfy $\mu=\theta\sum w_i$. Write $m=\sum w_i$ and $Q=\sum w_i^2$. The nonnegative weights give
\[
 (Q+\mu m)^2
 =\left(e\cdot\sum_i w_i y_i\right)^2
 \le \left\|\sum_i w_i y_i\right\|^2
 \le (1-s)Q+sm^2=(1-s)(Q+\mu m).
\]
Thus $Q+\mu m\le1-s$. Replacing $a_i$ by $\mu+w_i$ never decreases it. Scale all $w_i$ and $\mu$ together until $Q+\mu m=1-s$. At equality the new strengths are attainable: choose a neighbor Gram matrix $G_0=(1-s)I+s\mathbf1\mathbf1^T$ in dimension $k$ and set $e=(\sum w_i y_i)/(1-s)$. Then $\|e\|=1$ and $e\cdot y_i=\mu+w_i$. In particular every lifted strength is at most one.

Given $m,Q$, write $\sigma^2=Q/k-(m/k)^2$. Each $w_i$ is at most $u=m/k+\sqrt{k-1}\,\sigma$ by Cauchy on the other entries. Set $v=m/k-\sigma/\sqrt{k-1}$, so $v\ge0$ since $Q\le m^2$. Also $v\ge\min_i w_i$: apply $\sum z_i^2\le(\sum z_i)^2$ to $z_i=w_i-\min_j w_j$. The list $(u,v,\ldots,v)$ has exactly the original sum and sum of squares. If $\sigma=0$ there is nothing to prove. Otherwise interpolate $z\mapsto\phi(\mu+z)$ by the quadratic matching both value and derivative at $v$ and value at $u$. It majorizes on $[\min_i w_i,u]$ by the sign of the Hermite remainder $\phi'''(\xi)(z-v)^2(z-u)/6$. Its sum stays fixed under the two moment constraints, so the two-level list maximizes the potential. Its lower strength remains at least $\tau$. Writing $v=m(1-t)/k$ gives exactly the formulas above. Conversely each eligible $t$ is attained by the same $G_0$ construction. This proves both directions.

## Closed form for the quartic, including the exceptional pair

With $s=\tau=1/2$, write $H=k+1+(k-1)t^2$, $A=k+1+(k-1)t$ and $B=k+1-t$. The two strengths are $A/\sqrt{2kH}$ and $B/\sqrt{2kH}$; $a_-\ge1/2$ throughout. The quartic sum is $N/(8k^2H^2)$ with
\[
 N=2[A^4+(k-1)B^4]-kH[A^2+(k-1)B^2].
\]
For $k\ge3$ its derivative is negative at every $t>0$. Indeed,
\[
 2H'N-N'H=2kt(k-1)(k+1)\,P(t).
\]
Writing $n=k-3$, the four degree-three Bernstein coefficients of $P$ on $[0,1]$ are
\[
 (n+4)(3n^2+14n+7),\quad(n+3)(n+4)(3n+1),\quad
 \tfrac23(n+3)^2(4n+3),\quad2(n+3)^3 .
\]
All are positive, so only $t=0$ is optimal. The value there is the claimed $(k+1)(k+2)/(8k)$. For $k=2$ the same derivative numerator is $48t(7t^2-3)$, so $t=\sqrt{3/7}$ is the unique maximizer and gives $49/64$. For $k=1$, $a=1$ is necessary and sufficient. For equality at $k\ge2$, the optimal list has all $w_i>0$ (also for the exceptional pair). Strict monotonicity of $f$ excludes a strict increase in the lifting/scaling step; $f'''>0$ gives strict Hermite interpolation off the interpolation nodes. Equality in the Gram bound forces every $y_i\cdot y_j=1/2$ and equality in Cauchy determines the center. The [standalone symbolic checker](verify_kissing_quartic_star.py) checks the polynomial identities in the two indeterminates $k-3,t$, not a finite sample of orders.


## A quantitative penalty in lower dimension

When $k\ge3$ and the ambient dimension is $d<k$, the universal optimum above cannot even be approached arbitrarily closely:
\[
 C_k-\sum_i f(a_i)\ \ge\
 \min\!\left\{\frac{(k+1)^2}{256k^4},\
               \frac{k(k-d)}{384(k+1)^2}\right\}.
\]
Here the two terms come from different mechanisms. Use the **unscaled** $w,m,Q$ in the cap proof ($\mu=m$). If $\min_i w_i<m/(2k)$, some normalized coordinate differs from $1/k$ by at least $1/(2k)$. Hence the two-level parameter satisfies
$t^2=(kQ/m^2-1)/(k-1)\ge1/[4k(k-1)]$. This parameter is unchanged by scaling. The four Bernstein coefficients above are all at least $k(k+1)$ for $k\ge3$ (subtract $k(k+1)$ and expand in $k-3$); $H\le2k$. The displayed derivative identity implies
$-C'(t)\ge t(k-1)(k+1)^2/(32k^3)$ for the two-level value $C(t)$. Integration from zero yields the first penalty.

Otherwise $w_i\ge m/(2k)$ for all $i$. The average of the lifted strengths $m+w_i$ is at least $1/2$, so $w_i\ge1/[4(k+1)]$. Put $L=Q+m^2$. If $G$ is the actual neighbor Gram matrix, $\operatorname{rank}G\le d$ whereas $G_0=(I+\mathbf1\mathbf1^T)/2$ has every singular value at least $1/2$. Testing $G_0-G$ on an orthonormal basis of $\ker G$ gives $\|G_0-G\|_F^2\ge(k-d)/4$. Writing $\delta_{ij}=1/2-G_{ij}$ off the diagonal, we have $0\le\delta_{ij}\le3/2$ and thus $\sum_{i\ne j}\delta_{ij}\ge(k-d)/6$. Before scaling, Cauchy's inequality retains the loss
\[
 L(1/2-L)\ \ge\sum_{i\ne j}w_iw_j\delta_{ij}.
\]
Since $L\le1/2$ we get $1/2-L\ge(k-d)/[48(k+1)^2]$. Scaling the lifted strengths by $\sqrt{(1/2)/L}$ increases their quartic sum by at least $k(1/2-L)/8$: for $a\ge1/2$, $z\ge1$, one has $\tfrac{d}{dz}f(\sqrt z\,a)=2za^4-a^2/4\ge1/16$. The scaled configuration still obeys the universal optimum, proving the second term. 

## Joint cuts controlling the actual incident inner products

The formula also gives the exact support function of the possible pairs $(\sum a_i,\sum f(a_i))$ in nonnegative slope directions. For $\lambda\ge0$ and $k\ge1$, let $M_0=0$, $M_1=\max_{1/2\le a\le1}(f(a)-\lambda a)$, and for $j\ge2$ let
\[
 M_j=\max_{0\le t\le1}
  \big[f(a_+(t))+(j-1)f(a_-(t))-\lambda(a_+(t)+(j-1)a_-(t))\big]
\]
using order $j$. The sharp upper bound over ambient dimensions is
\[
 \sum_{i=1}^k[f(a_i)-\lambda a_i]\ \le\
 \max_{0\le j\le k}\{M_j-(k-j)\lambda/2\}.
\]
It is not valid to assume that the tilted quartic is increasing on all of $[1/2,1]$. Instead note it is strictly convex there. If its minimum is not at the left endpoint, the portion above its value at $1/2$ is either empty or a right-hand interval on which it is increasing. If its minimum is at the left endpoint, use the whole interval. Apply the cap theorem on that interval to the $j$ indices whose value is strictly above the left-endpoint value. For $j=0,1$ use the direct bounds. For the others the cost is at most $-\lambda/2$. Conversely take an optimizing $j$-tuple and adjoin $k-j$ vectors of the form $e/2+\sqrt3\,z_i/2$, where the $z_i$ are orthonormal and orthogonal to the previous space. The added inner products with prior neighbors are at most $1/2$ and between new neighbors are $1/4$. This proves equality over dimensions, not just a relaxation. This extension gives linear inequalities coupling the sum of the incident quartics to the sum of the incident strengths in a continuous Gram search.

## Why the star constraints help an entire configuration

For a code of $q$ points let $F_{ij}=f(x_i\cdot x_j)$, $d_i$ the strict degree at $i$, and $C_k$ the star constants above ($C_0=0$). Since $-1/64\le f\le0$ on $[-1/2,1/2]$,
\[
 \|F\|_\infty\le\max_i\{3/4+C_{d_i}+(q-1-d_i)/64\}.
\]
Every subset of the neighbors separately obeys its corresponding $C_k$ bound. Thus the theorem gives joint constraints on incident quartics, rather than estimating each edge as large as $3/4$.

There is also a direct correction to uniform probability weights. Let $b=F\mathbf1$, $u=q^{-1}\sum_i b_i$, and $L\ge\|F\|_\infty$. If $u\ge0$ and $0\le\gamma\le 1/L$, then $p_i=[1-\gamma(b_i-u)]/q$ is a probability vector. Expanding its quadratic form and using the symmetric operator norm bound $\|F\|_2\le L$ gives
\[
 q h(X)\le u-\frac{\gamma}{q}\sum_i(b_i-u)^2 .
\]
Thus dispersion of the per-point energies strictly improves the uniform test whenever $\gamma>0$. For instance, on a 27-point code with $h>3/(4\cdot13)$, a strong neighborhood cannot have 13 vertices: it is independent and its uniform measure would have energy at most $3/(4\cdot13)$. Hence $d_i\le12$. The row norm bound becomes $3/4+182/96+14/64<2.865$; $\gamma=0.346$ is valid. This does not require the 27 points to have any transitivity. The method is not itself a proof of a general kissing bound.

## Two certified six-dimensional component charges

Here is a concrete use of the nonuniform probability bound. Let $h$ denote minimal probability $f$-energy on a six-dimensional $60^\circ$ code of order $q$ and $u=q^{-1}\sum_i b_i$ the uniform per-point energy. Then
\[
 \begin{array}{c|c|c}
 q & \text{upper bound} &\text{guaranteed charge }1/h\\ \hline
 27& 27h\le 1.6321271 &\ge16.542829\\
 29& u\le 3277822550304317/2000000000000000&\ge17.694673 .
 \end{array}
\]
These are bounds for every such 27- or 29-set, not claims of sharpness. The 29-point row uses uniform probability; the 27-point row permits nonuniform weights. The verification has two ingredients.

First, the [standalone three-point verifier](verify-kissing-six-star-bv.js) proves
\[
 u-\frac{0.17}{27}\sum_{i=1}^{27}(b_i-1.631)^2
 \le \frac{1632126774274021}{10^{15}}.
\]
It also proves the displayed 29-point uniform row. In detail the positive semidefinite three-point kernel $H$ and nonnegative-harmonic polynomial $h_0$ use the [Bachoc–Vallentin construction](https://doi.org/10.1090/S0894-0347-07-00589-9) and the [normalization of the earlier source charts](https://github.com/mxym/math/blob/ebcb0c093d947093f246956f60d2e39a8f6697bd/research/euclidean-tensor-geometry/KissingUniversalSixtyNineParts.md). Set $J(t)=H(1,t,t)$. For the uncorrected row the inequality on a distinct ordered triple with pair inner products $a,b,c$ is
\[
 3(q-2)H(a,b,c)+\sum_{t=a,b,c}[f(t)+h_0(t)+3J(t)]
 \le3(B+\varepsilon),\qquad\varepsilon=1/200000 .
\]
For the corrected row **subtract** from the left side
\[
 \gamma\left\{\sum_{t=a,b,c}\big(2r f(t)+f(t)^2\big)
 +(q-2)\big[f(a)f(b)+f(b)f(c)+f(c)f(a)\big]\right\},
 \quad\gamma=17/100,\quad r=3/4-1.631.
\]
Averaging over distinct ordered triples and adding coinciding indices proves the required corrected statistic bound: expanding $(b_i-1.631)^2=(r+\sum_{j\ne i}f_{ij})^2$ gives exactly these three correction terms, plus the diagonal constant $r^2$. The resulting rational bound is $3/4+h_0(1)+H(1,1,1)+(q-1)(B+\varepsilon)-\gamma r^2$ (omit the last term in the uncorrected row). No fixed trial Gram matrix is used. Integer positive factors reconstruct the kernels, and outward-rounded tensor Bernstein coefficients check every sorted triple in $[-1,1/2]^3$ with nonnegative Gram determinant. The two rows visit 1,425 and 1,787 cells respectively.

Second, if $27h\le1.6321271$ there is nothing to prove. Otherwise $h>3/(4\cdot13)$, so the star argument permits $\gamma=.17$, and $u\ge27h>1.631$. The [previous uniform certificate](https://github.com/mxym/math/blob/c66c69d6b1c4c940eaa459936bbb12cc79198f87/research/euclidean-tensor-geometry/KissingSixSeventyFiveExtension.md) gives $u\le652948043974739/400000000000000$. Passing from a variance about $1.631$ to a variance about $u$ adds precisely $\gamma(u-1.631)^2$ to the corrected bound. Even at this upper endpoint its addition leaves the value strictly below $1.6321271$, a contradiction. The reciprocal charges have been rounded down.

For example, in the remaining [75-point obstruction](https://github.com/mxym/math/blob/c66c69d6b1c4c940eaa459936bbb12cc79198f87/research/euclidean-tensor-geometry/KissingSixTwoHeptadsAndSeventyFive.md) of sizes $(1,9,11,27,27)$ these new charges, together with $1.333333+7.329707$ for the singleton and eleven, force the nine-component itself to have
\[
 h_9\ge1/(48-1.333333-7.329707-2\cdot16.542829)>.1599666 .
\]
In the other list $(1,7,11,27,29)$ they similarly force $h_7>.1960992$. These are necessary conditions; neither is a contradiction by itself.

**Replay.** Run `python3 verify_kissing_quartic_star.py` for the symbolic identities and `node verify-kissing-six-star-bv.js` for both continuous three-point certificates, the rational bootstrap and the charge rounding. Both programs use only standard libraries.
