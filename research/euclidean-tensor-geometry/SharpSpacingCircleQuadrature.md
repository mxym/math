# Sharp spacing for positive quadrature on prescribed circular points and axes

Take any $2m+1$ points on a circle. If each consecutive angular gap is at least $\pi/(m+1)$, their positions can be assigned nonnegative weights that integrate every trigonometric polynomial of degree at most $m$ exactly. The **same guarantee holds for their unoriented axes**: a second choice of weights integrates all even frequencies $2,4,\ldots,2m$. Both spacing thresholds are sharp for **every** $m\ge1$. The points need not form an orbit or have any symmetry.

For five planar kissing points this gives the exact best weighted energy **$1/4$ for every configuration**, not just for the regular pentagon. The [dimension-free five-point bound](KissingOddComponentBarriers.md) is $0.253$; the present exact calculation on the circle does not close the gap in higher dimensions.

## Statement, including zero weights

Write $L=\pi/(m+1)$, $N=2m+1$, and let $X=\{e^{i\theta_j}\}_{j=1}^N$ have all circular gaps at least $L$. Fix **either** $h=1$ or $h=2$ and put $Y=\{e^{ih\theta}:e^{i\theta}\in X\}$; repeated projected nodes are pooled. There is a **unique vector of masses on the distinct nodes of $Y$** such that
$$
 w_y\ge0,\qquad\sum_{y\in Y}w_y=1,\qquad \sum_{y\in Y}w_y y^k=0\quad(1\le k\le m).
$$
These are the moments of the uniform probability measure. Mass on coinciding projections may be divided arbitrarily among their original points. The weights for $h=1$ and $h=2$ generally **differ**.

* If all gaps are strictly greater than $L$, the $N$ projected nodes are distinct and all weights are positive. If all gaps are at least $L+\epsilon$, $\epsilon>0$, every weight is at least $\sin(\epsilon/4)^{2m}$.
* At the closed threshold, if $Y$ contains a rotated regular $(m+1)$-gon, its vertices have weight $1/(m+1)$ and all other nodes have weight zero. Otherwise all the weights are positive.
* For each $h$ and every lower separation threshold $L'<L$, some $N$ points of separation greater than $L'$ admit **no** such nonnegative weights. For $h=2$ the counterexample may also be chosen without coinciding axes.

[Peherstorfer](https://arxiv.org/abs/1001.2451) gives a general orthogonal-polynomial characterization of positive trigonometric quadrature. [Austin–Trefethen](https://arxiv.org/abs/1612.04018) and [Yu–Townsend](https://arxiv.org/abs/2202.04722) study perturbations of individually prescribed equispaced nodes; the latter shows that an arbitrarily small fixed relative perturbation allowance does not ensure positivity uniformly in the degree. Our hypotheses concern a **minimum gap on the original circle**, including before the twofold projection when $h=2$. The point here is the sharp separation guarantee, its boundary support and its packing consequence, not a new characterization of all positive quadratures.

## 1. A sign test using a moving grid

For $N$ distinct projected angles $\phi_j$ (modulo $2\pi$), the cardinal interpolant at node $i$ is
$$
 Q_i(\phi)=\prod_{j\ne i}\frac{\sin((\phi-\phi_j)/2)}{\sin((\phi_i-\phi_j)/2)} .
$$
It is a trigonometric polynomial of degree at most $m$ since it has $2m$ factors, and $Q_i(\phi_j)=\delta_{ij}$. These $N$ polynomials form the cardinal basis of the $N$-dimensional interpolation space. The required weight is the uniform mean of $Q_i$. Every rotated regular $(m+1)$-point grid gives that mean by equal weights, since its sums of frequencies $1,\ldots,m$ vanish. **The grid can be chosen separately for each $i$.**

It is therefore enough, for each target $i$, to partition the projected circle into $m+1$ equal open cells with root-free boundaries, with no other node in the target cell and **two** other nodes in every remaining cell. Starting at the target, where $Q_i=1$, crossing a simple root reverses its sign. All grid boundaries consequently have positive values of $Q_i$.

## 2. Preparing those cells in both geometries

Assume first that all gaps are greater than $L$. Fix a target, rotate it to zero and write the other arguments in positive order. With the endpoint $2\pi=\theta_N$ included for notation,
$$
 \theta_j=jL+a_j,\qquad 0=a_0<a_1<\cdots<a_N=L.
$$
In particular no two original nodes are antipodal: every difference of two arguments with different indices is a multiple of $L$ plus a nonzero quantity of magnitude less than $L$, whereas $\pi$ is a multiple of $L$.

Partition the *original* circle into $2m+2$ fine bins of length $L$ starting at $\beta=(a_r+a_{r+1})/2$. Label them cyclically by $b$, with lower endpoints $\beta+bL$. Each node of index $j\le r$ lies in bin $j-1$, each $j>r$ ($j<N$) in bin $j$. Thus bin $r$ is vacant, bin $-1$ contains the target, and each other bin contains one point. Temporarily remove the target.

- **Ordinary angles, $h=1$.** Take $r=0$, giving adjacent empty bins $-1$ and $0$. Merge these and pair all the other consecutive bins in the same alignment. The resulting equal cells have the required occupancies.
- **Axes, $h=2$.** Take $r=m$, giving opposite empty bins $-1$ and $m$. Under angle doubling, two opposite bins map to the same open cell of length $2L$. Exactly the target cell is empty and every other cell contains two distinct nodes.

This proves positivity in both cases. If the excess in each gap is at least $\epsilon$, every $a_j$ is at least $\epsilon/2$ from $\beta$ modulo $L$: the midpoint of the chosen circular gap between consecutive residues has that distance to the closest residue. Every numerator in $Q_i$ at a coarse-grid boundary has absolute value at least $\sin(\epsilon/4)$ (doubling the angles only improves the angular separation from the projected boundaries). The denominator factors have absolute value at most one. Averaging proves the stated quantitative lower bound.

## 3. Closed spacing, uniqueness, and sharpness

Mix the circular gaps of a closed-threshold configuration with the equal gap $2\pi/N>L$, in proportions tending to zero for the equal-gap part. The positive probability vectors of the strict configurations have convergent subsequences, giving nonnegative weights by continuity. After pooling equal nodes, uniqueness follows from a Vandermonde matrix: the moment rows of orders $-m,\ldots,m$ comprise $2m+1$ consecutive powers, so its columns on any at most $2m+1$ distinct nonzero complex nodes are linearly independent.

Suppose the projected nodes are distinct and the limiting weight of a node $i$ is zero. The cardinal functions for $i$ converge uniformly, as none of its denominators tends to zero. Take a subsequence for which the phase of the associated regular grids also converges. The limiting $Q_i$ is nonnegative at all limiting grid points and has mean zero. Every grid point is therefore a zero, hence among the other nodes. Conversely any included regular $(m+1)$-gon gives the required moments with its uniform measure, so uniqueness gives exactly the asserted masses.

The only remaining case is an antipodal pair in the original circle when $h=2$. The pair divides the circle into two semicircles, with at most $m+1$ gaps on either side, and $2m+1$ gaps in total. The side with $m+1$ gaps must have every gap exactly $L$. It supplies the complete regular $(m+1)$-gon after angle doubling.

**Sharpness for ordinary nodes.** Start with a regular $(2m+2)$-gon minus one vertex. Of the two alternating regular $(m+1)$-gons one is intact. Its vertices alone carry the unique quadrature. Choose a remaining node $i$ outside that intact polygon and a node $j$ on it. The original cardinal polynomial $Q_i$ has a simple zero at $\phi_j$. Move $j$ through a signed angle $t$ and leave the other nodes unchanged. The unique interpolatory weights depend continuously on $t$, so $w_j(t)>0$ for small $t$. Exactness for the *old* $Q_i$ gives
$$
 0=w_i(t)+w_j(t)Q_i(\phi_j+t).
$$
One choice of sign of arbitrarily small $t$ makes $w_i(t)<0$. The separation can remain greater than any prescribed $L'<L$.

**Sharpness for axes.** Exactly $m+1$ distinct unit complex nodes with the required moments must be a regular $(m+1)$-gon. Indeed the square matrix with columns $\sqrt{w_y}(1,y,\ldots,y^m)^t$ has orthonormal rows. Its columns are then orthonormal: all $w_y=1/(m+1)$ and each quotient of two different nodes is a nontrivial $(m+1)$st root of unity. Now perturb a regular $(m+1)$-gon slightly so that it is not regular. On the original circle take both square roots of $m$ nodes and one square root of the last, giving $2m+1$ nodes with spacing arbitrarily close to $L$ but no allowable weights. Nonexistence persists on a neighborhood: existence is closed by compactness of the mass simplex and continuity of the moments. Thus, if desired, an additional small perturbation separates every projected node.

## 4. Exact planar kissing energy

For five planar unit vectors separated by at least $60^\circ$, put $f(t)=t^4-t^2/4$. At angular difference $u$,
$$
 f(\cos u)=\tfrac14+\tfrac38\cos(2u)+\tfrac18\cos(4u).
$$
The energy of any probability weights is consequently $1/4+3|\sum w_j e^{2i\theta_j}|^2/8+|\sum w_j e^{4i\theta_j}|^2/8$. The axis rule for $m=2$ attains the constant $1/4$. The preceding support description characterizes all minimizers, up to splitting masses on equal axes.

More generally, the same recipe reaches the constant Fourier coefficient for every circle interaction with nonnegative cosine coefficients on the prescribed frequencies. Giving each end of a weighted axis half its mass also produces a weighted spherical $(2m+1)$-design on the circle: all odd harmonics cancel in opposite pairs.

**Replay:** `python3 verify-sharp-circle-quadrature.py` uses exact integer bin occupancies and cardinal signs for strict and boundary profiles, and exact rational Fourier weights for explicit nonsymmetric-spacing test configurations. It is a check of the constructions, not an enumeration used in place of the proof.
