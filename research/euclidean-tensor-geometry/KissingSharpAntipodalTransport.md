# Sharp antipodal transport for odd spherical codes

Let $X$ be any $N$ distinct unit vectors with all distinct-point inner products at most $s$, where $0\le s<1$. Write $\mu_X$ for their uniform measure. How close can it be to its own reflection? Use the ordinary **squared chordal** transportation cost, and remove the normalization:
$$
 \mathcal A(X)=N W_2^2(\mu_X,\mu_{-X})
       =\min_{\pi\in S_N}\sum_{i=1}^N\|x_i+x_{\pi(i)}\|^2 .
$$
The last identity is the [uniform discrete assignment theorem](https://arxiv.org/abs/1803.00567). The permutation is **not** required to be an involution. In particular this is not [disjoint matching with an uncharged singleton](KissingUnrestrictedRmsAntipodalAsymmetry.md).

**Example (kissing angle).** At $s=1/2$, for every odd $N\ge5$,
$$
             \mathcal A(X)\ge (15-5\sqrt5)/2=1.909830\ldots .
$$
This is sharp over all ambient dimensions. Equality holds exactly for a regular great-circle pentagon together with antipodal pairs, provided their union obeys the original angle bound. Orthogonal extra axes always realize such examples in a sufficiently large dimension. For hypothetical odd kissing codes above 72 or 126 points in six or seven dimensions, respectively, the bounds are **strictly larger** (§5). No improvement of either general kissing number is claimed.

## 1. All separations: only two cycle lengths matter

The following is the exact minimum over all dimensions, with equality cases described below. Even $N$ gives zero, exactly for antipodal codes. For $N=1$ the answer is $4$; for $N=3$ it is $3$. For odd $N\ge5$ put $r_k=\cos(2\pi/k)$ and $A_k=2k(1-\cos(\pi/k))$.

* For $0\le s<r_5$, the answer is $\min(3,5-10s)$. Thus triangles win below $1/5$, with a tie at $1/5$.
* For $r_5\le s<1$, choose the **largest odd** $m\le N$ with $r_m\le s$. If $m=N$, the answer is $A_m$. Otherwise put $k=m+2$, $c_k=\cos(\pi/k)$, $d_k=\cos(3\pi/k)$. The answer is
$$
             \min\{ A_m,\ L_k(s)\},\qquad
             L_k(s)=2k\left(1-\frac{(1+s)/2+c_kd_k}{c_k+d_k}\right).
$$

A minimizing permutation has just one odd cycle; everything else consists of exact antipodal pairs. Each winning choice can be used, including either choice at a tie. For $A_m$ the cycle is a centered regular $m$-gon taken in star order; for the first branch the winning $3$ is an equilateral triangle, and the winning $5-10s$ is the two-distance pentagon with cycle-neighbor product $-1/2-s$ and second-neighbor product $s$. The winning $L_k$ has the following two-frequency form, up to orthogonal embedding and cyclic labeling:
$$
 \left(\sqrt{\lambda}\cos t,\sqrt{\lambda}\sin t,
       \sqrt{1-\lambda}\cos3t,\sqrt{1-\lambda}\sin3t\right),
 \quad t=2\pi j/k,\qquad
 \lambda=\frac{s-\cos(6\pi/k)}{\cos(2\pi/k)-\cos(6\pi/k)}.
$$
The transportation permutation advances $j$ by $(k-1)/2$, not by one. A nondegenerate transition therefore really uses **four** dimensions. No orthogonality of the remaining pairs to the cycle or to each other is required for equality.

## 2. Spectral bounds for one odd cycle

Let $z_0,\dots,z_{k-1}$ follow a permutation cycle; all cyclic indices are modulo $k$. Set $b_j=k^{-1}\sum_i z_i\cdot z_{i+j}$. Discrete Fourier decomposition of each real coordinate shows $b_1=\mathbb E t$ and $b_2=\mathbb E(2t^2-1)$ for a probability measure on $t=\cos(2\pi h/k)$: its masses are the summed normalized squared Fourier coefficients. The cycle costs $2k(1+b_1)$. The bottom spectral point $-c_k$ gives $A_k$. This is strictly decreasing with odd $k\ge3$: $\sin x\cdot x>1-\cos x$ for $0<x\le\pi/3$, e.g. by integration of the increasing sine.

For odd $k\ge5$ the two smallest distinct spectral points are $-c_k,-d_k$, so $(t+c_k)(t+d_k)\ge0$. Because $b_2\le s$, this and $\mathbb E t^2\le(1+s)/2$ give $L_k(s)$. For $k=5$ this simplifies to $5-10s$. This use of the second lag is related to the fixed-cycle bounds in [Unframed matchings, §2](KissingUnframedMatchings.md); the comparison of **all lengths**, optimal assignments and equality cases here are distinct.

To compare long cycles write $q=(1-s)/2$, $D_k=(1-c_k)(1-d_k)$, $H_k=2k/(c_k+d_k)$. Then $L_k(s)=H_k(q-D_k)$. The numbers $D_k$ decrease strictly with $k\ge7$. The numbers $H_k=k/[\cos(2\pi/k)\cos(\pi/k)]$ increase strictly along odd $k\ge7$. For real $k\ge9$ the logarithmic derivative has the sign of $1-2x\tan(2x)-x\tan x$, $x=\pi/k$. Positivity already follows at $x=\pi/9$ from $x<.35,\ \tan(2x)<.85,\ \tan x<.37$, and hence everywhere below it. The one remaining comparison is $H_7<12.48<H_9$. The accompanying rational Taylor checker verifies these outward bounds without sampling $k$.

If $r_5\le s$ and $m<N$, we have $s<r_k$ at $k=m+2$, so $q>\sin^2(\pi/k)>D_k$. Consequently every longer odd cycle costs **strictly more** than $L_k(s)$, and every odd cycle of length at most $m$ costs at least $A_m$, strictly more when shorter. If $s<r_5$, the same monotonic argument begins at $k=7$, where $L_7(r_5)>3$. A singleton always costs $4$. Since every odd cycle has positive cost, an assignment with more than one odd cycle cannot attain the stated minimum; even cycles have nonnegative cost.

## 3. Attainment, feasibility and rigidity

A regular centered $m$-gon has maximum product $r_m$, and its farthest-neighbor cycle costs $A_m$. For the five-cycle in the first branch, the active range is $1/5\le s<r_5$. Its circulant Gram matrix has diagonal 1, cyclic off-diagonals $-1/2-s,s,s,-1/2-s$. It is positive semidefinite: this matrix is affine in $s$, equals the regular simplex Gram matrix at $s=-1/4$ and the planar regular star pentagon's Gram matrix at $r_5$. The nonneighbors have product $s$, and the neighbors have smaller product. Thus it attains $5-10s$.

For $k=m+2\ge7$, write $x=\pi/k$. Because $s\ge\cos(2\pi/(k-2))\ge\cos(3x)$ and $s<\cos(2x)$, the specified weight lies in $[0,1)$. In fact $\lambda\ge2/3$ and $1-s\le(2/3)(1-\cos(4x))$. To check these last two claims it suffices to use $s\ge\cos3x$ and verify $3\cos3x\ge2\cos2x+\cos6x$ and $2(1-\cos4x)\ge3(1-\cos3x)$. With $z=\cos x\ge\cos(\pi/7)>\sqrt3/2$, the differences factor respectively as
$$
 (1-z)(4z^2-3)(8z^3+8z^2+2z-1),\qquad
 (1-z)(4z+1)(4z^2-3).
$$
For geometric index difference $\pm1$ the displayed two-frequency model has product exactly $s$. For any other nonzero difference $j$, its product is at most $1-\lambda(1-\cos(2jx))\le1-\lambda(1-\cos4x)\le s$. Its transportation edges use precisely the bottom two Fourier frequencies, with second transportation lag equal to $s$. It attains $L_k(s)$.

For rigidity at $A_m$, each coordinate belongs to the bottom two-dimensional real Fourier space. In geometric order the coordinate rows have the form $u\cos t+v\sin t$; constancy of their unit squared norms forces $\|u\|=\|v\|=1$ and $u\cdot v=0$ (the nonconstant frequency $2$ is distinguishable from its negative for odd $m\ge3$). For the five-cycle equality at $5-10s$ forces no constant Fourier mode and forces every second-lag product to equal $s$. Taking products with the zero vector sum gives $p_{i-1}+p_i=-1-2s$ for its cyclic edge products; oddness forces them all equal.

For $L_k(s)$ with $k\ge7$, equality forces each coordinate into the two bottom real planes, and all second-lag products equal $s$. Reindex in geometric order, using $t=2\pi j/k$; the vector-valued trigonometric polynomial has modes $\{-3,-1,1,3\}$. Its bilinear Gram form $G(t,v)$ is symmetric and real on real arguments. In $G(t,t)$, nonconstant frequencies are $\pm2,\pm4,\pm6$; these six are distinct modulo odd $k\ge7$ (all are even and the nonzero differences have magnitude at most 12). Thus their coefficients vanish separately. Frequencies $4$ and $6$ have only the unordered mode pairs $(1,3)$ and $(3,3)$, so these Gram coefficients and their conjugates vanish. Frequency $2$ combines $(1,1)$ and $(-1,3)$; it vanishes also in $G(t-x,t+x)$, because geometric neighbors have constant product. In this second relation the self term is unchanged and the mixed term is multiplied by $\cos(4x)\ne1$, forcing both to vanish. The only surviving Gram coefficients pair opposite frequencies. The Gram is therefore $\lambda\cos(t-v)+(1-\lambda)\cos(3(t-v))$, with $\lambda$ determined by diagonal and neighbor values. This determines the configuration up to isometry. Finally, a zero-cost even cycle must step to the exact antipode at every edge; distinct points force a transposition. Adding independent antipodal axes orthogonal to a winning cycle proves sharpness for every allowed $N$.

## 4. Kissing-angle consequences

At $s=1/2$ we have $r_5<1/2<r_7$ and $L_7(1/2)>2.15>A_5$ (the verifier gives outward comparisons). Thus only the planar pentagon wins; all other odd cycles cost above $2.15$ except a second pentagon, which already costs at least $A_5$ individually. In an even-size code, a permutation with an odd cycle must contain at least two, hence costs at least $2A_5$. If it has only even cycles, replace each by the cheaper of its two alternating sets of transpositions; their mean cost is the original cycle cost. The [unrestricted pairing bounds](KissingUnrestrictedRmsAntipodalAsymmetry.md) therefore give $W_2>2H$ for the even rows there ($H=.0512,.0681$ in six dimensions and $.0306,.0420,.0500$ in seven). Indeed $4NH^2<2A_5$ in every row.

## 5. Odd excess kissing codes are separated from the sharp transport minimizers

For hypothetical odd codes of sizes $73,75$ in six dimensions and $127,129,131$ in seven, respectively,
$$
 \mathcal A(X)>1.945,\ 2.150;\qquad \mathcal A(X)>1.931,\ 2.093,\ 2.150.
$$
There is no frame or symmetry assumption. To see this, when testing any of these thresholds only a single five-cycle can remain as the odd part: any other odd cycle costs above $2.15$ and any further odd parts cost at least $A_5$ each. Reduce the remaining even cycles to transpositions as above, leaving $p=(N-5)/2$ pairs $m_i\pm a_i$ and five unit points. Put $E=\sum_i\|m_i\|^2=ph^2$. The resulting assignment costs at least $A_5+8E$.

On the five points use the measure from [Unframed matchings, §2](KissingUnframedMatchings.md), with quartic self-energy at most $C=13/50$ and $\sum w_j^2\le4C/3$. Its mean $\bar z$ satisfies $\|\bar z\|^2\le(1+\sum w_j^2)/2\le101/150$. Give this measure total mass $b$; in the homogeneous fourth-energy calculation of [RMS asymmetry, §§1–4](KissingUnrestrictedRmsAntipodalAsymmetry.md), integrate the singleton–pair inequality against it. The diagonal singleton self term $3b^2/4$ becomes $Cb^2$, and the square-completion penalty $b^2/12$ becomes at most $101b^2/1800$ by keeping the common $\bar z$. All other terms, including the lower bound and tangent estimate, are unchanged with this $p$. In the order of the five rows above the [rational checker](verify-kissing-antipodal-transport.py) uses
$$
 (h_0,b)=(.01150,2.21),(.03000,1.82),(.00665,2.21),(.01940,1.83),(.02300,1.47).
$$
It verifies strict impossibility over each entire interval $0\le h\le h_0$ by exact Bernstein coefficients. Combining $A_5+8ph_0^2$ with the other-cycle cutoff proves the tabulated bounds. The fixed-dimensional numbers are lower bounds only, unlike the sharp all-dimensional extremum above.

**Replay.** Run `python3 verify-kissing-antipodal-transport.py` (standard library). The infinite cycle comparison, all-separation feasibility, and equality descriptions are analytic; the script checks their small trigonometric constants, factors and the finite-dimensional reinforcement. The proof neither requires solving an unrestricted sphere packing nor infers the six- or seven-dimensional maximum from an asymmetry statistic.
