# Log-log error bounds for the largest sample-vertex empty simplex

In a fixed full-dimensional compact convex body $K\subset\mathbb R^d$ ($d\ge2$), sample an infinite sequence of independent uniform points. Let $T_n$ be the maximum **volume fraction** of a simplex with vertices among the first $n$ points and no other point of those $n$ in its interior. The first-order growth $nT_n/\log n\to d$ almost surely is [prior](../largest-empty-sample-simplex-volume/PROOF.md). Here, almost surely,
$$
 -(3d^2+d)\ \le\ \liminf_n \frac{nT_n-d\log n}{\log\log n}
 \ \le\ \limsup_n \frac{nT_n-d\log n}{\log\log n}\ \le\ 2 .
$$
At fixed $n$ sufficiently large, $\Pr(nT_n>d\log n+x)\le C_d e^{-x}$ for $x\ge0$. Neither second-order endpoint is claimed sharp. Normalize $|K|=1$ throughout.

**Upper bounds.** The volume of $d+1$ iid uniform points' simplex has a density bounded by a dimension-only constant, by the case $m=1$ of the [anchor-chart density proof](EXTREME-COUNTS.md). (General position makes the separate convex-position constraint trivial.) Put $t=d+1$. At fixed $n$, summing over the $\binom nt$ subsets and integrating avoidance from $v$ to one bounds $\Pr(T_n\ge v)$ by $C_d n^d(1-v)^{n-d}$. Since $(1-v)^{n-d}\le e^d e^{-nv}$ for $0\le v\le1$, this proves the stated tail, also trivially true above volume one.

Let $m,N$ be consecutive terms of $n_j=\lfloor e^{\sqrt j}\rfloor$ at large $j$. Write $L=\log N$, so $N/m=1+O(1/L)$. If any $T_n$ on $m\le n\le N$ exceeds $v$, a tuple of the first $N$ points with this volume must avoid all first $m$ non-tuple points. Conditional on that fixed tuple there are at least $m-t$ independent such points. Summing over all candidates and integrating gives block failure probability at most $C_d N^t(1-v)^{m-d}/(m-d)$. At $v=(d\log N+B\log\log N)/N$, this is $O_{d,B}(L^{-B})$ for fixed $B>2$: the cost $(N-m+d)v$ is bounded. This is summable in $j$ because $L\asymp\sqrt j$. The function $(d\log n+B\log\log n)/n$ is eventually decreasing, so a good block gives the upper threshold for every intermediate $n$. Apply Borel–Cantelli and then use countably many $B\downarrow2$.

**Candidate geometry and occupancy.** Use the thin simplices of the [first-order construction](../largest-empty-sample-simplex-volume/PROOF.md), now with parameters
$$
 A=3d^2+d,\qquad B=2d+2,\qquad
 a=(dL-A\log L)/N,\qquad \rho=L^{-1}.
$$
Explicitly, take a small fixed $(d-1)$-simplex in an interior ball, join it to an apex at perpendicular height $w$ proportional to $a$ so the simplex volume is $a$. Rotate its normal in a fixed small cap on a maximal $wL^B$-separated net and translate along each normal at spacing $2w$ over a fixed small interval, retaining the interior ball's containment as in that construction. By cap covering and the two-slab intersection bound $C_K w^2/\sin\alpha$ for different normals of angle $\alpha$ (parallel translates are disjoint), the number and pair intersection volumes satisfy
$$
 M\ge c_K N^d L^{-d-B(d-1)},\qquad I=|R\cap S|\le C_K/(NL^{B-1}) \quad (R\ne S).
$$
At each of the $t=d+1$ vertices mark its homothetic corner of scale $\rho$ and volume $b=a\rho^d$. The corners are disjoint. Selecting one point per corner gives a simplex of volume at least $a(1-C_d\rho)$: each barycentric column differs from its identity column by at most $2\rho$ in one-norm, so the determinant differs from one by at most $(1+2\rho)^t-1$ by multilinearity.

Call a candidate good when exactly one of the first $N$ points lies in each corner, those $t$ points all have labels at most $m$, and no other point of the first $N$ lies anywhere in the candidate. The selected simplex then survives empty throughout the block. With $(m)_t=m(m-1)\cdots(m-t+1)$ the common probability is $p=(m)_t b^t(1-a)^{N-t}$. Since $Na^2=o(1)$, $mb\asymp L^{1-d}$ and $Na=dL-A\log L$, one has
$$
 Mp\ \ge\ c_K L^{A-d-B(d-1)+1-d^2}=c_K L^3 .
$$

**Matched corners.** For a pair $R,S$, shared corner labels give a partial matching between the two lists (disjoint corners within each list). For a matching of size $\ell$ assign $2t-\ell$ distinct labels from the first $m$; each unmatched label has available volume at most $b$, and each matched one at most $I$. All remaining labels must avoid the union. Thus joint probability is at most
$$
 \sum_{\ell=0}^{t}{t\choose\ell}^2\ell!(m)_{2t-\ell}
             b^{2t-2\ell}I^\ell (1-2a+I)^{N-2t+\ell}.
$$
For each term the falling-factorial ratio to $(m)_t^2$ is at most $m^{-\ell}(1+O_d(1/m))$. Its survival ratio to $(1-a)^{2N-2t}$ is at most $1+O_d(a+NI)$ uniformly: $(1-2a+I)/(1-a)^2\le1+I/(1-a)^2$, and the finitely many remaining fixed powers cost $1+O_d(a)$. Thus, dividing by $p^2$, the $\ell=0$ term contributes at most $1+O_d(a+NI+1/m)$ and the remaining terms contribute at most $O_d(I/(mb^2))$ in total for large $N$. Here $I/(mb^2)=O_K(L^{-3})$ and $NI=O_K(L^{1-B})$. If $Z$ counts good candidates, the variance bound now gives $\Pr(Z=0)\le (Mp)^{-1}+O_K(L^{-3})=O_K(L^{-3})$, summable over the blocks.

Almost surely each sufficiently late block therefore gives $T_n\ge a(1-C_d/L)$ for every intermediate $n$. Since $n/N=1+O(1/L)$, replacing $Na$ by $n a(1-C_d/L)$ loses at most $O_d(1)$; replacing $L$ by $\log n$ and $\log L$ by $\log\log n$ similarly costs $O_d(1)$ in the target. This proves the lower bound. No step presumes monotonicity of $T_n$. ∎
