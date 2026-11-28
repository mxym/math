# A bipartite-stress obstruction and global rank reduction for four through twenty points

For $4\le n\le20$ and arbitrary unit vectors with $x_i\cdot x_j\le1/2$ for $i\ne j$, let
$
 C(X)=\min_{w_i\ge0,\ \sum w_i=1}\sum_{i,j}w_i w_j
       \big((x_i\cdot x_j)^4-(x_i\cdot x_j)^2/4\big).
$
**Theorem.** For each such $n$, the maximum of $C(X)$ over every Euclidean dimension is already attained in $\mathbb R^{n-2}$. In particular the five-, seven- and nine-point global capacity questions can be studied in dimensions three, five and seven respectively. This gives a uniform cardinality extension and a shorter combinatorial explanation of the earlier [five-point reduction](https://github.com/mxym/math/blob/b951d2ba0c68c002beb43f9e24a55edeb3f23097/research/euclidean-tensor-geometry/KissingFivePointRankThreeReduction.md). It does not determine the maxima in these reduced dimensions.

### Convexity on the mass simplex

Write $G_{ij}=x_i\cdot x_j$ and $F_{ij}=f(G_{ij})$, $f(t)=t^4-t^2/4$. The compact domain of Gram matrices is $G\succeq0,\ G_{ii}=1,\ G_{ij}\le1/2$ for $i\ne j$; each can be realized in dimension $d\le n$. We only need $b^\mathsf TFb\ge0$ for real vectors $b$ with $\sum b_i=0$, not positivity of the whole matrix. For $T=\sum b_i x_i^{\otimes4}$, the double trace is zero, so $S=\operatorname{Tr}T$ is a traceless symmetric two-tensor. The trace operator on symmetric four-tensors obeys
$
 \operatorname{Tr}\operatorname{Tr}^*S=((d+4)S+(\operatorname{tr}S)I)/6.
$
Indeed its adjoint averages $S\otimes I$ over the six symmetric placements. Consequently $\|\operatorname{Tr}T\|^2\le (d+4)\|T\|^2/6$ on the double-traceless subspace: apply Cauchy–Schwarz to $\langle T,\operatorname{Tr}^* S\rangle=\|S\|^2$ and use $\|\operatorname{Tr}^* S\|^2=(d+4)\|S\|^2/6$. As $d\le20$,
$
 b^\mathsf TFb=\|T\|^2-\|\operatorname{Tr}T\|^2/4\ge0 .
$
This explains the stated range, without assuming the result fails for larger $n$.

### A rank-one stress forces a bipartite strong-edge graph

For $\tau>0$ add $\tau\sum_iw_i\log w_i$ to the minimized objective, obtaining $C_\tau$. Conditional positivity is sufficient for strict convexity on the simplex after adding the entropy; its minimizer $w$ is unique and every $w_i>0$. Also $C-\tau\log n\le C_\tau\le C$. At a maximizing $G$ of $C_\tau$, differentiating along feasible Gram segments gives a linear objective with entries $K_{ij}=w_iw_j f'(G_{ij})$ maximized there. Justification does not require an interior Gram point: sandwich the change in minimum by the changes for the two endpoint minimizing weights and use uniqueness and compactness. The strictly feasible test $G=I$ gives semidefinite dual multipliers
$
 K=D+U-S,\qquad S\succeq0,\quad SG=0,
$
where $D$ is diagonal and the nonnegative off-diagonal entries of $U$ may occur only at contacts $G_{ij}=+1/2$.

Call pairs with $G_{ij}<-1/2$ **strong**. On them $S_{ij}/(w_iw_j)=-f'(G_{ij})>1/4$. At a pair which is neither a contact nor strong the same quantity is $\le1/4$: the maximum of $-4t^3+t/2$ on $[-1/2,1/2]$ is $1/4$, by its endpoints and two stationary points. If $S=0$ there are no strong edges. If $S=ss^\mathsf T$ has rank one, set $q_i=s_i/w_i$. In any nontrivial connected component of the strong graph the $q_i$ all have the same, nonzero sign. Choose $v$ there maximizing $|q_v|$. Every other $i$ has a strong neighbor $j$, so
$
 q_iq_v\ge q_iq_j>1/4.
$
Thus every such $i$ is either a strong neighbor of $v$ or meets $v$ in a $+1/2$ contact. The strong neighbors form an independent set in the strong graph, because three pairwise strong vectors would have a sum of negative squared norm. The contact neighbors also form an independent set: two vectors making an angle of $60^\circ$ with $x_v$ have mutual angle at most $120^\circ$. Put $v$ with the contact neighbors and the strong neighbors on the other side. This gives the claimed bipartition of every component, including isolates.

### An attainable baseline and the limit

Set $m=\lceil n/2\rceil$. A bipartite graph on $n$ vertices has an independent set of size at least $m$; the mixed cost $f$ on every distinct pair of that set is nonpositive. Equal mass there shows $C\le3/(4m)$. Conversely take $\lfloor n/2\rfloor$ orthonormal axes with both signs and, for odd $n$, one additional orthogonal singleton. All cross-axis costs are zero; each axis contributes $3/4$ times its pooled mass squared. Equal pooled mass attains the optimum $3/(4m)$, in dimension $m\le n-2$.

If the unrestricted maximum is this baseline the assertion is immediate. If it is larger, then for all sufficiently small positive $\tau$ the maximum of $C_\tau$ is also above the baseline, so the strong graph of each such maximizer is not bipartite. Its stress therefore has rank at least two and $SG=0$ forces $\operatorname{rank}G\le n-2$. Compactness, closure of the rank constraint and uniform convergence of $C_\tau$ give a maximizer of the original $C$ in that rank. In the low cardinalities $n=4,6$, the baseline itself is exact: at four the triangle-free graph is bipartite, and at six the elementary $R(3,3)=6$ forces an independent triple.

The proof is analytic. The small checker `verify-kissing-bipartite-stress.py` verifies the scalar threshold, tensor constants, baseline examples, finite $n=4,6$ graph statements and the bipartition implication on small graphs.
