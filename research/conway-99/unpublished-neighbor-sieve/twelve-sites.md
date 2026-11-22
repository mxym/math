# Two exclusions for twelve sites in the triangle neighborhood

Use a triangle with the [three-wing labeling and component balance](triangle-complement.md). Let $C$ be a union of whole wing components of total size twelve. It has four sites per wing and every exterior vertex sees exactly two of its sites. In the induced cubic graph on $C$ write $N(i)$ for the neighbors of $i$. The number of exterior vertices with pair label $e=\{i,j\}$ in $C$ is
$$m_e=2-1_{j\in N(i)}-|N(i)\cap N(j)|-1_{i,j\text{ in the same wing}}.$$
All common neighbors within the 39-site shell have been counted because $C$ is closed under wing adjacency. A label of multiplicity two identifies two vertices that have reached their entire common-neighbor allowance. They cannot be adjacent, and no third vertex can see both.

If $y$ has label $e$, its eight exterior neighbors must contain each $i\in C$ exactly $d_i(e)=2-1_{i\in e}-|N(i)\cap e|$ times among their labels. Denote by $L_{ef}=L_{fe}$ the number of exterior edges between the two label classes, restricting to classes of positive size. Their entries satisfy
$$L_{ee}=0,\quad 0\le L_{ef}\le\min(m_e,m_f),\qquad \sum_{f\ni i} L_{ef}=m_e d_i(e).$$
A pair of classes is forbidden if $d_i(e)=0$ for some $i\in f$ or conversely. The upper bound follows from the multiplicity-two observation.

For connected $C$, label the four sites per wing successively using the first two cross matchings. The last matching is then a permutation $\pi$ on four letters. The mate matchings are $P,Q,R$ and relabeling fixes $P=(01)(23)$. Among the 216 initial choices, discard disconnected graphs and negative multiplicities. Direct simultaneous relabeling gives 35 types with named wings or 15 allowing wing permutations. The following two types fail the displayed equations.

| $P$ | $Q$ | $R$ | $\pi$ | Required weighted sum | Upper bound |
| --- | --- | --- | --- | ---: | ---: |
| $(01)(23)$ | $(01)(23)$ | $(01)(23)$ | $(12)$ | 4 | 0 |
| $(01)(23)$ | $(01)(23)$ | $(02)(13)$ | identity | 2 | 0 |

The [integer certificate checker](twelve_sites.py) stores the nonzero weights $v_{e,i}$ for the two linear combinations. For any allowed edge of classes $e,f$ its coefficient is $\sum_{i\in f}v_{e,i}+\sum_{j\in e}v_{f,j}$. The checker multiplies the positive part of each coefficient by its upper bound and sums. In both cases the prescribed right side exceeds this bound. These two exclusions account for six of the 35 named-wing types.

If $C$ has two components of size six, both are prisms. This gives one more template with 12 pair labels of multiplicity one and 24 of multiplicity two. Thus a triangle with such a twelve-site union has at most fourteen remaining templates for that union. A triangle without such a union has component sizes, divided by six, forming $(6)$, $(5,1)$ or $(3,3)$. It therefore has at most two components and residual dimension at most nine in the [exterior reconstruction](triangle-complement.md). These alternatives leave the global existence question open.
