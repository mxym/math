# A common determinant-49 target for all four remaining Conway ranks

**Equivalence.** A Conway 99-graph exists if and only if some even positive definite lattice of rank 44 and determinant 49 contains 99 vectors in one coset modulo three times the lattice, each of squared norm 28, with mutual inner products in $\{-8,1\}$. On the forward implication the lattice can be chosen indecomposable, with elementary 7-primary discriminant and at most 28 mutually orthogonal pairs of roots, with no other roots. Here a root means a vector of squared norm two.

## Passing to the same determinant

For a hypothetical graph let $r$ be its Seidel rank over $\mathbb F_7$ and $q=44-r$. The [rank exclusion](../rank-34-exclusion/README.md) leaves $q=2,4,6,8$. The graph gives an even lattice $L$ with discriminant group $(\mathbb Z/7)^q$, and vectors $u_i$ with Gram matrix $3I-A+J/9$. We have $3u_i\in L$, $u_i-u_j\in L$ and $\sum_i u_i u_i^t=7I$. [Graph lattice](https://github.com/YesterdaysLemon/conway-99-research/tree/main/attempts/wave66-spherical-code-shift) · [Level-seven extension](https://github.com/YesterdaysLemon/conway-99-research/tree/main/attempts/wave71-modular-theta-extension)

The normalized Gauss sum of the discriminant form is $e^{2\pi i44/8}=-1$ by Milgram's formula. In even dimension over $\mathbb F_7$ a hyperbolic plane has normalized Gauss sum one and an anisotropic plane has normalized sum minus one. The Witt decomposition thus has an anisotropic plane and $(q-2)/2$ hyperbolic planes. Take a maximal totally isotropic subspace $H$. Its preimage $U$ in $L^*$ is an even overlattice with discriminant $H^\perp/H$ of order 49. The possible indices $[U:L]$ are $1,7,49,343$. The marks $v_i=3u_i$ in $U$ have the required norms and mutual inner products, and $v_i-v_j\in3U$.

## Roots of the enlarged lattice

A root $a$ of $U$ is in $L^*$ because $L\subset U$ and $U$ is integral. Its evaluations $t_i=\langle a,u_i\rangle$ form a signed norm-14 eigenvector by the short-vector dictionary. For roots $a,b$, tightness gives $t(a)\cdot t(b)=7\langle a,b\rangle$. If $a\ne\pm b$, at most two positive sites of $t(a)$ can be positive sites of $t(b)$, since three determine the entire signed Fano configuration. The same applies to each of the other three sign choices. There are at most four matching and at most four conflicting nonzero signs. The resulting absolute dot product is at most four. Integrality in $U$ now forces $a\perp b$. [Fano triple closure](../short-support-packing/README.md)

Choose one root per antipodal pair. Let $m_i$ be the number of chosen roots which evaluate nontrivially at $i$. Subtract the projection onto their span:
$$a_i=u_i-\tfrac12\sum_{a}t_i(a)a,\qquad \|a_i\|^2=28/9-m_i/2.$$
Each $b_j=\langle a_i,u_j\rangle$ belongs to $1/9+\tfrac12\mathbb Z$, and $\sum b_j=0$. Consequently $(b_j-1/9)(b_j+7/18)\ge0$ at every site. Summing yields $\sum b_j^2\ge99\cdot7/162=77/18$. Tightness gives $\sum b_j^2=7\|a_i\|^2$, so $m_i\le5$. Equality would put every $b_j$ in $\{1/9,-7/18\}$, although $b_i=\|a_i\|^2=11/18$. Hence $m_i\le4$. Each chosen root uses fourteen sites, giving at most $\lfloor99\cdot4/14\rfloor=28$ antipodal pairs.

In the original rank-42 case $U=L$. Moreover every vector of squared norm $14j$ in $\sqrt7 U^*$ is $\sqrt7$ times a vector of $U$ of squared norm $2j$: its discriminant class is isotropic in an anisotropic plane and must vanish. In particular the graph then has $N_{14}\le56$.

## The marked lattice is indecomposable

Suppose $U$ is an orthogonal direct sum of two nonzero even integral lattices. For any nonadjacent sites $i,j$, $u_i-u_j$ is a lattice vector of squared norm six. If both direct-summand components are nonzero, their squared norms are two and four. The component of norm two is a root $a$ with $|t_i(a)-t_j(a)|=2$. Thus $i,j$ occur with opposite signs in one of the Fano supports counted above.

At $i$ at most four root pairs occur, and each has only three nonadjacent sites of the opposite sign: the other four opposite sites are its four Fano neighbors. Of the 84 nonneighbors at least 72 therefore give differences supported in a single summand. For two such neighbors $j,k$ the summand must be the same. Otherwise $u_j-u_k$ would have squared norm twelve by orthogonality, whereas the graph marks give only six or eight. The graph of these single-summand pairs has minimum degree at least 72 on 99 sites and is connected. Its edges at every site use the same summand, so all differences lie in one summand. They span the whole real space by centering and tightness, a contradiction.

## Recovering the graph from its 99 vectors

Let $G$ be the Gram matrix of any $n$ vectors of norm 28 in dimension 44 with the indicated two mutual inner products. Summing $(G_{ij}-1)(G_{ij}+8)$ gives
$$972n=\operatorname{tr}(G^2)+7\left\|\sum_i v_i\right\|^2-8n^2\ \ge\ (28^2/44-8)n^2.$$
Thus $n\le99$. At equality the vectors sum to zero and $G$ has 44 positive eigenvalues all equal to $28\cdot99/44=63$. Put an edge precisely at inner product minus eight, so $G=27I-9A+J$. The zero row sums give degree fourteen. Substituting $G^2=63G$ gives $A^2=12I-A+2J$, exactly the two required common-neighbor counts. Neither center nor tightness needs to be imposed in a construction.

## Arithmetic checks at the remaining ranks

The following formal theta pairs obey the level-seven Fricke relation, the marked lower bounds $y_2\ge462$, $y_3\ge41058$, $y_4\ge3156588$, and $x_7=x_8=x_9=y_1=0$. Their nonconstant coefficients are even, integral and nonnegative through exponent 50. In the rank-42 row they also satisfy $x_{7j}=y_j$ throughout this cutoff. Entries are in the original graph-generated lattice normalization.

| Rank | $(x_{10},x_{11},x_{12},x_{13},x_{14})$ | $y_2$ | $y_3$ | $y_4$ |
|---:|---|---:|---:|---:|
| 36 | $61920,0,2,1223700,5255634$ | 462 | 62,924 | 11,931,234 |
| 38 | $8632,2,0,173604,738030$ | 462 | 248,600 | 90,044,416 |
| 40 | $0,0,8162,24612,92658$ | 462 | 1,498,364 | 638,235,906 |
| 42 | $0,0,0,2632,1000$ | 1,000 | 10,648,712 | 4,464,109,880 |

Run `python3 verify.py` for an exact rational reconstruction of both cusp expansions in each row. These coefficient checks leave the existence of the lattice with the required 99 marks open.
