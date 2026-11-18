# Monotonicity for forest-supported matrices in a fixed ordering

For a Hermitian matrix $A=(a_{ij})$ indexed in the order $1,\ldots,n$, set
$$
P_A(q)=\sum_{\pi\in S_n}q^{\operatorname{inv}(\pi)}\prod_{i=1}^n a_{i,\pi(i)},\qquad
\operatorname{inv}(\pi)=\#\{(i,j):i<j,\ \pi(i)>\pi(j)\}.
$$
Use the polynomial convention $0^0=1$. The support graph has the edge $\{i,j\}$ precisely when $i\ne j$ and $a_{ij}\ne0$. A permutation of the labels can change the polynomial, so no reordering is assumed.

**Theorem.** Let $A$ be positive semidefinite with forest support. If all diagonal entries are positive and the forest has an edge, then $P_A$ is strictly increasing on $[-1,\infty)$. If $A$ is positive definite and non-diagonal, there exists $\varepsilon_A<-1$ such that $P_A$ is strictly increasing on $(\varepsilon_A,\infty)$. A zero diagonal entry forces a zero row, so $P_A$ is then identically zero; a diagonal matrix has constant $P_A$.

## 1. A nonnegative expansion over matchings

A nonzero permutation term cannot have a cycle of length at least three: that cycle would be present in the support graph. Thus the permutation swaps the ends of the edges of a matching $M$ and fixes the remaining vertices. Denote it by $\pi_M$, write $V(M)$ for the vertices it covers, and set
$$
h(M)=\prod_{\{i,j\}\in M}|a_{ij}|^2,\qquad
w(M)=h(M)\prod_{v\notin V(M)}a_{vv}.
$$
The coefficient attached to $\pi_M$ before grouping equal inversion counts is $w(M)$.

For each matching $F$ put
$$
b(F)=h(F)\det A\big[[n]\setminus V(F)\big]\ge0,
$$
where brackets select a principal submatrix and the empty determinant is one. Expand the complementary determinant. Its nonzero permutation terms consist of mutually disjoint transpositions; each extra transposition has sign $-1$. Hence
$$
b(F)=\sum_{M\supseteq F}(-1)^{|M|-|F|}w(M).
$$
For $M\subseteq T$ the interval of matchings between $M$ and $T$ is Boolean, so summing the alternating signs in this interval gives zero unless $M=T$. Consequently
$$
w(M)=\sum_{F\supseteq M}b(F),\qquad
P_A(q)=\sum_F b(F)H_F(q),\qquad
H_F(q)=\sum_{S\subseteq F}q^{\operatorname{inv}(\pi_S)}.
$$
In particular $\sum_F b(F)=\prod_i a_{ii}$. This use of determinants does not require a nonzero determinant or any division by a minor.

## 2. The crossing correction as a union size

For an edge $e=\{i,j\}$ with $i<j$, let $L_e=2(j-i)-1$, the inversion count of its transposition in the full order. Two vertex-disjoint edges **cross** when their endpoints interleave. For every $S\subseteq F$,
$$
\operatorname{inv}(\pi_S)=\sum_{e\in S}L_e-2\operatorname{cr}(S),
$$
where $\operatorname{cr}$ counts unordered crossing pairs. This is the transposition case of [Marques de Sá's disjoint-permutation formula (2018 preprint, Corollary 5.3)](https://www.mat.uc.pt/preprints/ps/p1809.pdf), [published in 2019](https://doi.org/10.1016/j.laa.2018.09.027). Here is a direct check. Only comparisons between endpoints of distinct moved edges can differ from the sum of single-edge counts. When the two intervals are separated, nested, or interleaved, their cross-edge comparisons contribute respectively $0,4,2$ joint inversions, versus $0,4,4$ counted separately. Each comparison uses two positions, so these account for all corrections. In particular $\operatorname{inv}(\pi_S)\equiv |S|\pmod2$.

Fix $F$. For every crossing pair $e,f\in F$, create two tokens shared by exactly the two sets $C_e,C_f$. Give each $C_e$ another $L_e-2d_e$ private tokens, where $d_e$ is the number of its crossing partners in $F$. For $e=\{i,j\}$ each partner uses a distinct vertex strictly between $i$ and $j$, so $d_e\le j-i-1$ and at least one private token is available. The resulting sets have no triple intersection; the cardinality of their union over $e\in S$ is exactly $\operatorname{inv}(\pi_S)$.

Activate each token independently with probability $r\in[0,1]$. Let $E_e$ be the event that all tokens of $C_e$ are active. Edge events need not be independent: the size of the union, not the sum of individual sizes, determines the intersection probability. By inclusion-exclusion and the parity above,
$$
H_F(-r)=\sum_{S\subseteq F}(-1)^{|S|}\Pr\!\left(\bigcap_{e\in S}E_e\right)
=\Pr(\text{no }E_e\text{ occurs}).
$$
Use an independent uniform random variable for each token and activate it when this variable is at most $r$. As $r$ increases the event on the right can only shrink. Therefore $H_F$ is nondecreasing on $[-1,0]$. For $F\ne\varnothing$, $H_F(-1)=0$ and $H_F(0)=1$. If the polynomial took equal values at two points in this interval, monotonicity would make it constant between them and hence identically constant. Thus the increase is strict. On $[0,\infty)$ it is also strict, since at least one positive-degree monomial occurs and all coefficients are nonnegative. For $F=\varnothing$ the polynomial is just one.

When all diagonal entries are positive and $e$ is a support edge, $w(\{e\})>0$. Because it is the sum of the nonnegative $b(F)$ over $F\ni e$, at least one strictly increasing summand has positive mass. This proves the claimed strict increase, including for singular matrices without a zero row. The two constant cases follow from $|a_{ij}|^2\le a_{ii}a_{jj}$ and the definition.

## 3. Derivative at the left endpoint

At $q=-1+s$ a token is missing with probability $s$. For nonempty $F$, to avoid all of the events $E_e$ one must miss at least one token in every $C_e$. A single missing token works precisely when it lies in the intersection of all $C_e$. The probability of at least two missing tokens is $O(s^2)$ for a fixed family. It follows that $H_F'(-1)$ is the size of this intersection: $L_e$ for a singleton, two for a crossing pair, and zero otherwise. Thus
$$
P_A'(-1)=\sum_e L_e\,b(\{e\})+2\sum_{\{e,f\}\ \mathrm{crossing}}b(\{e,f\}).
$$
For positive definite $A$ all complementary principal determinants are positive. Any support edge gives a strictly positive term in the first sum; continuity of the derivative extends strict increase to a left neighborhood of $-1$. No positive slope at $q=0$ is required.

**Checks on the endpoints and the order.** For two consecutive $2\times2$ blocks $B_t=\left(\begin{smallmatrix}1&t\\t&1\end{smallmatrix}\right)$, the polynomial of $B_t\oplus B_t$ is $(1+t^2q)^2$. If $t=1$ there is no left extension for this singular matrix. For $0<t<1$ the matrices are positive definite and the turning points $-1/t^2$ tend to $-1$ as $t\uparrow1$. Thus the left neighborhood cannot be uniform even in dimension four. In contrast, for a unit-diagonal matrix with only the edges $\{1,3\}$ and $\{2,4\}$, of squared magnitudes $u,v$, the polynomial is $1+(u+v)q^3+uvq^4$. Treating its two blocks as consecutive would incorrectly eliminate the crossing correction.

## Relation to earlier work

* [Bapat (1992)](https://doi.org/10.1080/03081089208818174) proposed monotonicity on $[-1,1]$; see also [Bapat–Lal (1994)](https://doi.org/10.1016/0024-3795(94)90497-9).
* [Da Fonseca (2005), Theorem 4.3](https://doi.org/10.1080/03081080500092372) already **stated the tree result** on $[-1,1]$ for Hermitian positive definite matrices. [Marques de Sá's 2015 letter](https://www.mat.uc.pt/preprints/ps/p1519.pdf) exhibits counterexamples to identities used in that proof, not to monotonicity itself. The [2017 preprint, Theorem 6.1](https://www.mat.uc.pt/preprints/ps/p1722.pdf), [published in 2018](https://doi.org/10.1016/j.laa.2017.11.024), proves the result for noncrossing forests. [Da Fonseca's correction, §3](https://arxiv.org/html/1804.02231#S3), also states the labeling restriction. The proof here removes it; no global priority is asserted.
* [Mitchell (2020)](https://doi.org/10.7153/oam-2020-14-56) studied the positive-definite and singular formulations and proved the rank-one and order-three cases. For general supports, [Kitamura](https://github.com/KitaKen1/bapat-lal-q-permanent-lean) reports an order-144 complex Hermitian counterexample on $[-1,1]$. [Da Fonseca–Goyal (November 2026)](https://arxiv.org/html/2611.14694v1#S1) construct unrestricted real positive definite counterexamples at each prescribed parameter above one. None of these statements, nor the present forest theorem, resolves the unrestricted real symmetric question on $[-1,1]$.
