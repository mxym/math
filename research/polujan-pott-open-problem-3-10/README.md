# Quadratic permutations giving homogeneous cubic bent functions for every cubic offset

**Theorem.** For every integer $m\ge3$ there exists a quadratic permutation $\pi_m$ of $\mathbf F_2^m$ such that the **same** invertible linear change of variables $T_m:(u,v)\mapsto(v,u+v)$ makes
$$
f_{\pi_m,\psi}(T_m(u,v))=v\cdot\pi_m(u+v)+\psi(u+v)
$$
a homogeneous cubic bent function for **every** homogeneous cubic $\psi$ on $\mathbf F_2^m$, also allowing $\psi=0$. If $m\equiv3\pmod4$, a single permutation formula acts on the entire block and is an involution commuting with every permutation of the $m$ coordinates.

This gives an affirmative answer to Polujan and Pott's **Open Problem 3.10** ([journal §3.3, p. 1713](https://link.springer.com/article/10.1007/s10623-019-00712-y), [open PDF p. 1713](https://d-nb.info/1250415683/34#page=13)), with a witness in every possible dimension $2m\ge6$. The problem also appears as Open Problem 4.30 of Polujan's 2021 dissertation. This is **not** the separate question about functions outside the completed Maiorana–McFarland class: every function here is in the completed class by construction.

## 1. A test in the fixed shear coordinates

Work over $\mathbf F_2$, and write $e_i$ for the coordinate vectors. For a vector map $\pi$ of degree at most two, suppose
$$
\pi(0)=0,\qquad \pi_i(e_i)=0,\qquad
\pi_i(e_i+e_j)=0\quad (i\ne j). \tag{1}
$$
Then $g(u,v)=v\cdot\pi(u+v)$ vanishes on all inputs $(u,v)$ of total weight at most two. If $v=0$ this is immediate. If $v=e_i$, then $u\in\{0,e_i,e_j:j\ne i\}$, and (1) applies to $u+v$. If $v=e_i+e_j$ then $u=0$, and both $i$ and $j$ components vanish by (1). Conversely, all tests in (1) are necessary for this same shear with zero offset: use inputs $(u,v)=(e_i,e_i),(0,e_i),(e_j,e_i)$ respectively. This is a criterion for **this shear**, not for arbitrary linear changes of basis.

Because $g$ has degree at most three, vanishing at all points of weight at most two is exactly the absence of constant, linear and quadratic ANF coefficients. A cubic monomial of $\psi$ uses three distinct coordinates; upon $y_i=u_i+v_i$ it expands to eight cubic monomials because the three variable-pairs are disjoint. Thus $g+\psi(u+v)$ has only cubic terms. Its Walsh coefficients are nonzero of magnitude $2^m$: in coordinates $(x,y)=T_m(u,v)$, where $T_m^{-1}(x,y)=(y+x,x)$, the sum over $x$ kills every $y$ except the uniquely specified $\pi^{-1}(a)$ at frequency $(a,b)$, giving
$$
W_{f_{\pi,\psi}}(a,b)=2^m(-1)^{\psi(\pi^{-1}(a))+b\cdot\pi^{-1}(a)}.
$$
The invertible linear change just permutes the Walsh frequencies. In particular the homogeneous function is not zero; it has exact degree three. The assumptions also force $\pi$ itself to have degree two: (1) annihilates the coefficients of an affine $\pi$, which cannot be a permutation.

## 2. One formula in dimension $3$ modulo $4$

Write $S(y)=\sum_i y_i$, $Q(y)=\sum_{i<j}y_i y_j$, and $p(y)=S(y)+Q(y)$. Set
$$
\pi(y)=y+p(y)\mathbf 1. \tag{2}
$$
For $y=0$, $e_i$, or $e_i+e_j$, the relevant $p$ value is respectively $0,1,1$, proving (1). Expanding at the complementary input gives
$$
p(y+\mathbf 1)+p(y)
=m+\binom m2+(m-1)S(y)=0\qquad (m\equiv3\pmod4).
$$
Thus the flip bit is unchanged after either doing nothing or adding $\mathbf 1$; applying (2) twice gives $y$. This is an explicit all-coordinate involution; its mixed products couple different coordinates, and the expression does not rely on a decomposition into small blocks.

It is also the only coordinate-permutation-equivariant quadratic permutation satisfying (1) in the fixed coordinate system for $m\ge3$. Indeed the stabilizer of $i$ forces the $i$-th row's degree-at-most-two coefficients to depend only on whether they contain $i$. After (1) the row is
$$
b(1+y_i)\sum_{j\ne i} y_j+d\sum_{\substack{j<k\\j,k\ne i}}y_jy_k
$$
with $b,d$ independent of $i$. If $b=0$, each unit vector maps to zero. If $b=1,d=0$, each vector of weight two maps to zero. The remaining choice $b=d=1$ is (2). On each pair $\{y,y+\mathbf 1\}$ this is a permutation exactly when $p$ agrees on the two points. The displayed identity holds everywhere exactly for $m\equiv3\pmod4$ (for even $m$ it depends nontrivially on $S$; for $m\equiv1\pmod4$ it equals one). This uniqueness statement concerns only equivariant quadratic permutations for this shear, not all possible families.

## 3. Two extra small blocks give every dimension

The following are explicit component ANFs in variables $a,b,c,d$ (and $e$ in dimension five), in that order. A product such as $ab$ means multiplication of two bits.

| component | $\pi_4(a,b,c,d)$ | $\pi_5(a,b,c,d,e)$ |
|---|---|---|
| 1 | $b+ab+c+ac+bc$ | $b+ab+c+ac+bc$ |
| 2 | $c+bc+d+bd+cd$ | $a+ab+c+bc+ac$ |
| 3 | $ab+ad+bd$ | $a+ac+b+bc+ab+de$ |
| 4 | $a+ad+c+cd+ac$ | $e+de+ab+ac+bc$ |
| 5 | | $d+de+ab+ac+bc$ |

There are no constant terms. In row $i$ every off-diagonal linear term $y_j$ has the same coefficient as $y_i y_j$, and there is no $y_i$ term, so (1) follows by substituting support $\{i\}$ or $\{i,j\}$. Bijection is a finite check. Interpret the first variable as the least significant bit. The images at successive integers starting with zero are:

* $m=4$: `0,8,1,12,11,10,9,13,2,6,5,4,3,14,7,15`.
* $m=5$: `0,6,5,28,3,26,25,31,16,22,21,12,19,10,9,15,8,14,13,20,11,18,17,23,4,2,1,24,7,30,29,27`.

Each list contains every integer in its respective range exactly once. For a product of such permutations on disjoint coordinate blocks, (1) stays true. In particular if $i,j$ belong to distinct blocks, component $i$ at $e_i+e_j$ only sees $e_i$ inside its own block, hence is zero. Every integer $m\ge3$ is a nonnegative sum of 3, 4 and 5: take its unique residue representative from $\{3,4,5\}$ and append blocks of 3. Combine the $m=3$ involution with the two extra blocks. Note that we take a product only of the permutations; the offset $\psi$ in §1 may have arbitrary **cross-block** cubic monomials.

## Reproducibility

Run `python3 verify.py` (Python 3.10+, standard library). The script re-evaluates every seed table from the component ANFs rather than assuming the lists, checks the fixed shear conditions and the complete transformed ANF, and computes every Walsh coefficient for the requested small examples. It computes the ANF of each transformed base offset monomial independently from the truth table, including cross-block monomials for the product in $m=6$. It also checks nonzero offsets directly. The uniform results are the proofs above, not extrapolations from verification. The wrong-residue symmetric formula in $m=5$ and the identity permutation in $m=3$ are negative controls to catch different errors.

## Prior art and scope (November 2026)

* [Polujan & Pott (2020), §3.3, Remark 3.8, Eq. (3.6), and Open Problem 3.10](https://doi.org/10.1007/s10623-019-00712-y): they already found twelve-variable examples and explicitly recognized disjoint supports as preserving homogeneity. A finite genuinely defect-free example with such supports can be repeated by products to get infinitely many dimensions where all offsets remain valid, an immediate extension of that observation. We do not claim to invent the offset mechanism, the use of products or the MM construction. The contribution is an explicit uniform involution regime, the stronger every-dimension construction, and the exact result within the fixed-shear equivariant subclass.
* [Polujan dissertation (2021), Open Problem 4.30, p.122](https://opendata.uni-halle.de/bitstream/1981185920/38199/1/Polujan_Alexandr_Dissertation_2021.pdf), asks the same infinite-family question, and separates it from degree-at-least-four homogeneous bent functions (Open Problem 4.6). Nothing here addresses the latter.
* [Zhang, Pašalić, Bapić & Wang (2024)](https://doi.org/10.1016/j.ic.2024.105149) address a different problem, homogeneous cubics **outside** the completed class. [Kudin et al. (2024), §5](https://doi.org/10.1007/s12095-024-00724-z) use the dual-bent condition to construct homogeneous cubics, not this fixed-permutation, fixed-change, arbitrary-offset statement. The older primary construction with identity permutation and selected offset is discussed as Result 3.1 of Polujan–Pott.
* We checked searches for the two problem numbers, the cited article and the arbitrary-offset condition, [Carlet et al. (2025)](https://arxiv.org/abs/2511.12652), [Pašalić et al. (August 2026)](https://arxiv.org/abs/2608.21461), and [Wu, Wang & Hyun (September 2026)](https://arxiv.org/abs/2609.13968). The last addresses the symplectic-design conjecture with a nonlinear change, not Open Problem 3.10. We did not find the all-dimension statement or its fixed-shear classification in the material checked. The small permutations, including the six-variable homogeneous bent functions they produce, are not claimed to define new equivalence classes. This is a scoped search, not a priority guarantee.
