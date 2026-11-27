# Homogeneous cubic vectorial bent functions in every output dimension

**Theorem.** For each integer $r\ge2$, there is a vectorial bent function $H_r:\mathbf F_2^{8r}\to\mathbf F_2^r$ such that every nonzero binary linear combination of its coordinate functions has an algebraic normal form consisting only of degree-three monomials. This answers **Open Problem 4.31** in Alexandr Polujan's [*Boolean and Vectorial Functions: A Design-Theoretic Point of View*](https://opendata.uni-halle.de/bitstream/1981185920/38199/1/Polujan_Alexandr_Dissertation_2021.pdf), §4.5, p.123, in the affirmative. The output dimension is genuinely vectorial, starting at two, and the same construction works for all $r\ge2$.

A vectorial Boolean function is bent if every nonzero binary linear combination of its coordinates is bent. The degree and homogeneity statements below refer to the binary ANF in the specified coordinate basis, not to a degree notion for field polynomials.

## 1. A small binary permutation

Let $\pi:\mathbf F_2^4\to\mathbf F_2^4$ have the following component ANFs, with coordinates indexed $0,1,2,3$ and written $a,b,c,d$:
$$
\begin{aligned}
\pi_0&=b+ab+c+ac+bc,\\
\pi_1&=c+bc+d+bd+cd,\\
\pi_2&=ab+ad+bd,\\
\pi_3&=a+ad+c+cd+ac.
\end{aligned}
$$
The image list (least significant bit first) is
`0,8,1,12,11,10,9,13,2,6,5,4,3,14,7,15`.
These are exactly the sixteen different outputs. Observe also
$$
\pi(0)=0,\qquad \pi_i(e_i)=0,\qquad \pi_i(e_i+e_j)=0\quad(i\ne j). \tag{1}
$$
In component $i$ there is no linear term $y_i$, and each off-diagonal linear term $y_j$ has the same coefficient as the quadratic term $y_i y_j$. These facts give (1) directly.

## 2. A parity lift to a field permutation

Let $K=\mathbf F_{2^r}$ with any ordered binary basis whose first element is $1$. For $q\in K$ let $\rho(q)\in\mathbf F_2$ be the sum of its basis coordinates. Put $Z=\ker\rho$. Write each field coordinate uniquely as $y_i=\beta_i\cdot1+z_i$, with $\beta_i=\rho(y_i)$ and $z_i\in Z$.

Index the four slots by two-bit integers, with $\mathbin{\mathtt{xor}}$ denoting non-carrying bitwise addition of these indices. Split them into halves $\{0,1\}$ and $\{2,3\}$. For $\lambda=\beta_0+\beta_1$ define the permutation of slots
$$
\sigma_\beta(i)=
\begin{cases}
i\mathbin{\mathtt{xor}}2,&\lambda=0,\\
i\mathbin{\mathtt{xor}}1,&\lambda=1.
\end{cases}
$$
Thus the first branch exchanges the halves and the second swaps within each half. Both have no fixed slot. The field vector map
$$
\Pi_i(y)=\pi_i(\beta)\cdot1+z_{\sigma_\beta(i)} \tag{2}
$$
is a permutation of $K^4$. On the parity quotient it applies the binary permutation $\pi$, and on each fiber it applies an invertible reordering; recover $\beta$ first and then undo that reordering. Its binary coordinate degree is at most two: the second term is
$$
(1+\lambda)z_{i\mathbin{\mathtt{xor}}2}+\lambda z_{i\mathbin{\mathtt{xor}}1},
$$
and the parity extraction and fiber coordinates are binary-linear.

## 3. Binary cubic homogeneity and vectorial bentness

Define
$$
H_r(u,v)=\sum_{i=0}^3 v_i\Pi_i(u+v),\qquad u,v\in K^4. \tag{3}
$$
Its coordinate functions have binary degree at most three by (2) and bilinearity of field multiplication. We show $H_r(u,v)=0$ whenever the total binary Hamming weight of $(u,v)$ is at most two. The case $v=0$ is immediate. Otherwise:

* If all occupied basis bits lie in just one slot $i$ (counting corresponding $u_i$ and $v_i$ together), $\beta$ is either $0$ or $e_i$. Then $\pi_i(\beta)=0$ by (1), and the reordering in (2) reads a zero fiber coordinate in a different slot. Hence $\Pi_i(u+v)=0$.
* If two distinct slots $i,j$ are occupied, each has exactly one basis bit, so $\beta=e_i+e_j$. By (1) both $\pi_i(\beta)$ and $\pi_j(\beta)$ vanish. If the two slots are in the same half then $\lambda=0$ and both read fiber coordinates across the split, hence outside $\{i,j\}$. If they are in different halves then $\lambda=1$ and both read their within-half partners, again outside $\{i,j\}$. Thus $\Pi_i(u+v)=\Pi_j(u+v)=0$.

In either case every term with $v_i\ne0$ vanishes. Since evaluation at binary points of weight at most two determines all coefficients in degrees zero, one and two, every output coordinate in (3) has only cubic monomials.

Finally let $L:K\to\mathbf F_2$ be any nonzero binary-linear functional, which represents any nonzero binary linear combination of the output bits. The binary pairing $(a,x)\mapsto L(ax)$ is nondegenerate: for $a\ne0$ multiplication by $a$ is onto, and $L$ is not identically zero. Change variables invertibly from $(u,v)$ to $(x,y)=(v,u+v)$. At any binary Walsh frequency there exist $a,b\in K^4$ representing the corresponding linear character by $L(a\cdot x+b\cdot y)$. Sum first over $x$:
$$
\begin{aligned}
\sum_{x,y\in K^4}(-1)^{L(x\cdot\Pi(y)+a\cdot x+b\cdot y)}
&= |K|^4(-1)^{L(b\cdot\Pi^{-1}(a))}.
\end{aligned}
$$
The amplitude is $|K|^4=2^{4r}$, which is the bent amplitude in $8r$ bits. Hence all nonzero output combinations are bent. In particular no such combination is zero, so each has exact degree three. This proof requires neither a special irreducible polynomial for $K$ nor classification data.

## Reproducibility

Run `python3 verify.py` (Python 3.10+, standard library). The script independently computes the binary seed truth table from its monomials, finite-field products by reduction, the lifted permutation and the low-weight evaluations for $r=1,2,3$. For $(n,r)=(16,2)$ it computes all three nonzero components on every input; their ANFs have 168, 180 and 184 nonzero cubic terms and no other terms, and all 65,536 Walsh magnitudes in each component equal 256. A switched-branch control is still a permutation but fails homogeneity, so the tests distinguish the two hypotheses. These finite tests support but do not replace the all-$r$ proof.

## Prior art and exact scope (November 2026)

* [Polujan's dissertation](https://opendata.uni-halle.de/bitstream/1981185920/38199/1/Polujan_Alexandr_Dissertation_2021.pdf), §4.5, p.123, reports a negative search in six and eight variables and then asks the unrestricted existence question. This result supplies a sixteen-input, two-output example and an infinite family. It asserts neither the smallest possible example nor optimal output dimension. It is unrelated to the restriction on homogeneous scalar bent functions of degree at least four in the same dissertation's Open Problem 4.6.
* Vectorial bent functions based on the field inner product with permutations are standard. The construction here uses the classical Walsh argument, not a new definition or proof of the general MM construction; the contribution is the parity/fiber lift that preserves binary cubic homogeneity uniformly for all nonzero output components.
* We checked direct searches for “non-quadratic homogeneous vectorial bent functions”, the thesis problem number and variations, plus [Zhang, Pašalić, Bapić & Wang (2024), §5](https://doi.org/10.1016/j.ic.2024.105149), [Carlet et al. (2025)](https://arxiv.org/abs/2511.12652), and [Pašalić et al. (2026)](https://arxiv.org/abs/2608.21461). The 2024 vectorial construction has a different target (strongly outside the completed MM class); our components are in that class. The 2025 analysis concerns scalar homogeneous functions. We did not find an earlier resolution of Open Problem 4.31 in these materials. This is a scoped prior-art check, not a universal priority guarantee.
