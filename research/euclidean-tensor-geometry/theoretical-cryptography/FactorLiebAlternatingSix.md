# Lieb permanental dominance for the natural action of A₆

**Catalogue #071.** Let \(A=(a_{ij})\) be a complex Hermitian positive semidefinite matrix of order six. For the natural alternating subgroup \(A_6\le S_6\) and every nonzero finite-dimensional character \(\chi\) of \(A_6\),
\[
 \frac{1}{\chi(e)}\sum_{\sigma\in A_6}\chi(\sigma)\prod_{i=1}^6a_{i,\sigma(i)}
 \ \le\ \operatorname{per}A.
\]
For each of the two eight-dimensional split irreducibles, on a correlation matrix this holds with an extra nonnegative deficit of at least \(\frac1{10}\sum_{i<j}|a_{ij}|^2\). Thus there is equality for either of these two characters exactly at diagonal matrices when all diagonal entries are positive. This treats the full natural **alternating subgroup**, not all subgroups of \(S_6\).

The proof of the split cases is an explicit positive rational combination of eleven inequalities in permutation class sums. In particular it permits arbitrary complex phases and does not use a permanent-on-top assumption. No computer approximation is a premise.

## 1. Reduction to two split characters

If a diagonal entry is zero, the corresponding row and column of \(A\) vanish by positive semidefiniteness and all monomials vanish. Otherwise normalize by a positive diagonal congruence. Every monomial is multiplied by the same factor \(\prod_i a_{ii}\) when going back from the correlation matrix to \(A\). Below the diagonal is one. It suffices to treat irreducible characters, since a normalized character of a direct sum is a convex combination of the normalized irreducible characters.

We use the usual restriction rule for the alternating subgroup of the symmetric group. A nonsplit irreducible of \(A_6\) is the restriction of an irreducible of \(S_6\) with partition \(\lambda\ne\lambda'\), and it has normalized generalized matrix function
\[
 \frac12\left(\operatorname{Imm}_\lambda(A)/f^\lambda
              +\operatorname{Imm}_{\lambda'}(A)/f^\lambda\right),
\]
by \(\chi_{\lambda'}=\operatorname{sgn}\,\chi_\lambda\); here \(f^\lambda=f^{\lambda'}\) is the degree. These ordinary order-six immanants already obey Lieb's inequality, for example by [Heyfron](https://doi.org/10.1017/S030500410006953X), who combines prior results with his own to cover all orders through eight except one order-eight partition. The unique self-conjugate partition of six is \((3,2,1)\), and its restriction splits as the two eight-dimensional irreducibles. Their character values are tabulated in [Hertweck, Table 1](https://arxiv.org/pdf/math/0703288). On cycle types \(1^6,2^2 1^2,3\,1^3,3^2,4\,2,5^+,5^-\), the rows have values
\[
             8,\ 0,\ -1,\ -1,\ 0,\ (1\pm\sqrt5)/2,\ (1\mp\sqrt5)/2 .
\]
Here \(5^+,5^-\) distinguish the two \(A_6\)-classes of cycle type \(5\,1\); their naming is arbitrary and a fixed odd relabeling interchanges them. Each of these classes is inverse invariant, since inversion of a 5-cycle is effected by two transpositions. All class sums below are real by Hermitian symmetry.

Write \(m_\sigma=\prod_i a_{i,\sigma(i)}\), \(u_{ij}=|a_{ij}|^2\), \(S=\sum_{i<j}u_{ij}\). Write \(U_\nu\) for the sum of \(m_\sigma\) over a cycle type \(\nu\), with the two indicated split sums \(U_{5^+}\) and \(U_{5^-}\). We abbreviate fixed points in subscripts. Let \(D=U_{2^2}\) and \(M=U_{2^3}\); these are the weighted matching sums of sizes two and three, with edge weights \(u_{ij}\). The split functions can be obtained by taking \(t=\pm\sqrt5\) in
\[
 f_t=1-\frac18(U_3+U_{3^2})
             +\frac{1+t}{16}U_{5^+}+\frac{1-t}{16}U_{5^-}.
\tag{1}
\]
We shall establish \(\operatorname{per}A-f_t\ge S/10\) for \(t=56/25\). Odd relabeling gives the other rational endpoint, and interpolation gives both values \(t=\pm\sqrt5\), since \((56/25)^2>5\).

## 2. Eleven nonnegative generators

For a vertex set \(I\), let \(P_I=\operatorname{per}A[I]\) and \(\Delta_I=\det A[I]\). Averages in this section always run uniformly over the specified choices.

1. \(F=\mathbb E_{v\ne w}(\Delta_{V\setminus\{v,w\}}-\Delta_{V\setminus\{v\}})\), for \(V=\{1,\ldots,6\}\). This is nonnegative by Fischer's determinant inequality with diagonal one.
2. For \(j=1,2,3\), put \(L_j=\mathbb E_{|I|=j}\sum_{\sigma:\,|\{i\in I:\sigma(i)\notin I\}|=1}m_\sigma\). These are nonnegative first cross-coefficients of Lieb's block expansion. A direct proof for these coefficients is given below.
3. \(R=\mathbb E_{|I|=2}(P_I-\Delta_I)(P_{V\setminus I}-\Delta_{V\setminus I})\). Each factor is nonnegative: \(\Delta_I\le1\) by Hadamard, and \(P_I\ge1\) by iterating Lieb's block inequality.
4. \(C=U_3+\frac23 S-\frac23 D\).
5. \(T=U_{3^2}+\frac49 D\).
6. \(B_- = U_{5^-}+\frac85D\) and \(B_+=-U_{5^+}+\frac85D\).
7. \(H=8M-U_6\).
8. \(Q=U_{3\,2}+\frac43D\).

Here and below the order of generators in the rational certificate is \(F,L_1,L_2,L_3,R,C,T,B_-,B_+,H,Q\).

**First crossing \(L_j\).** For a fixed cut \(I,J\), write \(A\) as a Gram matrix of vectors \(u_i\) with inner product linear in the second variable (in this paragraph only, \(u_i\) denotes a vector). The matrix \(G_I[i,i']=\operatorname{per}A[I\setminus\{i\},I\setminus\{i'\}]\) is the Gram matrix of symmetrized products of the vectors remaining after one is deleted. Use the same construction for \(G_J\). Indeed, for a list of \(m\) vectors the symmetrized tensor \((m!)^{-1/2}\sum_\pi v_{\pi(1)}\otimes\cdots\otimes v_{\pi(m)}\) gives the mixed permanent by the tensor inner product. For a permutation in the one-cross class, write \(i\mapsto j\) and \(j'\mapsto i'\) for the two cross arrows. The remaining assignments inside each part sum to \(G_I[i,i']G_J[j',j]\). Thus the one-cross coefficient is
\[
 \sum_{i,i'\in I;\ j,j'\in J}
     a_{ij}\overline{a_{i'j'}}\,G_I[i,i']\,\overline{G_J[j,j']}\ \ge0
\]
as a quadratic form of \(G_I\otimes\overline{G_J}\) on the conjugated array of cross entries. This includes a singleton part (empty symmetrized product).

**Cubic support.** Let the eigenvalues of \(A-I\) be \(x_i\), and put \(\tau=2S/6\). We have \(x_i\ge-1\), \(\sum_i x_i=0\), \(\sum_i x_i^2=2S\), and \(\sum_i x_i^3=3U_3\). The nonnegative sum \(\sum_i(x_i+1)(x_i-\tau)^2\) gives \(U_3\ge-\frac23 S+\frac29 S^2\). Also \(D\le S^2/3\): regard the edges of \(K_6\) as the vertices of a graph in which disjoint edges are adjacent. Its clique number is at most three. At fixed total mass \(S\), take a maximizing weight vector for \(D\) with minimum support. If two supported vertices are nonadjacent, transferring their total mass to the one with larger weighted neighbor sum does not decrease \(D\) and shrinks the support. Therefore a maximizer can be supported on at most three mutually disjoint edges and then \(D=\frac12(S^2-\sum_e u_e^2)\le S^2/3\). These two inequalities prove \(C\ge0\).

**Two triangles and a triangle with a swap.** For a triple \(I\) put \(S_I=\sum_{ij\subset I}u_{ij}\) and \(z_I=2\operatorname{Re}(a_{ij}a_{jk}a_{ki})\), with \(i,j,k\) its vertices in any order. Then
\[
       -S_I/3\le z_I\le 2S_I/3.
\tag{2}
\]
The upper bound comes from AM–GM and \(S_I\le 3\). For the lower bound, if \(S_I\le 3/4\), \(2(S_I/3)^{3/2}\le S_I/3\), and if \(S_I\ge3/4\), the minor \(1-S_I+z_I\ge0\) gives the claim. For complementary triples \(I,J\), (2) implies \(z_Iz_J\ge -(2/9)S_IS_J\). Summing over the ten unordered complementary pairs, each pair of disjoint edges occurs twice in \(\sum S_I S_J\). This proves \(T\ge0\). Similarly \(U_{3\,2}=\sum_{I,e:\,I\cap e=\varnothing}z_Iu_e\). Each pair of disjoint edges occurs four times in \(\sum_{I,e:\,I\cap e=\varnothing}S_Iu_e\): choose which edge is the disjoint swap, and choose the extra triangle vertex from the two unused vertices. This proves \(Q\ge0\).

**The split five-cycles.** On an oriented five-cycle delete any one of its five undirected edges; the four path edges split into two alternating pair matchings \(J_1,J_2\). The absolute product on the five-cycle is at most
\[
 \frac12\left(\prod_{e\in J_1}u_e+\prod_{e\in J_2}u_e\right)
\]
by \(|a_{ij}|\le1\) on the omitted edge and AM–GM. Upon averaging over the five omissions, each of the five disjoint pair matchings contained in that cycle receives weight \(1/5\), since it occurs for two omissions. For either \(A_6\)-class of 72 oriented five-cycles, each pair matching of \(K_6\) occurs eight times: \(A_6\) is transitive on the 45 pair matchings (an odd stabilizer is available by swapping endpoints of one matched edge), and the total count is \(72\cdot5=45\cdot8\). Hence \(|U_{5^\pm}|\le(8/5)D\), proving both bounds. This uses the two classes separately and does not replace each orientation by its sign.

**Six-cycles.** The two alternating perfect matchings on an oriented six-cycle give an upper bound for its absolute monomial by the average of their products of \(u_e\). A prescribed perfect matching occurs in sixteen oriented six-cycles: orient its three edges independently and choose a cyclic order of the three resulting blocks. Thus \(|U_6|\le 8M\), proving \(H\ge0\).

## 3. Rational decomposition

The identity is
\[
 \operatorname{per}A - f_{56/25} - \frac{S}{10}
 = \frac1{56000}\,
   (18000 F+47292 L_1+23010 L_2+1580 L_3+7275 R
    +24924 C+6504 T+7800 B_-+7880 B_++970 H+844 Q).
\tag{3}
\]
Here are detailed coefficient checks. All coefficients are per individual monomial in the given type, not divided by class size. If \(\sigma\) has \(f\) fixed points and \(m=6-f\) moved points, its coefficient in \(F\) is \(-\operatorname{sgn}(\sigma)fm/30\), by counting the ordered deleted \((v,w)\). Its coefficient in \(R\) equals \(4\) times the number of its transpositions divided by 15 if \(\sigma\) is even, and zero otherwise. Indeed, only a cut pair on a transposition has odd restriction in that pair, and the complementary restriction must also be odd. For \(L_j\), if the cycle lengths are \(\ell_1,\ldots,\ell_b\) (including fixed points), the numerator after multiplying by \(\binom6j\) is the coefficient of \(x^j\) in
\[
   \sum_{\ell_h\ge2}\ell_h (x+x^2+\cdots+x^{\ell_h-1})
                        \prod_{k\ne h}(1+x^{\ell_k}).
\]
This counts the unique cycle on which a size-\(j\) set has a single exit; its occupied vertices form one nonempty proper consecutive run. The rest of the coefficients follow directly from the definitions of the scalar generators. For clarity this gives:

| Cycle type | \(F\) | \(L_1\) | \(L_2\) | \(L_3\) | \(R\) | RHS coefficient in (3) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| \(1^6\) | 0 | 0 | 0 | 0 | 0 | 0 |
| \(2\,1^4\) | 4/15 | 1/3 | 8/15 | 3/5 | 0 | 9/10 |
| \(2^2 1^2\) | -4/15 | 2/3 | 8/15 | 2/5 | 8/15 | 1 |
| \(2^3\) | 0 | 1 | 0 | 3/5 | 0 | 1 |
| \(3\,1^3\) | -3/10 | 1/2 | 4/5 | 9/10 | 0 | 9/8 |
| \(3\,2\,1\) | 1/6 | 5/6 | 8/15 | 3/10 | 0 | 1 |
| \(3^2\) | 0 | 1 | 2/5 | 0 | 0 | 9/8 |
| \(4\,1^2\) | 4/15 | 2/3 | 4/5 | 4/5 | 0 | 1 |
| \(4\,2\) | 0 | 1 | 4/15 | 2/5 | 4/15 | 1 |
| \(5^+\) | -1/6 | 5/6 | 2/3 | 1/2 | 0 | 319/400 |
| \(5^-\) | -1/6 | 5/6 | 2/3 | 1/2 | 0 | 431/400 |
| \(6\) | 0 | 1 | 2/5 | 3/10 | 0 | 1 |

The rightmost column is exactly the LHS coefficients of (3) by (1). Each weight on the right of (3) is positive, so the deficit is at least \(S/10\). Odd relabeling and the interpolation described above complete the two split cases and the theorem. For an arbitrary matrix with positive diagonal the deficit in each split case is at least
\[
   \frac{\prod_i a_{ii}}{10}
      \sum_{i<j}\frac{|a_{ij}|^2}{a_{ii}a_{jj}} .
\]

### Replay and relation to known cases

The arithmetic and the matching incidences can be checked with ordinary Python 3:

~~~sh
python3 verify_factor_lieb_alternating_six.py
~~~

The checker enumerates all 720 permutations, computes the first five generator coefficients by literal subsets and also by the separate cycle formulas, checks actual alternating conjugacy for each five-cycle class, and checks all incidences used above. All arithmetic is integer or rational. The proof of nonnegativity in §2 is analytic.

[Lieb's original paper](https://doi.org/10.1512/iumj.1967.16.16008) states the generalized conjecture. [Zeng's order-four theorem](https://arxiv.org/abs/2608.21749) and [Yi Yu's order-five preprint record](https://doi.org/10.5281/zenodo.24549308) concern **all** subgroups in their respective orders. The latter record describes a different five-cycle approach at order five; its restricted proof files are not a dependency here. [Yi Yu's projective-action results](https://aixiv.online/abs/2611.03137) do not include the natural alternating action on six letters: the action arising from the identification \(A_6\cong\mathrm{PSL}_2(9)\) on the projective line has degree ten. [Lavi's quadratic immanant inequality](https://hexagonmath.org/pdf/2611.00429v1) refers to ordinary symmetric-group blocks and is not assumed in (3). No assertion is made about all order-six subgroups or the all-order conjecture.
