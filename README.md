# Homogeneous cubic bent functions without affine derivatives outside the completed Maiorana–McFarland class in every even dimension at least ten

**Theorem.** For every even integer $n\ge10$ there exists a Boolean function on $\mathbf F_2^n$ whose algebraic normal form is homogeneous of degree three, whose Walsh coefficients all have magnitude $2^{n/2}$, whose derivative in every nonzero direction is quadratic, and which is not in the completed Maiorana–McFarland class $\mathcal M^\#$. These four properties hold for the **same function**.

This answers the unnumbered existence question immediately **before** Open Problem 5.1 in Polujan & Pott (2020), §5, p.1718. It is not a claim to solve their separately numbered problem for the first time, or to give an indecomposable family. The outstanding dimensions listed in the 2024 comparison are **12, 14, 18**. The proof below does not need that comparison for its correctness: five explicit seeds and closure under direct sums give all dimensions.

## 1. A cubic model in two odd-sized blocks

All operations on bits are in $\mathbf F_2$. For integers $k,l\ge2$, split the coordinates into $(a,b,s;c,d,t)$ with $a,b\in\mathbf F_2^k$, $c,d\in\mathbf F_2^l$, and $s,t$ bits. Select matrices $A,B$ of sizes $k,l$ with $A,A+I,B,B+I$ invertible. For example, multiplication by a field element other than 0 and 1 works in every dimension at least 2. With the standard dot product set
$$
F(a,b,s;c,d,t)=a\cdot A b+c\cdot B d+s(a\cdot b)+t(c\cdot d)+st. \tag{1}
$$
The formula in these coordinates is cubic, **not** homogeneous. We only claim homogeneous witnesses after §3.

**Bentness.** For fixed frequency $(u,v)$ on the first $2k$ coordinates and fixed $s$, the character sum over $a,b$ is
$$
\sum_{a,b}(-1)^{a\cdot(A+sI)b+u\cdot a+v\cdot b}
=2^k(-1)^{v\cdot(A+sI)^{-1}u}.
$$
The exponent on the right is an affine function of the single bit $s$. The second block contributes $2^l$ times a sign with exponent affine in $t$. Including selector frequencies, the remaining two-bit sum is, up to sign, a Walsh coefficient of $st$, hence is $\pm2$. Thus every complete Walsh coefficient has magnitude $2^{k+l+1}$, as required for $n=2k+2l+2$.

## 2. Absence of affine derivatives and exclusion of the completed class

For a cubic Boolean function $f$, write $T(u,v,w)=D_uD_vD_w f(0)$ with $D_u f(x)=f(x+u)+f(x)$. This is an alternating trilinear form, independent of base point, determined by the cubic coefficients. $D_u f$ is affine exactly if $T(u,\cdot,\cdot)=0$: the second differences of a quadratic encode all its quadratic coefficients.

Call $W$ relaxed if $T(W,W,V)=0$; denote its maximal dimension by $r(f)$. An $n/2$-dimensional space on which *all* second derivatives vanish identically is necessary for $\mathcal M^\#$ membership. Indeed $x\cdot\pi(y)+g(y)$ is affine in $x$ on every $x$-coset, and changing the input affinely and adding an affine output preserves the criterion. Such a space is in particular relaxed. Consequently $r(f)<n/2$ suffices to exclude $\mathcal M^\#$; it is not asserted as a necessary condition.

In a single block $E=U\oplus\mathbf F_2e$ with $\dim U=2k$, let $\sigma$ extract the selector. The polar form $B_U$ of $q(a,b)=a\cdot b$ on $U$ is nondegenerate. The top form of $s q(a,b)$ is
$$
T_E(v,w,z)=\sigma(v)B_U(w_U,z_U)+\sigma(w)B_U(v_U,z_U)+\sigma(z)B_U(v_U,w_U).
$$
Its radical is zero: a vector with $\sigma(v)=1$ has nonzero contraction on $U\times U$; one with $\sigma(v)=0$, $v_U\ne0$, pairs nontrivially with $e$ and a suitable $z\in U$.

If $W\subseteq U$ is relaxed, evaluating against $e$ shows $W$ is symplectically isotropic and hence $\dim W\le k$. If some $v\in W$ has $\sigma(v)=1$, for any $w\in W\cap U$ and $z\in U$ the equation $T_E(v,w,z)=B_U(w,z)=0$ forces $w=0$. Then $\dim W=1$. An isotropic $k$-space in $U$ attains the bound, so the maximal relaxed dimension is $k$.

The top form of (1) is the direct sum of two such forms. Its radical is the direct sum of their zero radicals. A relaxed subspace projects to a relaxed subspace in each block (test the third argument in one block at a time); the map to the product of its two projections is injective. Conversely the product of two relaxed spaces is relaxed. The exact relaxed dimension is therefore $k+l=n/2-1$. This proves all structural claims for (1). The same projection argument works for any direct sum of cubic functions, not just (1).

## 3. Five certified homogeneous seeds

Take $k=2$ and $l=2,3,4,5,6$ respectively. The companion matrix in dimension $j$ sends the bit polynomial $b(X)$ to $Xb(X)\bmod P_j$, where the binary masks for $P_2,\ldots,P_6$ are respectively $7,11,19,37,67$ (bit $i$ is the coefficient of $X^i$). Both this matrix and its sum with the identity are invertible, since $P_j(0)=P_j(1)=1$; irreducibility is not needed. In a packed integer the consecutive coordinates from least to most significant are $a,b,s,c,d,t$, each vector block least-index first.

For each $n$, the corresponding ordered list in [bases.json](bases.json) gives the binary integers for the columns $v_0,\ldots,v_{n-1}$ of a linear transformation $L$. Define the witness
$$
H_n(z)=F(Lz)+\sum_{i=0}^{n-1}F(v_i)z_i. \tag{2}
$$
The lists have full binary rank. Since $F(0)=0$, (2) has no constant or linear terms. Its quadratic coefficient at $i,j$ is $F(v_i+v_j)+F(v_i)+F(v_j)$, which is zero for each listed pair. Linear substitution cannot increase degree. The invertible substitution and linear correction preserve degree, absolute Walsh spectrum, derivative degrees, and relaxed dimension. In particular the remaining function is exactly a nonzero homogeneous cubic. The following finite data can be checked directly by integer arithmetic, not by reproducing the search for the bases.

| $n$ | cubic terms | quadratic terms | rank of contraction map | relaxed dimension | absolute Walsh coefficient |
|---:|---:|---:|---:|---:|---:|
| 10 | 59 | 0 | 10 | 4 | 32 |
| 12 | 108 | 0 | 12 | 5 | 64 |
| 14 | 176 | 0 | 14 | 6 | 128 |
| 16 | 275 | 0 | 16 | 7 | 256 |
| 18 | 410 | 0 | 18 | 8 | 512 |

The bases were obtained by choosing independent vectors and restricting remaining candidates to those passing the displayed pair test. The existence proof uses only the resulting columns, not search assumptions, heuristics or randomness.

## 4. Every even dimension

Write an arbitrary even $n\ge10$ as $n=j+10t$ with unique $j\in\{10,12,14,16,18\}$ and integer $t\ge0$. Take $H_j$ on $j$ coordinates plus $t$ copies of $H_{10}$ on disjoint sets of coordinates. Homogeneity is immediate. Walsh spectra multiply. The top-form radical is zero and relaxed dimensions add by §2, giving relaxed dimension $n/2-(t+1)<n/2$. This establishes the theorem for every even $n\ge10$. No claim of nondecomposability is made for these direct sums.

## Verification

In this directory, with Python 3.10+ and no external packages, run:
```sh
python3 verify_values.py
python3 verify_symbolic.py
```
The first program computes all truth tables of (2), inverts the Boolean subset transform for the complete ANF, computes every Walsh coefficient, and verifies full contraction rank. The second independently starts from monomials in the old variables and expands in the Boolean polynomial quotient using $z_i^2=z_i$. It also verifies slice matrix ranks and the explicit linear correction. The reported relaxed index is the proved index in §2; it is not asserted to have been checked by exhaustive subspace enumeration. Both codes output the SHA-256 of the same sorted list of ANF monomial masks (three bytes per mask, little endian), and include negative controls. They refuse optimized Python mode.

## Prior art and scope (checked November 2026)

* [Polujan & Pott, *Cubic bent functions outside the completed Maiorana–McFarland class* (2020)](https://doi.org/10.1007/s10623-019-00712-y), [open paper](https://d-nb.info/1250415683/34): §5 p.1718 distinguishes the all-dimensions question from separately numbered Open Problem 5.1. Proposition 1.3 gives the second-derivative criterion, Theorem 4.5 gives the relaxed-space direct-sum bound, and Theorem 4.9 records previous existence ranges. The published ten-variable homogeneous example is prior work; the 10 and 16 seeds here are provided for the independent induction, not to claim priority on those dimensions.
* [Zhang, Pašalić, Bapić & Wang, *Constructions of several special classes of cubic bent functions outside the completed Maiorana–McFarland class* (2024)](https://doi.org/10.1016/j.ic.2024.105149), [author manuscript](https://eprint.iacr.org/2022/1587): the comparison table in the updated manuscript (Table 1, row HCBFwAD outside the class) lists 12, 14 and 18 as the remaining dimensions. The work gives homogeneous nondecomposable examples and answers the separate no-direct-sum problem; we do not reassert that as new.
* [Li, Kan, Peng, Tan & Liu (2021)](https://doi.org/10.1587/transfun.2021EAL2003) give a ten-variable cubic bent function with no affine derivative outside the class; their reported existence theorem concerns ten variables, not the three outstanding homogeneous dimensions.
* Four-slice Walsh concatenation and linearly changing variables to obtain homogeneous cubics are existing techniques. Compare [Pasalic et al., *Bent functions satisfying the dual bent condition and permutations with the $(\mathcal A_m)$ property*](https://doi.org/10.1007/s12095-024-00724-z), [author version, especially §5](https://arxiv.org/abs/2310.10162). We claim neither the concatenation principle nor a generally new homogenization method. Relevant later work checked includes [Carlet et al., *On Counts and Densities of Homogeneous Bent Functions* (2025)](https://arxiv.org/abs/2511.12652) and [Pašalić et al., *Bent Functions and the Completed Maiorana–McFarland Class* (2026)](https://arxiv.org/abs/2608.21461).
* We found no previous explicit verification of the four simultaneous properties in all three residual dimensions in the sources checked. This is a scoped literature search, not a universal priority guarantee or a claim that the witnesses define new EA-equivalence classes.
