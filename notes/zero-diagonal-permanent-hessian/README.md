# Exact tangent Hessian of the permanent at the zero-diagonal barycentre

**Status:** complete elementary proof of the *local spectral statement below*; the global zero-diagonal minimum conjecture is **not solved**. This is a research note, not a claimed resolution or a claim of historical priority. In particular, Burghduff (1995) already established that the barycentre is a strict local minimum. The explicit two-eigenvalue formula is recorded as an independent calculation; its novelty relative to every earlier treatment has not been established.

**Research author:** Yongxian Zhang (张永贤), School of Computer Science and Engineering, South China University of Technology; <mxymmxym1@gmail.com>; ORCID 0009-0000-3864-3536. No external funding. AI-assisted derivation and checks, not human peer review. No Lean formalization is claimed.

## Problem and exact scope

Let \(n\ge4\), \(U=(\mathbf1\mathbf1^{\mathsf T}-I)/(n-1)\), and
\[
\mathcal T_n=\{X\in\mathbb R^{n\times n}:x_{ii}=0,\ X\mathbf1=0,\ \mathbf1^{\mathsf T}X=0\}.
\]
The matrix \(U\) lies in the relative interior of the zero-diagonal doubly stochastic polytope and \(\mathcal T_n\) is the tangent space of its affine hull. Write \(D_m\) for the number of derangements of \(m\) objects, \(D_0=1\), \(D_1=0\).

**Theorem (full tangent Hessian spectrum).** With the Frobenius inner product, the Hessian of \(A\mapsto\operatorname{per}(A)\) at \(U\), restricted to \(\mathcal T_n\), has exactly the following orthogonal eigenspace decomposition:

| Space | Dimension | Hessian eigenvalue |
| --- | ---: | --- |
| \(\mathcal T_n^+=\{X\in\mathcal T_n:X=X^{\mathsf T}\}\) | \(n(n-3)/2\) | \(\displaystyle\lambda_+=\frac{D_{n-2}+2D_{n-3}+2D_{n-4}}{(n-1)^{n-2}}\) |
| \(\mathcal T_n^-=\{X\in\mathcal T_n:X=-X^{\mathsf T}\}\) | \((n-1)(n-2)/2\) | \(\displaystyle\lambda_-=\frac{D_{n-2}+2D_{n-3}}{(n-1)^{n-2}}\) |

Both eigenvalues are strictly positive. Consequently \(U\) is a nondegenerate strict local minimum of the permanent on the zero-diagonal doubly stochastic polytope. More precisely, for every \(X\in\mathcal T_n\),
\[
\left.\frac{d^2}{dt^2}\operatorname{per}(U+tX)\right|_{t=0}
=\lambda_+\|\tfrac12(X+X^{\mathsf T})\|_F^2
 +\lambda_-\|\tfrac12(X-X^{\mathsf T})\|_F^2.
\]
This does **not** compare \(\operatorname{per}(A)\) with \(\operatorname{per}(U)\) for arbitrary \(A\) in the polytope. The original global inequality, including its first unsettled order \(n=5\), remains open.

## Proof

Put \(N=n-2\). For two allowed off-diagonal positions \((i,j)\) and \((k,l)\), the mixed second derivative of the permanent vanishes when \(i=k\) or \(j=l\). Otherwise it equals the permanent of the submatrix of \(U\) obtained by removing rows \(i,k\) and columns \(j,l\). The remaining \(N\times N\) zero-one support has \(N-2+m\) prohibited entries on a partial matching, where
\(m=|\{i,k\}\cap\{j,l\}|\in\{0,1,2\}\). Every other entry equals \(1/(n-1)\). Thus the mixed second derivative is \(c_m/(n-1)^N\), where inclusion-exclusion gives
\[
 c_m=\sum_{s=0}^{N-2+m}(-1)^s\binom{N-2+m}{s}(N-s)!.
\]
We can alternatively count the permutations avoiding the first \(N-2+m\) diagonal positions according to which of the \(2-m\) unrestricted positions are fixed. This yields the exact identities
\[
 c_0=D_N+2D_{N-1}+D_{N-2},\qquad
 c_1=D_N+D_{N-1},\qquad c_2=D_N.
\]

Fix \(X\in\mathcal T_n\) and an allowed position \(i\ne j\). In the Hessian action \((HX)_{ij}\), only positions \((k,l)\) with \(k\ne i\), \(l\ne j\), \(k\ne l\) contribute. Because all row and column sums of \(X\) vanish, the sum of their \(x_{kl}\) values is \(x_{ij}\). Those with \(m=2\) comprise only \((k,l)=(j,i)\), contributing \(x_{ji}\). Those with \(m=1\) are the other positions in row \(j\) or column \(i\), contributing \(-2x_{ji}\). The remaining \(m=0\) positions therefore contribute \(x_{ij}+x_{ji}\). Consequently
\[
 (HX)_{ij}=
 \frac{c_0(x_{ij}+x_{ji})-2c_1x_{ji}+c_2x_{ji}}{(n-1)^N}
 =\frac{(D_N+2D_{N-1}+D_{N-2})x_{ij}+D_{N-2}x_{ji}}{(n-1)^N}.
\]
The diagonal of \(HX\) is not a tangent coordinate; the displayed formula is the gradient projected to the off-diagonal affine tangent. The operator on \(\mathcal T_n\) is a linear combination of \(X\) and \(X^{\mathsf T}\); in particular it preserves both zero diagonal and row/column-sum constraints. Substitution \(X^{\mathsf T}=\pm X\) gives the stated two eigenvalues.

For completeness, symmetric zero-diagonal matrices have \(n(n-1)/2\) independent entries; their \(n\) row-sum constraints are independent for \(n\ge3\), so \(\dim\mathcal T_n^+=n(n-3)/2\). Skew-symmetric zero-diagonal matrices have the same number of entries; their row-sum constraints have rank \(n-1\), giving \(\dim\mathcal T_n^-=(n-1)(n-2)/2\). Every tangent matrix is the sum of its symmetric and skew-symmetric parts. Since \(D_N+2D_{N-1}>0\) for \(N\ge2\), both eigenvalues are positive. The Hessian is positive definite on the tangent space, so the standard second-derivative argument and relative interiority of \(U\) give a strict local minimum. \(\square\)

## Exact independent checks

Run `python3 checker.py`. It directly counts the permanents of all relevant zero-one minors by integer dynamic programming; independently forms generators of both tangent sectors; verifies the Hessian action, eigenvalue numerators and sector dimensions **without floating-point arithmetic** for all \(4\le n\le8\). The finite checks are corroboration of the above all-order written proof, not a substitute for it. Neither the randomized explorations nor an exhaustive finite search can resolve the all-order global inequality.

## Relation to previous results

- H. Minc, *Theory of permanents 1982–1985*, Linear and Multilinear Algebra 21 (1987), 109–148, Conjecture 44: the **global** minimization question.
- D. London and H. Minc, *On the permanent of doubly stochastic matrices with zero diagonal*, Linear and Multilinear Algebra 24 (1989), 289–300: global minimum through \(n=4\).
- J. B. Burghduff, *Minimum permanents of doubly stochastic matrices with zero main diagonal*, Linear and Multilinear Algebra 40 (1995), 125–140: the **strict local minimum** in all orders, which this note does not re-claim as new.
- Current problem status / references: https://yair-lavi.com/mincs-list/conjecture-44/index.html (consulted October 9, 2026).
