# Two Ky Fan bounds for the Taylor coefficients

For complex Hermitian $A,B$ of the same finite size, write $H=A+B$ and set
$$
Q_k=\sum_{j=0}^k {k\choose j} A^j B^{k-j},\qquad R_k=\operatorname{Re}Q_k=(Q_k+Q_k^*)/2 .
$$
Thus $H^k$ and $Q_k$ are the $k$th derivatives at zero of $e^{tH}$ and $e^{tA}e^{tB}$, respectively. Write $s$ for the decreasing singular-value list, $\lambda$ for the decreasing list of signed eigenvalues of a Hermitian matrix, and $x\prec_w y$ for comparison of all prefix sums of the two decreasing lists, including the full sums.

**Theorem A (singular values).** Suppose $A,B$ each have at most two distinct eigenvalues. For every $k\ge1$,
$$
s(H^k)\prec_w s(R_k)\prec_w s(Q_k).
$$
The same holds whenever $A,B$ admit a common orthogonal decomposition into reducing blocks of dimension at most two. In particular, it holds for every pair of size two. Since $\lambda(H^k)\prec_w s(H^k)$, this implies Zhang's original comparison in these classes.

**Theorem B (signed eigenvalues).** Under the global two-spectrum hypothesis, $\lambda(H^k)\prec_w\lambda(R_k)$ holds for every even $k$. For each odd $k\ge5$ it holds if and only if the pair commutes or $c\ge0$, where
$$
c=\tfrac12\big(\lambda_{\max}(A)+\lambda_{\min}(A)+\lambda_{\max}(B)+\lambda_{\min}(B)\big).
$$
In dimension two $c=\operatorname{Tr}(H)/2$; the analogous normalized-trace identity need not hold in larger dimensions.

**Prior boundary.** In every dimension, $R_1=H$ and $R_2=H^2$, and Zhang treated orders three and four. His published article already gives an order-five counterexample to the signed intermediate comparison; Pauli examples for all odd orders from five are also prior. The centered scalar moment bound below is explicitly in Forrester–Thompson, and the shifted *signed trace* conclusions follow from it. The point here is the non-trace prefix and the full **singular** prefix, and hence all orders on the specified class, not a new scalar trace inequality. See [sources](SOURCES.md).

## 1. Centered coefficients in size two

A commuting pair gives $Q_k=R_k=H^k$. For a noncommuting pair write
$$
A=a_0I+aU,\quad B=b_0I+bV,\quad c=a_0+b_0,\quad K=aU+bV ,
$$
where $a,b>0$ are the spectral half-gaps and $U,V$ are traceless Hermitian symmetries. Put $\tau=\operatorname{Tr}/2$ and $\rho=\tau(UV)$. Every traceless Hermitian matrix in size two squares to a scalar, so $UV+VU=2\rho I$. The Hilbert–Schmidt Cauchy–Schwarz bound gives $|\rho|\le1$; equality would give $U=\pm V$. Thus $|\rho|<1$ and
$$
K^2=h^2 I,\quad h^2=a^2+b^2+2ab\rho>0,\qquad J=K/h .
$$
Let $X$ take the two values $(a+b)^2,(a-b)^2$ with probabilities $(1+\rho)/2,(1-\rho)/2$. Write $M_m=\mathbb E[X^m]$ for $m\ge1$, $M_0=1$. In particular $M_1=h^2$. With $E_j=R_j(aU,bV)$ and $E_0=I$, for $m\ge0$:
$$
E_{2m}=M_m I,\qquad \tau(E_{2m+1})=0,\qquad \tau(JE_{2m+1})=M_{m+1}/h.
$$

Indeed, with $P_e=(I+eU)/2$ and $S_f=(I+fV)/2$ for signs $e,f$, the spectral expansions give
$$
E_j=\sum_{e,f}(ea+fb)^j\operatorname{Re}(P_eS_f),\qquad
\operatorname{Re}(P_eS_f)=\tfrac14[(1+ef\rho)I+eU+fV].
$$
Pair $(e,f)$ with $(-e,-f)$. Even powers retain precisely the scalar term. The odd powers are traceless and satisfy
$$
E_{2m+1}=\tfrac12\big[(a+b)^{2m+1}(U+V)+(a-b)^{2m+1}(U-V)\big].
$$
Since $\tau(K(U\pm V))=(a\pm b)(1\pm\rho)$, this gives the stated projection identity, also when $a=b$. Alternatively it follows from $\tau(KE_j)=\tau(E_{j+1})$ by differentiating the trace of the centered exponential product and cycling the $bV$ factor.

By Jensen, $M_m\ge h^{2m}$, strictly for $m\ge2$: the two distinct nonnegative atoms have positive weights. This is the [Forrester–Thompson coefficientwise trace estimate](https://arxiv.org/pdf/1408.2008), §2.1, paragraph following (2.6), not just an inequality between whole exponentials. It yields both $E_{2m}\ge h^{2m}I$ and $\tau(J E_{2m+1})\ge h^{2m+1}$. No matrix-order assertion about the odd centered coefficients is needed.

## 2. Two different singular-value tests

The scalar shift in the exponential product gives $R_k=\sum_j {k\choose j} c^{k-j} E_j$. Write $u=\tau(R_k)$, $v=\tau(JR_k)$. For $c\ge0$, all binomial weights are nonnegative. Taking the even and odd contributions separately,
$$
u\ge U_0=\tfrac12[(c+h)^k+(c-h)^k],\qquad
v\ge V_0=\tfrac12[(c+h)^k-(c-h)^k].
$$
Both right sides are nonnegative by their binomial expansions. For the rank-one projection $P=(I+J)/2$, the Rayleigh quotient gives
$$
\|R_k\|_\infty\ge \lambda_{\max}(R_k)\ge \operatorname{Tr}(PR_k)=u+v
\ge (c+h)^k=\|H^k\|_\infty .
$$
For the second prefix, use $I$ and $J$ separately in trace-norm duality:
$$
\|R_k\|_1\ge\max\{|\operatorname{Tr} R_k|,|\operatorname{Tr}(JR_k)|\}
\ge 2\max(U_0,V_0)=|(c+h)^k|+|(c-h)^k|=\|H^k\|_1 .
$$
The equality uses $|x|+|y|=\max(|x+y|,|x-y|)$. The second test matters at odd orders when $c<h$: the trace does not then control the trace norm of $H^k$.

For $c<0$ reflect $(A,B)$ to $(-A,-B)$. This multiplies all three degree-$k$ matrices by $(-1)^k$ and preserves their singular values. The two tests prove the first leg of Theorem A. Its second leg holds without hypotheses, since for every Ky Fan norm, the triangle inequality and invariance under adjoint give
$$
\|R_k\|_{(r)}\le (\|Q_k\|_{(r)}+\|Q_k^*\|_{(r)})/2=\|Q_k\|_{(r)} .
$$

## 3. When the signed comparison holds

For $c\ge0$, the preceding Rayleigh quotient bounds the top **signed** eigenvalue of $H^k$ and $2u\ge2U_0$ bounds its trace. These are both signed prefixes. For even orders reflection does not change either matrix, so this holds for all $c$.

For odd $k\ge5$, on a noncommuting block with $c<0$, the signed trace defect from the centered moments is
$$
\tau(R_k-H^k)=\sum_{0\le2j\le k}{k\choose 2j}c^{k-2j}(M_j-h^{2j})<0 .
$$
The $j=0,1$ terms vanish, all later terms are negative, and $j=2$ occurs. Thus the full signed prefix fails; no claim that every prefix fails is required. This does not violate either singular-value inequality. The necessity from the signed trace is already a scalar-shift consequence of the earlier moment formula. Sufficiency also needs the top signed eigenvalue test.

## 4. The reducing blocks

If one matrix is scalar the pair commutes. Otherwise the spectral-midpoint normalization in arbitrary dimension again gives two Hermitian symmetries $U,V$. They have common reducing blocks of dimension at most two (the [classical two-projections decomposition](https://doi.org/10.1090/S0002-9947-1969-0251519-5)). To see this directly, let $W=UV$. It is unitary, $UWU=W^*$, and $V=UW$. For a nonreal eigenvalue $z$ in the upper semicircle, $U$ maps an orthonormal basis $x_j$ of its eigenspace to a basis $Ux_j$ of the conjugate eigenspace. The spans of $x_j,Ux_j$ are pairwise orthogonal and invariant under $U,W$, hence under $V$. On the $W=\pm I$ eigenspaces, $V=\pm U$, giving simultaneous eigenlines. These exhaust the space. Both $U$ and $V$ have zero diagonal and eigenvalues $+1,-1$ on each nonreal-pair block. Consequently the block half-gaps and midpoint sum there are the common global values $a,b,c$.

For block-diagonal matrices, the sum of the $r$ largest entries of a concatenation is the maximum over allocations of exactly $r$ slots to the blocks of the sums of the corresponding block prefixes. This holds for signed lists too; zero slots are allowed. Theorem A thus passes to any direct sum of blocks of size at most two. Under the global two-spectrum hypothesis, the favorable signed cases hold in every block. In the adverse case all noncommuting blocks have the same $c<0$ and strictly negative full trace defect, while commuting blocks contribute zero. Thus the global signed comparison also fails. This proves Theorem B; it does not give the same signed criterion for an arbitrary sum of blocks with different midpoint shifts.
