# When is the Johnston–Russo–Sikora pure-state overlap guarantee sharp?

This AI-assisted research note addresses a question in [Johnston–Russo–Sikora (JRS), Quantum 9, 1622 (2025)](https://doi.org/10.22331/q-2025-02-04-1622), [arXiv:2311.17047v2, §6](https://arxiv.org/html/2311.17047). Here $n$ counts **states**, not dimension. For normalized pure vectors $v_1,\dots,v_n$ in any finite complex dimension, perfect exclusion (antidistinguishability) means that positive semidefinite effects $M_i$ sum to the identity and $\langle v_i,M_iv_i\rangle=0$ for each $i$. As in JRS, an effect can be zero; this is not the stronger convention requiring every label to be used.

Write $s_n=(n-2)/(2(n-1))$ for the **squared** JRS overlap cap. Let $A_n$ be the infimum of $\max_{i\ne j}|\langle v_i,v_j\rangle|^2$ over non-antidistinguishable $n$-tuples in all finite dimensions. By JRS Corollary 5.4, $A_n\ge s_n$, and a tuple meeting the cap itself is always antidistinguishable. Tightness means $A_n=s_n$ (approach via failures, not failure at the endpoint).

**Claim.** $A_5=s_5=3/8$. For each fixed $n\ge6$, $A_n>s_n$. Together with the previously proved sharpness for $n=2,3,4$, this decides the qualitative tightness question for every $n$. The [trureturing settlement](https://the-omega-institute.github.io/trureturing-mdbook/Problems/johnston-russo-sikora-2025-antidistinguishability-tightness.html) already gives an explicit positive squared-overlap gap for $n\ge10$ under these same finite-dimensional pure-state and POVM conventions; for $n=7,8,9$, the earlier complex-equiangular-line spectral cubic of [Balla, Theorem 2.3 and Lemma 4.3](https://arxiv.org/html/2110.15842) already excludes the boundary configuration after the JRS boundary reduction (§2 below). The cases of primary interest here are therefore sharpness at five and nonsharpness at six. We give a common short proof for all $n\ge6$, not a claim that all these cases require new geometric bounds. The classical degree-two projective Jacobi kernel also rules out the boundary from six on, as shown in §2. The contribution is the application to the exclusion cutoff and the explicit five-state sharpness witness, not a new general line bound. This proof gives no optimal $A_n$ or numerical gap for $n\ge6$.

## 1. Compactness forces an equiangular configuration of rank at most three

Fix $n\ge3$. If $A_n=s_n$, take a sequence of non-antidistinguishable tuples whose squared overlap maxima converge to $s_n$. Their Gram matrices lie in the compact set of positive semidefinite complex $n\times n$ matrices with diagonal one (entries have modulus at most one). Thus after taking a subsequence $G_j\to G$; $G$ is itself a Gram matrix, for instance of the columns of $G^{1/2}$ in $\mathbb C^n$. Neither the original dimensions nor a uniform gap for all $n$ enter. We do **not** assume non-antidistinguishability is closed or that the limiting tuple fails.

Let $p_0\ge p_1\ge\dots\ge p_{n-1}\ge0$ be the eigenvalues of $G/n$; they sum to one. JRS Theorem 5.1 says $\sqrt{p_0}\le\sum_{i>0}\sqrt{p_i}$ is sufficient for antidistinguishability for every Gram matrix. Its contrapositive is strict for each failure; by continuity of ordered eigenvalues and square roots the limit satisfies $\sqrt{p_0}\ge\sum_{i>0}\sqrt{p_i}$. Also
$$
\sum_i p_i^2=\operatorname{Tr}(G^2)/n^2\le[n+n(n-1)s_n]/n^2=1/2.
$$

Here is the exact equality argument. Write $T=p_0$, $y_i=\sqrt{p_i}$ for $i>0$, $u=\sum y_i^2$, $h=\sum_{i<j} y_i y_j$ (positive indices only). Then $T\ge u+2h$. Therefore
$$
2\sum_i p_i^2-(\textstyle\sum_i p_i)^2
=(T-u)^2-4\sum_{i<j}y_i^2y_j^2
\ge4\bigl(h^2-\textstyle\sum_{i<j}y_i^2y_j^2\bigr)\ge0.
$$
Both inequalities must be equalities. In particular at most one of the nonnegative pair products $y_i y_j$ may be nonzero, so $G$ has rank at most three. Moreover its squared trace-purity bound was equality. Since every off-diagonal squared overlap was bounded by $s_n$, *every one equals* $s_n$. The rank-three equality condition is $\sqrt{p_0}=\sqrt{p_1}+\sqrt{p_2}$. This low-rank route is consistent with the prior $n\ge10$ argument. For six through nine states the dimension-square bound alone is insufficient; the cubic of Balla already supplies an obstruction from seven on.

## 2. A qutrit obstruction at the boundary for $n\ge6$

For a limiting equiangular tuple let $P_i=v_i v_i^*$ on its span and $B=n^{-1}\sum_i P_i$. The nonzero eigenvalues of $B$ are those of $G/n$, so $\operatorname{Tr}B=1$, $\operatorname{Tr}B^2=1/2$. The real Hilbert space of Hermitian matrices has inner product $\langle H,K\rangle=\operatorname{Tr}(HK)$. The Gram matrix of the $P_i$ is $(1-s_n)I_n+s_n\mathbf1\mathbf1^T$, nonsingular. Rank at most two is impossible for $n\ge5$: Hermitian matrices on a two-dimensional space have real dimension four. Thus the span is exactly $\mathbb C^3$, and $B$ is positive definite there.

Set $T_i=P_i-B$ and let $W=\operatorname{span}_{\mathbb R}\{T_i\}$. Since $\operatorname{Tr}(P_i B)= [1+(n-1)s_n]/n=1/2$, $W$ is orthogonal to $I$ and $B$. The Gram matrix of the $T_i$ is $(1-s_n)(I_n-\mathbf1\mathbf1^T/n)$. In any real orthonormal basis $H_a$ of $W$ the coordinate matrix $D_{ai}=\langle H_a,T_i\rangle$ thus has $D D^T=(1-s_n)I$: its nonzero singular values all equal $\sqrt{1-s_n}$. Expanding $T_i=\sum_aD_{ai}H_a$ and summing squares, with no commutativity assumption, gives
$$
n(B-B^2)=\sum_i T_i^2=(1-s_n)\sum_{a}H_a^2.
$$
The left equality follows by expanding $(P_i-B)^2$, using $P_i^2=P_i$ and $\sum P_i=nB$.

For *any* Hilbert–Schmidt real orthonormal basis of $\mathrm{Herm}(3)$ the sum of the squares of its elements is $3I$. Indeed, take the three diagonal matrix units and for each $j<k$ take $(E_{jk}+E_{kj})/\sqrt2$ and $i(E_{jk}-E_{kj})/\sqrt2$. This gives $3I$, and the sum is unchanged under a real orthogonal change of basis. Extend the basis of $W$ by the two mutually orthonormal Hermitian matrices $I/\sqrt3$ and $\sqrt6(B-I/3)$, and then complete it if needed. Dropping only positive semidefinite squares yields the Loewner bound
$$
\frac{n}{1-s_n}(B-B^2)\preceq\frac83 I -6(B-I/3)^2 .
$$
Substitute $n/(1-s_n)=2(n-1)$. Equivalently
$$
0\preceq2(I-B)(I-(n-4)B).
$$
The largest eigenvalue $b$ of $B$ is strictly below 1 and strictly greater than $1/2$: otherwise $\sum p_i^2\le b\sum p_i\le1/2$ would force all three positive eigenvalues to be $1/2$, contradicting trace one. At $n\ge6$ the displayed matrix eigenvalue $2(1-b)(1-(n-4)b)$ is strictly negative. This rules out the boundary limit. For $n>9$ one can already stop at the linear independence of $n$ projectors in $\mathrm{Herm}(3)$. We have therefore shown $A_n>s_n$; equivalently one can add a sufficiently small (per-$n$) positive amount to $s_n$ while retaining the sufficient condition, by using any amount strictly below $A_n-s_n$.

### Earlier spectral obstruction already covers seven through nine states

For precision about prior work, let $b$ again be the top eigenvalue of $B$. Its two remaining positive eigenvalues have sum $1-b$, so $1/2=\operatorname{Tr} B^2\ge b^2+(1-b)^2/2$, giving $1/2<b\le 2/3$. The Gram matrix has top eigenvalue $nb$ and constant off-diagonal modulus $\alpha=\sqrt{s_n}$. In this setting [Balla, Theorem 2.3 and Lemma 4.3](https://arxiv.org/html/2110.15842) give, after inserting $\lambda_1=nb$, $\alpha^2=s_n$ and multiplying by $2(n-2)/n^3$,
$$
f_n(b):=2(n-2)b^3-(n-1)b+1\ge0.
$$
This convex cubic has $f_n(1/2)=(4-n)/4$ and $f_n(2/3)=(13-2n)/27$. Both endpoint values are negative for $n\ge7$, so no boundary tuple from §1 exists there. This is a consequence of Balla's line inequality with the JRS limiting reduction, not a claim that Balla stated the quantum conclusion. For $n=6$, $f_6(2/3)=1/27>0$; the scalar-cubic comparison alone does not settle this case. The proof above avoids the cubic and handles six as well. No application of Balla's general extremal size Theorem 1.11 is required.

### Alternative from the classical projective Jacobi kernel, including six states

This argument uses a classical geometric tool instead of the projection proof. In complex projective dimension two the degree-two Jacobi kernel is
$$
K(t)=P_2^{(1,0)}(2t-1)=10t^2-8t+1,\qquad t=|\langle v,w\rangle|^2.
$$
For any finite list of unit qutrits, the matrix of these kernel values is positive semidefinite by the addition formula; see [Koornwinder (1973), §3, eq. (3.1)](https://doi.org/10.1137/0125027), [Delsarte–Goethals–Seidel (1975), Theorem 3.3](https://research.tue.nl/en/publications/bounds-for-systems-of-lines-and-jacobi-polynomials/), or [Cohn–Kumar–Minton, §2.2](https://arxiv.org/pdf/1308.3188).

On the limiting configuration from §1 the all-ones vector is an eigenvector of the kernel matrix with eigenvalue
$$
3+(n-1)K(s_n)=-\frac{n(n-6)}{2(n-1)}.
$$
This is negative for $n\ge7$. For $n=6$ it is zero. Append any unit vector $e$ to the six. In the positive semidefinite extended matrix, $(1,1,1,1,1,1,0)$ still has quadratic form zero, and hence belongs to its kernel. The final row gives $\sum_i K(|\langle e,v_i\rangle|^2)=0$. By convexity,
$$
K(\langle e,B e\rangle)\le0.
$$
In particular $K(b_j)\le0$ at each of the three eigenvalues of $B$. But $\sum_j K(b_j)=10\operatorname{Tr}B^2-8\operatorname{Tr}B+3=0$, so each $b_j$ is a root $(4\pm\sqrt6)/10$. Three such numbers cannot sum to one: their sum is $(12+m\sqrt6)/10$ for an odd integer $m$. This is a second obstruction valid from six states on. The kernel and its positivity are classical; applying them at the exclusion boundary is the deduction here, not a claim that the sources formulated the quantum result.

## 3. A five-state cyclic family attaining the sharp cap in the limit

Use the following positive real weights:
$$
a=(1-1/\sqrt2)/2,\quad D=1-a,\quad
b=(D+\sqrt{D^2-1/2})/2,\quad c=(D-\sqrt{D^2-1/2})/2 .
$$
Their sum is one; $aD=bc=1/8$. The radicals are real since $D> 1/\sqrt2$. As $0<c<b<D$, $c=1/(8b)>1/(8D)=a$. Also $b>1/2$: the quadratic $z^2-Dz+1/8$ is negative at $1/2$ since $D>3/4$. In particular $b>c>a>0$.

For a primitive fifth root of unity $\omega$, set $v_j=(\sqrt a,\sqrt b\,\omega^j,\sqrt c\,\omega^{-j})^T$, $0\le j<5$. For $z=\omega^{j-k}\ne1$ we have
$$
|a+bz+cz^{-1}|^2=a^2+b^2+c^2+a(b+c)(z+z^{-1})+bc(z^2+z^{-2}).
$$
Since $a(b+c)=bc=1/8$, $a^2+b^2+c^2=1-2(a(b+c)+bc)=1/2$, and the four nontrivial powers of $z$ sum to $-1$, the common squared overlap is $3/8$. The nonzero Gram eigenvalues are $5a,5b,5c$ by Fourier orthogonality. The purity identity implies $(b-a-c)^2=4ac$ by expansion; $b>1/2$ fixes the positive sign, hence $\sqrt b=\sqrt a+\sqrt c$.

Now shift the weights to $((1-\epsilon)a,(1-\epsilon)b+\epsilon,(1-\epsilon)c)$ with $0<\epsilon<1$. The middle square root is strictly greater than the sum of the other two. The Gram matrix remains circulant. By the necessary direction of JRS Theorem 5.1 for circulant Gram matrices this makes the new tuple non-antidistinguishable. Its largest squared overlap tends to $3/8$ as $\epsilon\downarrow0$ by continuity and finiteness. At the endpoint the unperturbed family *is* antidistinguishable; the perturbed families establish sharpness.

For a direct check of non-antidistinguishability, let $U=\operatorname{diag}(1,\omega,\omega^{-1})$. If any exclusion POVM existed for the $U^jv_0$ orbit, average its translates with corresponding cyclic label shifts; the resulting covariant POVM has effects $U^j M_0 U^{-j}$. They sum to $I$ and the diagonal of $M_0$ is $(1/5,1/5,1/5)$. Because $M_0v_0=0$, the sum of the three columns of $M_0^{1/2}$ weighted by the corresponding amplitudes is zero. Each column has norm $1/\sqrt5$. The triangle inequality requires the largest amplitude to be at most the sum of the other two, contrary to the chosen perturbation. This is the familiar cyclic state exclusion criterion in this instance, not a new criterion.

**Scope.** Ordinary one-copy exclusion with arbitrary POVMs, not identification of measurement devices, strong exclusion, a new eigenvalue criterion, tightness of the Frobenius bound, or the exact optimal cap once $n\ge6$. No priority claim for the geometry of qutrit lines or cyclic frames. No computation about samples or numerical SDP feasibility enters the proof.
