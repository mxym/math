# Strict dimension growth for the Schatten inequality for sums of matrix moduli
Research draft. This analytic argument has received a [separate internal AI-assisted review](REVIEW.md), not external peer review or formal verification. For antecedents and scope see [PRIOR.md](PRIOR.md).

For integers m,n≥1, let
$$
c_p(m,n)=\max_{A_1,\dots,A_m\in M_n(\mathbb C),\, B\ne0}
      \|\sum_i A_i\|_p/\|B\|_p,\qquad B=\sum_i |A_i|,\quad |A|=(A^*A)^{1/2}.
$$
Write $c_p(m)=\sup_n c_p(m,n)$. Normalize $\|B\|_p=1$: since $0\le |A_i|\le B$, eigenvalue monotonicity gives $\|A_i\|_p\le1$. The normalized set is nonempty, closed and bounded in finite dimension, so the indicated maximum exists. The constants are ≤m by the triangle inequality, ≥1 by a single nonzero summand, and nondecreasing in n by zero padding.

**Theorem.** For $m\ge2$, $1<p<2$ and every $n\ge1$,
$$
c_p(m,n)<c_p(m,n+1).
$$
Thus no finite dimension attains the universal constant. In particular, dimensions $m+1$ already suffice to beat the largest quotient of m matrices of rank at most one in any finite dimension. The two-matrix consequence uses matrices of size 3. This determines neither the universal constant nor the exact finite-dimensional constants, excludes no infinite-dimensional extremizer, and does not give a single numerical tuple simultaneously valid for all p.

## Proof

Use both input and output Hilbert spaces, without identifying their bases. Write $S=\sum_i A_i$, $H_i=|A_i|$, $E=\operatorname{ran}B$, $r=\dim E$; each $A_i$ vanishes on $E^\perp=\bigcap_i\ker H_i$. At a normalized extremizer, $S\ne0$.

**A. Folding a rectangular competitor back to its input dimension.**
For any maps $T_i:\mathbb C^n\to\mathcal K$ to a finite-dimensional output space, set $T=\sum T_i$. Let P project onto $\operatorname{ran}T$ and let J embed this range isometrically into $\mathbb C^n$; this is possible because $\operatorname{rank}T\le n$. The n-by-n maps $A'_i=JPT_i$ have $\|\sum A'_i\|_p=\|T\|_p$ and
$$
|A'_i|=(T_i^*PT_i)^{1/2}\le(T_i^*T_i)^{1/2}=|T_i|
$$
by operator monotonicity of square root. Their denominator therefore does not increase by eigenvalue monotonicity; it is nonzero if $T\ne0$.

**B. Rank of a fixed-size maximizing sum.**
If $(A_i)$ attains $c_p(m,n)$ then $\operatorname{rank}S=r$. Indeed $D=\sum_i A_i^*A_i$ is positive definite on $E$ (its kernel is $E^\perp$); write $D|_E\ge dI_E$, $d>0$. For $0<s<1$ define $T_i v$ with a common first output $\sqrt{1-s}\,A_i v$ and its own (mutually orthogonal) output $\sqrt{s}\,A_i v$, all other outputs zero. Then $|T_i|=H_i$ and
$$
T^*T=(1-s)S^*S+sD.
$$
If $k=\operatorname{rank}S<r$, on $E$ the latter dominates $(1-s)S^*S+sdI_E$. Eigenvalue comparison gives, with $\beta=p/2<1$,
$$
\|T\|_p^p\ge (1-s)^\beta \|S\|_p^p+(r-k)(sd)^\beta>\|S\|_p^p
$$
for all sufficiently small positive $s$; the loss is $O(s)$ and the gain a positive multiple of $s^\beta$. Lemma A would yield a strictly better competitor of size n, contradiction.

**C. What a flat pair of adjacent dimensions would force.**
Suppose $c_p(m,n)=c_p(m,n+1)=C$. Every n-dimensional maximizer also maximizes after adjoining one zero input/output coordinate. Let $W=U_S |S|^{p-1}/\|S\|_p^{p-1}$ with $S=U_S|S|$ its polar decomposition, using zero on the kernel. This has Schatten conjugate norm one, $\operatorname{ReTr}(W^*S)=\|S\|_p$; by B its rank on $E$ is r and it vanishes on $E^\perp$.

First, $W(\operatorname{ran} H_i)\subseteq\operatorname{ran} A_i$. Extend each polar factor of $A_i$ to a unitary $U_i$ so $A_i=U_iH_i$. Replacing $U_i$ by any other unitary preserves the denominator. The linear functional $\operatorname{ReTr}(W^* \sum U_iH_i)$ therefore cannot be increased at the maximizing tuple (duality for the numerator). For the i-th term the maximum over a unitary is $\|H_iW^*\|_1$, by polar decomposition. Equality forces $M=U_iH_iW^*$ positive semidefinite: if $M=V|M|$, equality $\operatorname{ReTr}M=\operatorname{Tr}|M|$ requires $\operatorname{Re}\langle x,Vx\rangle=1$ for every unit eigenvector $x$ of $|M|$ of positive eigenvalue, hence $Vx=x$. In particular,
$$
\operatorname{ran}(W H_i)=\operatorname{ran}(W H_i U_i^*)=\operatorname{ran}M^*=\operatorname{ran}M\ \subseteq\ \operatorname{ran}A_i.
$$

Next, $W(E\cap\ker H_i)\subseteq\operatorname{ran}A_i$. For a unit vector $v$ in this intersection take any unit $y\perp\operatorname{ran}A_i$ in the original output. Vacuous zero-dimensional cases obey the assertion. Rotate $y$ by a phase so that $\operatorname{ReTr}(W^*y v^*)=|\langle y,Wv\rangle|$. Adjoin a new orthogonal unit input $e$ in the additional dimension, pad square matrices and $W$ by zero, and put $w=a v+\sqrt{1-a^2}e$, $0<a<1$. For $t>0$ change only $A_i$ to $A_i+t y w^*$. Since $A_i^*y=0$ and $H_iw=0$, exactly
$$
|A_i+t y w^*|=H_i+t ww^*.
$$
Compare the old norming functional with the upper bound in dimension $n+1$:
$$
C\|B\|_p+t a|\langle y,Wv\rangle|\le \big\|S+t yw^*\big\|_p\le C\big\|B+tww^*\big\|_p.
$$
For $p>1$ the directional derivative of the right-hand norm at $t=0$ is $\operatorname{Tr}(B^{p-1}ww^*)/\|B\|_p^{p-1}=a^2\langle v,B^{p-1}v\rangle/\|B\|_p^{p-1}$. For completeness this derivative follows by taking $f(x)=|x|^p$ in $d\,\operatorname{Tr} f(B+tK)/dt|_{t=0}=\operatorname{Tr} f'(B)K$. For polynomials this is cyclicity of trace; general $C^1$ functions follow by uniformly approximating their derivative by polynomials on a compact interval containing both spectra and integrating the polynomials. Indeed eigenvalue Lipschitz continuity $|\lambda_j(B+tK)-\lambda_j(B)|\le |t|\|K\|_\infty$ bounds the error in each difference quotient by $\|K\|_\infty$ times the derivative approximation error. The scalar chain rule for the positive $p$-th root then gives the displayed derivative even for singular B.

Divide by $ta$, first take $t\downarrow0$ at fixed $a$, then $a\downarrow0$. Thus $\langle y,Wv\rangle=0$ for every such $y$, proving the assertion. The two inclusions cover $E=\operatorname{ran} H_i\oplus (E\cap\ker H_i)$; hence $\operatorname{ran}A_i$ contains $W(E)$ of dimension r. Conversely its rank is at most r. Thus **every summand of every n-dimensional maximizer must have rank r**, i.e. all $H_i|_E$ must be positive definite.

**D. An incompatible maximizing decomposition.**
Keep an n-dimensional maximizer and its $U_i,W,B$. For positive $K_i$ supported on E with $\sum K_i=B$, set $\Phi(K)=\operatorname{ReTr}(W^*\sum_i U_iK_i)$. Since $|U_iK_i|=K_i$,
$$
\Phi(K)\le \|\sum_i U_iK_i\|_p\le C\|B\|_p=\Phi(H).
$$
The maximizing point H is in the relative interior by C. More explicitly take $K=(B,0,\ldots,0)$; $H-\delta(K-H)$ is also admissible for sufficiently small $\delta>0$ because every $H_i|_E$ is strictly positive, while $K-H$ is supported on E and its components sum to zero. By linearity $\Phi(K)<\Phi(H)$ would make this opposite perturbation larger than $\Phi(H)$. Thus $\Phi(K)=\Phi(H)$ and $(U_1 B,0,\ldots,0)$ is another n-dimensional maximizer. Since $m\ge2$ and $r>0$, this contradicts C for its zero summand. The assumed equality of adjacent dimensions is impossible.

**Rank-one consequence.** For $A_i=u_i v_i^*$, all initial vectors span a space of dimension at most m and all output vectors span a space of dimension at most m. Using independent isometries of these two spaces into $\mathbb C^m$ gives m-by-m matrices preserving the singular values of their sum and of the sum of their moduli (up to zeros). Therefore every rank-one quotient is at most $c_p(m,m)$, whereas some m-tuple of size $m+1$ attains $c_p(m,m+1)>c_p(m,m)$. No external rank-one optimality theorem is needed.

