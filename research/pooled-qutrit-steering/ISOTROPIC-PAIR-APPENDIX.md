# Appendix: a second proof of the qutrit pair lemma

**Yongxian Zhang.** Independent argument for the [isotropic proof](ISOTROPIC.md). It is not needed for the main two-gap result. The torus regions and elementary unitary zero-pattern classification are prior (Führ–Rzeszotnik); the order-three Fourier classification is classical. See the [source discussion](ISOTROPIC-SOURCES.md).

**Pair lemma.** If every state unbiased to a basis $A$ has at most one probability strictly above $1/3$ in a second qutrit basis $B$, the two bases have a common ray.

Write $U=B^*A$; an $A$-flat state has $B$-coordinates $U(1,u,v)^T/\sqrt3$, up to phase, with $|u|=|v|=1$. Rephasings and permutations of rows and columns do not affect the hypothesis. A common ray is an entry of modulus one. We first establish that for each column $w$ whose entries are all nonzero, the other two columns $c,d$ satisfy $|c_i|=|d_i|$ for every row $i$. Permute columns to the order $(c,d,w)$. Put $a_i=\bar w_i c_i$, $b_i=\bar w_i d_i$. For fixed $u$, the three differences from the flat output level, after scaling by three, are real first harmonics in $v=e^{i\phi}$:
$$
 F_i(u,v)=|c_i+u d_i+v w_i|^2-1
       =2\Re(\bar c_i d_i u)+2\Re\{\bar v(a_i+u b_i)\}.
$$
Here each row of $U$ has unit norm; the sum of the three $F_i$'s is zero by unitarity. No two may be strictly positive.

Choose a row $i$ with $(c_i,d_i)\ne(0,0)$. There is $u_0$ for which $\Re(\bar c_i d_i u_0)=0$ and $c_i+u_0d_i\ne0$: if both entries are nonzero take the relative phase in quadrature; otherwise any phase works. Since $w_i\ne0$, on a nonempty open arc about $u_0$ this harmonic has oscillation strictly larger than the absolute value of its constant term. For each such $u$, it has two distinct sign-changing zeros on the $v$-circle. At either zero both other harmonics vanish: their sum is zero there, and if one were nonzero one of them would be strictly positive, still positive nearby on the side where $F_i>0$. This contradicts the hypothesis.

The real vector space spanned by $1,\cos\phi,\sin\phi$ has dimension three; prescribing zeros at two distinct circle points imposes two independent homogeneous conditions (the evaluation vectors start with 1 and the other two coordinates uniquely determine the point). All three harmonics are therefore real multiples of the same harmonic at this $u$. Their complex oscillation coefficients have the same phase up to a real sign. In the complex exterior square, with componentwise conjugation, this says
$$
 (a+u b)\wedge(\bar a+u^{-1}\bar b)=0.
$$
This Laurent polynomial in $u$ vanishes on an open arc, so its $u^1,u^0,u^{-1}$ coefficients all vanish. In particular $b\wedge\bar a=0$, i.e. $b=\lambda\bar a$ with $\lambda\ne0$. The constant coefficient is $a\wedge\bar a+b\wedge\bar b=(1-|\lambda|^2)a\wedge\bar a=0$. Since $a=\operatorname{diag}(\bar w)c$ and $b=\operatorname{diag}(\bar w)d$ are linearly independent (the diagonal matrix is invertible and $c,d$ are orthonormal), $a\wedge\bar a\ne0$. Thus $|\lambda|=1$; taking moduli proves the desired $|c_i|=|d_i|$.

Suppose now that $U$ has no entry of modulus one. No row or column can then have two zeros. Nor can two zeros occupy different rows and columns: if all rows have at most one zero, two such rows have exactly one common nonzero coordinate, contradicting their orthogonality. Thus at most one entry of $U$ vanishes. If there is exactly one, choose a dense pivot column $w$ different from the column of that zero. Equality of moduli in the remaining two columns would give two zeros in the exceptional row, a contradiction. If no entry vanishes, all three columns can be pivots, forcing all entries of $U$ to have modulus $1/\sqrt3$. Up to rephasing and permutations, the only such 3-by-3 unitary is the normalized Fourier matrix: set its first row and column to $1/\sqrt3$; orthogonality of each other row to the first forces the two remaining phases to be $\omega,\omega^2$ in one order, with $\omega=e^{2\pi i/3}$, and the two orders must differ. But the flat input $(1,1,-1)^T/\sqrt3$ for the Fourier matrix gives sorted output probabilities $(1,4,4)/9$, violating the hypothesis. This rules out the last case and proves the lemma.

