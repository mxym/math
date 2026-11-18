# Which triples attain the trine bound?

**Corollary.** Let $\rho_0,\rho_1,\rho_2$ be density matrices on a common finite-dimensional complex Hilbert space. With the equal-prior normalization of the [sharp bound](PROOF.md), $T-S=3\sqrt3/2-2$ if and only if, on the span of their supports and up to one common unitary, the three states have the form
$$
\rho_i=\pi_i\otimes\omega,\qquad i=0,1,2,
$$
where the $\pi_i$ are an ordered triple of pure qubit trine states and $\omega$ is the same density matrix for all three labels. Zero blocks outside this span do not matter. On the span one can and does take $\omega$ faithful.

[Weiner, Proposition 6.1 and Theorem A.1](https://arxiv.org/html/2609.17920v1) already characterized equality for qubits and for pure triples in any dimension. His [Appendix A.3, Eqs. (75)–(76)](https://arxiv.org/html/2609.17920v1#A1.SS3) proves that tensoring with a common ancilla or taking a flagged mixture of trines preserves the value. The point here is **necessity for arbitrary mixed triples**, as a corollary of the sharp-bound argument in [#85](https://github.com/mxym/math/pull/85). Rigidity at maximum violation of the ordinary chained Bell inequality is established in [Šupić, Augusiak, Salavrakos and Acín](https://arxiv.org/abs/1511.09220); the direct calculation below specializes that structure to the discrimination problem. It does not give a robustness estimate.

### Necessity

Let $H$ be the span of the three supports and use an optimal dual $Y\succeq\rho_i$, $S=\operatorname{Tr}Y$. Compression to $H$ and extension by zero preserve feasibility, so optimality gives $\operatorname{Tr}(Y|_{H^\perp})=0$ (compression understood). Positivity then forces the entire complement block and its cross terms to vanish. Conversely, a vector in $\ker Y$ is in every $\ker\rho_i$; thus $Y$ is invertible on $H$.

On $H$ write $\tau=Y/S$ and use its eigenbasis and canonical purification $\psi=\sum_j\sqrt{t_j}|j,j\rangle$. Put
$$
 A_i=(2Y^{-1/2}\rho_iY^{-1/2}-I)^{\mathsf T},\qquad
 B_i=\operatorname{sgn}(\rho_i-\rho_{i+1})
$$
with $+1$ on the kernel, and cyclic indices. The $A_i$ are Hermitian contractions and the $B_i$ Hermitian involutions. By [§3 of the bound proof](PROOF.md), the two strict slopes on either side of $S=2$ force $S=2$ at equality; then $T=3\sqrt3/2$ and $4T/S=3\sqrt3$.

Set $a_i=(A_i\otimes I)\psi$ and $b_i=(I\otimes B_i)\psi$. The discrimination reduction and direct-sum Cauchy–Schwarz give
$$
3\sqrt3=\operatorname{Re}\sum_i\langle a_i-a_{i+1},b_i\rangle
\le \sqrt3\left(3\sum_i\|a_i\|^2-\Big\|\sum_i a_i\Big\|^2\right)^{1/2}
\le 3\sqrt3 .
$$
Here all $\|b_i\|=1$; the parenthesis equals $\sum_i\|a_i-a_{i+1}\|^2$. Equality gives $\|a_i\|=1$ for each $i$, $\sum_i a_i=0$, and $a_i-a_{i+1}=\sqrt3 b_i$ for every $i$. Faithfulness of $\tau$ now gives $A_i^2=I$ from $\operatorname{Tr}\tau(I-A_i^2)=0$, and $\sum_i A_i=0$ since the corresponding operator on the first factor annihilates $\psi$.

For $D_i=A_i-A_{i+1}$, comparing coefficients of $|j,k\rangle$ in the last vector relation gives
$$
D_i\sqrt\tau=\sqrt3\sqrt\tau B_i^{\mathsf T},\qquad
\sqrt\tau D_i=\sqrt3 B_i^{\mathsf T}\sqrt\tau .
$$
The second equation is the adjoint of the first. Hence $D_i\tau=\tau D_i$. The commutators $[A_i,\tau]$ are consequently all equal, and sum to zero; each vanishes. Returning to the original state space, $E_i=A_i^{\mathsf T}$ still commute with $\tau$, which is real diagonal in the chosen basis. They are involutions and sum to zero.

Since $(E_i+E_j)^2=I$ for $i\ne j$, their pairwise anticommutators equal $-I$. Thus $P=E_0$ and $Q=(E_1-E_2)/\sqrt3$ are anticommuting Hermitian involutions. Let $K$ be the $+1$ eigenspace of $P$. The map $Q$ takes $K$ unitarily onto the $-1$ eigenspace. The identification $|0\rangle\otimes v\mapsto v$, $|1\rangle\otimes v\mapsto Qv$ realizes $P=\sigma_z\otimes I_K$ and $Q=\sigma_x\otimes I_K$. Commuting with $P$ makes $\tau$ block diagonal; commuting with $Q$ makes the two diagonal blocks identical. Thus $\tau=(I_2/2)\otimes\omega$ with $\operatorname{Tr}\omega=1$. Now $E_1=(-P+\sqrt3 Q)/2$ and $E_2=(-P-\sqrt3 Q)/2$, so $(I+E_i)/2=\pi_i\otimes I_K$ for the three pure qubit states at mutual Bloch angle $120^\circ$. Finally
$$
\rho_i=\sqrt Y\,(I+E_i)\sqrt Y/2=\tau(I+E_i)=\pi_i\otimes\omega .
$$

### Sufficiency

Each pair trace distance is $\sqrt3/2$ since tensoring with a state preserves the trace norm. The POVM $(2/3)\pi_i\otimes I_K$ and dual $I_2\otimes\omega$ both give $S=2$. These computations prove the converse. In a flagged direct sum of ordered trines, align the trine in each orthogonal block by its own unitary and put the common flag weights into $\omega$. Thus the earlier flagged examples are included, not excluded.

**Status:** AI-assisted derivation and independent internal mathematical review; not an external peer review or a formalization. No worldwide priority claim.
