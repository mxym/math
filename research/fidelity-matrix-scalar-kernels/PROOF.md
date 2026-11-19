# Fidelity matrices: four full-rank qutrits defeat every power, and only trivial universal scalar kernels remain

Yongxian Zhang (张永贤). AI-assisted research draft, November 19, 2026. Internally reviewed, not externally peer reviewed. See [source boundaries](SOURCES.md); no historical-priority claim.

## Statements and conventions

For trace-one positive semidefinite matrices on a common finite-dimensional complex Hilbert space use
$$
 R(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1
 =\operatorname{tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho},\qquad F=R^2.
$$
A positive kernel means that all indicated finite real symmetric Gram matrices are positive **semidefinite**, not invertible. The symbol “power” below denotes the entrywise scalar power, not the operator power.

**Theorem A (power, fixed number of states).** For a prescribed real $\alpha>0$, the matrix $[F(\rho_i,\rho_j)^\alpha]_{i,j=1}^K$ is PSD for every list of $K$ states in every finite dimension exactly as follows:

| List size | Universal exponents |
|---|---|
| $K=1,2$ | all $\alpha>0$ |
| $K=3$ | $\alpha\ge 1/2$ |
| $K\ge4$ | none |

For every prescribed $\alpha>0$, four isospectral positive definite real rational $3\times3$ density matrices suffice to witness failure; for that exponent the four can be made arbitrarily close to each other. At $\alpha=1$, both 4 states and Hilbert-space dimension 3 are minimal. This does not assert dimension 3 is minimal for *all* exponents, or that a single list defeats unboundedly large exponents.

**Theorem B (universal scalar kernels).** Let $f:[0,1]\to\mathbb R$ take finite real values. Then $[f(R(\rho_i,\rho_j))]$ is PSD for every finite list of density matrices in every finite dimension if and only if there are real numbers $0\le c\le D$ such that $f(r)=c$ for $0\le r<1$ and $f(1)=D$. No continuity, measurability, monotonicity or a priori boundedness is assumed. The same description holds with $F$ in place of $R$ since $r\mapsto r^2$ is a bijection of $[0,1]$ fixing 1. In particular a continuous such scalar transform is constant. **Both** list size and dimension can grow in this latter proof. Kernels involving functions of the individual matrices other than their pairwise fidelity, e.g. $\operatorname{tr}(\sqrt\rho\sqrt\sigma)$, are not so constrained.

## A: a common orthogonal flag converts a qubit square into a strict violation

Write $Z=\left(\begin{smallmatrix}1&0\\0&-1\end{smallmatrix}\right)$ and $X=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$. In cyclic order set $U_i=Z,X,-Z,-X$. For rational $0<r<1$ put $Q_i=(I+rU_i)/2$. These are real trace-one matrices with eigenvalues $(1\pm r)/2$. For two qubit states, the eigenvalues of $\sqrt{Q_i}Q_j\sqrt{Q_i}$ give the elementary identity
$$
 R(Q_i,Q_j)^2=\operatorname{tr}(Q_iQ_j)+2\sqrt{\det Q_i\det Q_j}.
$$
The $x_{ij}=R(Q_i,Q_j)^2$ are therefore $1$ on the diagonal, $1-r^2/2$ for adjacent indices and $1-r^2$ for opposite ones. This matrix encodes the standard real two-basis qubit square; the pure-state two-MUB and sign-vector approach already occurs in Fannes et al.

Given $p=2\alpha>0$, choose rational $\epsilon=1/(1+\lceil p\rceil)$, so $0<\epsilon<1$ and $(p-1)\epsilon<1$. In $\mathbb R^2\oplus\mathbb R$ let
$$
 \rho_i=\epsilon Q_i\oplus(1-\epsilon).
$$
These are full rank and have the same spectrum. Square roots and trace norms respect orthogonal blocks, giving
$$
 R(\rho_i,\rho_j)=1-\epsilon+\epsilon\sqrt{x_{ij}}.
$$
Set $g(x)=(1-\epsilon+\epsilon\sqrt{x})^p$. For $0<x\le1$,
$$
 g''(x)=\frac{p\epsilon(1-\epsilon+\epsilon\sqrt{x})^{p-2}}{4x^{3/2}}
 \big((p-2)\epsilon\sqrt{x}-(1-\epsilon)\big)<0.
$$
For $p\le2$ the last bracket is negative; for $p>2$ it is at most $(p-1)\epsilon-1<0$. The sign vector $z=(1,-1,1,-1)^T$ is an eigenvector of the circulant matrix $[F^\alpha]$, with eigenvalue
$$
 g(1)+g(1-r^2)-2g(1-r^2/2)<0
$$
by strict concavity at the midpoint. Taking positive rational $r\downarrow0$ makes all four states converge to the same full-rank matrix. For $K>4$ append any distinct states and retain the bad principal submatrix. Multiplying entries by $\sqrt{p_i p_j}$ for positive ensemble weights merely gives a congruence and preserves failure.

In particular for the ordinary squared fidelity choose $\epsilon=1/2$, $r=4/5$ (this $\epsilon$ also meets the strict bracket requirement). Here $x_{\rm adj}=17/25$, $x_{\rm opp}=9/25$. Thus the adjacent and opposite *flagged* squared fidelities are $(21+5\sqrt{17})/50$ and $16/25$ respectively. The alternating eigenvalue is $(4-\sqrt{17})/5<0$. The 2-by-2 blocks of the four qutrit matrices are respectively $\operatorname{diag}(9,1)/20$, $\left(\begin{smallmatrix}5&4\\4&5\end{smallmatrix}\right)/20$, $\operatorname{diag}(1,9)/20$ and $\left(\begin{smallmatrix}5&-4\\-4&5\end{smallmatrix}\right)/20$; the third entry is always $1/2$.

For $K\le2$, use $0\le F\le1$ directly. For $K=3$, Fannes et al., Proposition 1 (journal numbering), prove that the three-state root-fidelity matrix is PSD. Its entries are nonnegative. The FitzGerald–Horn theorem on entrywise powers of entrywise nonnegative PSD matrices preserves positivity in size 3 whenever the power is at least 1. This gives all $2\alpha\ge1$, including equality. For necessity use three pure real qubit vectors $(1,0),(1,1)/\sqrt2,(0,1)$: the consecutive squared fidelities are $1/2$ and the remaining one is zero. The $[F^\alpha]$ matrix is the identity plus $2^{-\alpha}$ times the adjacency matrix of the three-vertex path; its smallest eigenvalue is $1-\sqrt2\,2^{-\alpha}$, strictly negative if $\alpha<1/2$. Finally, in qubit dimension
$$
 F(\rho,\sigma)=\operatorname{tr}(\rho\sigma)+2\sqrt{\det\rho\det\sigma}.
$$
This is a real Gram inner product in the direct sum of Hermitian matrices (Hilbert–Schmidt inner product) and one real coordinate. Dimension 1 is trivial. This explains the previously known all-qubit positivity of Fannes et al., Proposition 6, and establishes minimality at $\alpha=1$. Pure states in any dimension at $\alpha=1$ likewise give a Gram matrix of projectors (their Proposition 5).

## B: two sign tests force rigidity

The fidelity between pure vectors' projectors is the modulus of their inner product in the root convention. For orthogonally flagged direct sums, root fidelity adds termwise: $R(\bigoplus p_j\rho_j,\bigoplus q_j\sigma_j)=\sum_j\sqrt{p_jq_j}\,R(\rho_j,\sigma_j)$, with zero-weight blocks omitted. This follows by block functional calculus. In particular disjoint blocks give zero, and coincident pure flags of weight $a$ give $a$.

1. **Boundedness.** Put $D=f(1)\ge0$. Every $r\in[0,1]$ is a pure-qubit root overlap (take $e_1$ and $re_1+\sqrt{1-r^2}e_2$). The two-point test gives $|f(r)|\le D$.
2. **Monotonicity without regularity.** Fix $0\le a<b<1$. Use $2n$ diagonal states, in two groups of $n$. Every state places mass $a$ on the same flag, mass $b-a$ on its group's flag, and mass $1-b$ on a flag private to that state. All these flags are orthogonal except for the stated coincidences. Distinct within-group overlaps are $b$; all across-group overlaps are $a$. The vector with $n$ plus signs and then $n$ minus signs has quadratic form $2n[D+(n-1)f(b)-nf(a)]\ge0$. Divide the bracket by $n$ and let $n\to\infty$ to obtain $f(a)\le f(b)$.
3. **An upper bound for *every* short increment.** Fix $a<1$, $n\ge2$ and $0\le s\le1-a$. Use two mutually unbiased orthonormal bases in a common $n$-dimensional subspace (standard and Fourier). For each of their $2n$ vectors put mass $s$ on its rank-one projector, $a$ on a single common flag, and $1-a-s$ on a private flag. The flag spaces are orthogonal to each other and to the basis space. Distinct same-group root fidelities are $a$ and across-group root fidelities are $a+s/\sqrt n$. The same signed-vector test, now for these mixed states, gives
$$
  f(a+h)-f(a)\le (D-f(a))/n\le 2D/n
  \quad\text{for every }0\le h\le(1-a)/\sqrt n.
$$
No density, extension or continuity argument for $h$ is hidden here: use exactly $s=h\sqrt n$. The basis and sign test alone, with *no* flags, already underlie Fannes et al., Proposition 4; flags are what allow $a$ and $s$ to vary independently. Complex Fourier matrices for all $n$ may even be replaced by real Walsh matrices along an unbounded subsequence.
4. **Propagation.** For fixed $0\le a<b<1$ split $[a,b]$ into $m=\lceil(b-a)\sqrt n/(1-b)\rceil$ equal intervals. Each step has length at most $(1-b)/\sqrt n$, hence lies within the permitted range from each left endpoint. Summing the increments gives $f(b)-f(a)\le 2Dm/n\to0$. Combined with step 2 this proves $f\equiv c$ on $[0,1)$. The test on $n$ orthogonal pure states with all coefficients $+1$ gives $D+(n-1)c\ge0$ for all $n$, hence $c\ge0$; step 1 gives $c\le D$.
5. **Sufficiency and repetitions.** The standard equality $R(\rho,\sigma)=1$ iff $\rho=\sigma$ follows, for example, from its trace-norm unitary maximization and equality in Hilbert–Schmidt Cauchy–Schwarz for normalized square-root factors (or Uhlmann's purification formula). Consequently the transformed matrix is $c\mathbf1\mathbf1^T+(D-c)[\mathbf1_{\rho_i=\rho_j}]$. The last matrix is the Gram matrix of equality-class indicator vectors. Both summands are PSD, including for repeated states and $D=c=0$. This completes both directions.
