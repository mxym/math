# Twisted cyclic complex and non-light-like deformations

This uses the [untwisted cyclic reduction](UNTWISTED.md) and the same Cartesian spin-one supercharge. Here coupling parameters follow Hagendorf §4.1, and the boundary twist is π in the first two sections.

## 1. Twisted reduction

Let \(D=\operatorname{diag}(-1,1)\), \(A=M_2(\mathbb C)=\mathbb CI\oplus V\), \(V=\mathfrak{sl}_2\), and \(\theta(a)=D^{-1}aD\). Work in the invariant subspace \(A^{\otimes(n+1),\theta^{\otimes(n+1)}}\). Rotate last to first applying \(\theta\) to the moved factor; let \(t_n\) be this rotation multiplied by \((-1)^n\). Its \((n+1)\)-st power is the identity on invariants. The Hochschild faces are the usual ones except the last face
\[
d_n(a_0,\ldots,a_n)=(\theta(a_n)a_0,a_1,\ldots,a_{n-1}).
\]
With the usual insertion-of-unit degeneracies, this is the standard cyclic object obtained by taking the invariants of the \(\theta\)-paracyclic module. See [Hadfield and Krähmer, §4.1](https://arxiv.org/abs/0711.4102). Use the quotient by \(1-t_n\) with differential \(b=\sum_i(-1)^i d_i\) to compute its cyclic homology.

The chain map \(G\) sending \((a_0,\ldots,a_n)\) to the scalar \(\operatorname{tr}(D a_0\cdots a_n)\) is a morphism to the scalar cyclic object: each ordinary face leaves the product unchanged, the twisted face works by ordinary cyclic trace, and unit insertions leave the product unchanged. Explicitly,
\[
\operatorname{tr}(D\theta(a_n)a_0\cdots a_{n-1})
=\operatorname{tr}(a_n D a_0\cdots a_{n-1})
=\operatorname{tr}(D a_0\cdots a_n).
\]
This also checks equivariance for the cyclic rotation. On the underlying Hochschild chains, the operation \(a_0\mapsto D a_0\) untwists the last face, is invertible, and preserves \(\theta\)-invariants. Averaging over the order-two diagonal action commutes with the ordinary Hochschild differential. The ordinary matrix algebra has Hochschild homology \(\mathbb C\) in degree zero, detected by trace, and zero above zero by separability (or Hochschild Morita invariance). Conjugation acts trivially on trace classes. Thus \(G\) induces an isomorphism on the underlying Hochschild homology. The natural [Connes SBI sequence for cyclic objects, Proposition 9.6.11](https://math.mit.edu/~hrm/palestine/weibel/09-hochschild_and_cyclic_homology.pdf) then gives an isomorphism on cyclic homology in every degree by induction. In particular this cyclic homology is one dimensional in even degrees and zero in odd degrees.

The subcomplex \(K\) spanned by chains containing a scalar factor is quasi-isomorphic to its all-scalar subcomplex via the same gap proof as at trivial twist. To be explicit, in the associated graded by \(r>0\) traceless letters, mark the first such letter, giving blocks \(v_i I^{k_i}\) with positive total gap length. Moving a terminal block to the beginning applies \(\theta\) to its \(v_i\) and the usual Koszul sign for its length crossing all other blocks. On the \(\theta^{\otimes r}\)-invariants this operator has order dividing \(r\). The last Hochschild face agrees with the ordinary final gap shortened because its moving factor is a scalar; a last gap of length zero supplies no face preserving \(r\). Hence the gap differential and elementary acyclicity work unchanged. Invariants and coinvariants of the indicated finite actions are exact by averaging, so every positive-\(r\) associated graded piece remains acyclic. This proof works also when \(r=1\).

The cyclic map induced by the scalar inclusion into \(A\) vanishes on homology: composing with \(G\), already a cyclic homology isomorphism, on all-scalar words gives the factor \(\operatorname{tr}D=0\). The long exact sequence of the cyclic quotient by \(K\) now gives one class in each degree: it comes from even \(HC_n^\theta(A)\) for even \(n\), and from even \(HC_{n-1}(\mathbb CI)\) for odd \(n\). Every class lies at zero charge. Indeed the constructions commute with conjugation by the diagonal spin torus, the target of \(G\) and all scalar chains are charge zero, and the long exact sequence decomposes into weights.

## 2. Dynamical ground states

Identify the cyclic quotient by \(K\) with signed twisted cyclic coinvariants on \(V^{\otimes s}\), \(s=n+1\), realized orthogonally as the \(\mu_s=(-1)^{s+1}\) eigenspace of the twisted shift on \(\theta^{\otimes s}\)-invariants. A weight \(Q\) in that invariant subspace is even. The adjoint of the boundary is the spin-one dynamical supercharge, up to nonzero length-dependent normalization: multiplication projected to \(V\) is the cross product and the twisted last-face merge is the extra boundary insertion in Hagendorf's construction upon taking the adjoint. The adjoint twist is the same involution. More explicitly the normalized supercharge is \(\sqrt{s(s+1)}\) times first-site splitting between the orthogonal projectors, just as without twist: simultaneous rotations of input and output multiply by the opposite signs and all \(s+1\) signed cyclic summands contribute equally. Thus the Hodge Laplacian \(H_s=Q_s^\dagger Q_s+Q_{s-1}Q_{s-1}^\dagger\) has exactly one zero vector up to scale in the signed even-charge sector, and it is neutral. The density is \(3I+P-2|g\rangle\langle g|\), with the crossing-boundary copy twisted, by Hagendorf equations (8),(9). This establishes the π-twist half of Conjecture 4.2 at the same isotropic point as the trivial-twist half.

## 3. All non-light-like Hagendorf coupling parameters

This section concerns only the spin-chain singlet count, not transfer ranks away from the isotropic point. In Hagendorf §4.1.1 the magnetic basis is \(|0\rangle,|1\rangle,|2\rangle\) and
\[
\psi_0=|10\rangle-|01\rangle,\quad
\psi_1=|20\rangle-|02\rangle,\quad
\psi_2=|21\rangle-|12\rangle,\quad
q(x,y)=(x\psi_0-y\psi_2,\ \psi_1,\ x\psi_2-y\psi_0)
\]
with the three columns indexed by \(|0\rangle,|1\rangle,|2\rangle\). Thus \(q(x,y)=q(1,0)A\), with \(A\) acting by \(xI-y\) times the exchange on the two extreme-weight basis vectors, and by 1 on the middle vector. More explicitly, use the standard spherical basis
\[
|0\rangle=-(e_1+ie_2)/\sqrt2,\qquad
|1\rangle=e_3,\qquad
|2\rangle=(e_1-ie_2)/\sqrt2.
\]
It follows that \(e_1=(|2\rangle-|0\rangle)/\sqrt2\), \(e_2=i(|0\rangle+|2\rangle)/\sqrt2\), and \(A=\operatorname{diag}(x+y,x-y,1)\) in Cartesian coordinates. The identification \(q(1,0)=-i q_{\mathrm{Cart}}\) follows from \(\psi_1=-i(e_1\otimes e_2-e_2\otimes e_1)\) and the common \(SU(2)\) equivariance (or by evaluating all three columns).

Suppose \(x^2\ne y^2\), so the three diagonal entries \(\lambda_i\) of \(A\) are nonzero, and put \(\Delta=\lambda_1\lambda_2\lambda_3\). Choose \(g=\operatorname{diag}(a_1,a_2,a_3)\) with \(a_i^2=\Delta/\lambda_i\), changing one square-root sign if necessary so that \(a_1a_2a_3=\Delta\); this is possible over \(\mathbb C\) because the squared product is \(\Delta^2\). The cross-product formula gives
\[
(g\otimes g)q(1,0)g^{-1}(e_i)
=\frac{a_ja_k}{a_i}\,q(1,0)(e_i)
=\lambda_i q(1,0)(e_i)
=q(x,y)(e_i),
\quad \{i,j,k\}=\{1,2,3\}.
\]
The map \(g\) commutes with both the unit twist and \(\theta=\operatorname{diag}(-1,-1,1)\). Consequently \(g^{\otimes s}\) commutes with the appropriate cyclic shift and carries the global isotropic complex to the deformed one, since each local insertion conjugates as above and the seam insertion is defined by translations. This chain isomorphism proves that for every real \(x,y\) with \(x^2\ne y^2\), the no-twist signed sector has no supersymmetry singlets and the π-twisted signed even-magnetization sector has exactly one. At \(y\ne0\) the chain does not generally preserve individual magnetization, so the latter class is asserted in the even sector rather than in the neutral weight. The conjugacy is not generally unitary and makes no assertion about the nonzero Hamiltonian spectrum or the full spectral exchange Conjecture 4.1.
