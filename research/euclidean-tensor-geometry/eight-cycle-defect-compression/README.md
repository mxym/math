# A compressed defect-lifting construction for alternating eight-cycle quantum max-flow

**Yongxian Zhang.** AI-assisted research note with exact certificates.

In the periodic translation-invariant alternating eight-cycle model of [Gesmundo–Landsberg–Walter](https://arxiv.org/abs/1801.09106) over \(\mathbb C\), the exact ranks at common physical and bond dimensions 12, 15, and 18 are \(20736,50624,104976\), respectively. The checks operate on matrices of size at most \(6^4=1296\), rather than the final \(18^4\), by lifting a one-dimensional defect from the ternary model.

## Alternating flattening and symmetry

For an arbitrary integer matrix \(K\) of size \(q\), choose the shared slices \(A_i=e_iK_{i,*}\). The flattening indexed by words \(u,v\) of length four is \(M_K[u,v]=\prod_{j=0}^3K_{u_j,v_j}K_{v_j,u_{j+1}}\), with cyclic subscripts. In fact for every shared tensor (not just such slices), trace rotation gives \(M[u,v]=M[v,\rho u]\) where \(\rho\) is left rotation. If \(P e_u=e_{\rho u}\) then \(M^\mathsf T=MP\) and \(MP=PM\). The dimension of the \(-1\) eigenspace is \((q^4+q^2-2q)/4\), computed by the traces of \(P^0,\dots,P^3\). The pairing is skew-symmetric on this eigenspace, which is bilinear-orthogonal to all other eigenspaces and nondegenerate for the standard bilinear form. At \(q=15\) this dimension is \(12705\), odd, so \(\operatorname{rank}M\le50624\). At \(q=12,18\) simply use \(\operatorname{rank}M\le q^4\).

## Defect compression

Work modulo the prime 1009 for the certificate. Take
\[
 K_A=\begin{pmatrix}1&1&1\\1&2&3\\1&4&5\end{pmatrix},
 \qquad K_B[i,j]=(i+1)^j \quad(0\le i,j<s).
\]
Write \(M_A=M_{K_A}, M_B=M_{K_B}\). The checker gives \(\operatorname{rank}M_A=80\), a common left and right null vector \(h\) (the only free lexicographic coordinate is 79, normalized to 1), and \(h[\rho u]=-h[u]\). It verifies \(\operatorname{rank}M_B=s^4\) for the chosen sizes \(s=4,5,6\).

Now take dimension \(q=3s\) with pair labels \((a,x)\). Use a polynomial family of integer matrices
\[
 K(t)_{(a,x),(b,y)}
  =K_A[a,b]K_B[x,y]\big(1+t\,U[a,b]V[x,y]\big),
 \qquad U=E_{00}.
\]
The checker specifies \(V\) for each \(s\); every residue is represented by an integer. At \(t=0\) the alternating flattening is \(M_A\otimes M_B\) up to word-index ordering. Its left and right nullspaces have bases \(h\otimes e_u\).

Expand the eight edge factors to first order in \(t\), and pair with those bases. For a forward edge \(j\), its ternary contribution is \(\sum_{a,b}h[a]M_A[a,b]h[b]U[a_j,b_j]\), independent of \(j\) by simultaneous rotation of both words. Denote this value by \(c\). For the following edge \(U[b_j,a_{j+1}]\), the substitution \((a,b)\mapsto(b,\rho a)\) preserves \(M_A[a,b]\) and negates \(h[a]h[b]\). Thus its contribution is \(-c\). The checker evaluates \(c=9\pmod{1009}\). The first-order map from the kernel to the cokernel is consequently
\[
 D[u,v]=c M_B[u,v]\sum_{j=0}^3\big(V[u_j,v_j]-V[v_j,u_{j+1}]\big).
\]
Its rank is \(256,624,1296\) for \(s=4,5,6\), respectively. These numbers use exact modular Gaussian elimination. Multiplication by \(c\ne0\) does not change the check.

Choose constant row and column bases over \(\mathbb F_{1009}\) that put the kernels last and the invertible complementary block first at \(t=0\). The off-diagonal blocks vanish at \(t=0\), so the Schur complement has leading term \(tD\). A nonzero minor of \(D\) shows that over \(\mathbb F_{1009}(t)\) the full rank is at least \(80s^4+\operatorname{rank}D\). Thus some integer minor polynomial of the original, untransformed flattening is nonzero modulo 1009. It is nonzero over \(\mathbb C\), and a complex specialization attains the asserted bound. This reasoning does not require the original polynomial itself to specialize within a finite set of field elements.

## Consequences and reproduction

Full rank at 12 and 18 gives full rank at \(12a^2\) and \(18a^2\) for all positive integers \(a\), by taking tensor products with the known GLW square-dimension witnesses. Under the obvious index permutations the flattening of tensor-product slices is the Kronecker product of flattenings. Multiplying a deficient witness by another does not prove sharpness; the first-order compression is needed for the near-full \(q=15\) value here.

Run `python3 verify.py` with NumPy installed and assertions enabled. The result is not a formula for all dimensions.
