# Normal form and twisted special-point fusion

Companion to the [all-length rank theorem](README.md). Model: [Gesmundo–Landsberg–Walter](https://arxiv.org/abs/1801.09106); related [alternating spin-chain transfer](https://arxiv.org/abs/1408.1716) and [rational fusion](https://www.math.purdue.edu/~otsymbal/Papers/FKT.pdf). This supplement verifies the local fusion directly.

## 1. Move the deformation to one seam

For a generic local tensor its three slices span a hyperplane of matrices with annihilating linear form \(A\mapsto\operatorname{tr}(MA)\), for \(M\) with two distinct nonzero eigenvalues. A simultaneous similarity of all slices preserves the trace coefficients and diagonalizes \(M\). A physical basis change then lets us choose the three slices to span the hyperplane \(W=\langle |01\rangle,|10\rangle,|00\rangle+t|11\rangle\rangle\), with \(t\ne0\). The alternating map can be realized by including \(W^{\otimes s}\) on the even bonds of the \(2s\) virtual bits and then taking the quotient by the annihilator of \(W^{\otimes s}\) on the odd bonds, using the ordinary bilinear pairing. This latter annihilator is the sum of spaces with a factor on the line \(|00\rangle+\rho|11\rangle\), \(\rho=-1/t\), on at least one odd bond.

Change the virtual coordinates at sites \(2j\) and \(2j+1\) by \(\operatorname{diag}(1,\rho^{-2j})\) and \(\operatorname{diag}(1,\rho^{2j+1})\), respectively, for \(0\le j<s\). On each even bond the covector annihilating the transformed row space becomes \((1,1)\) in the \(00,11\) coordinates. On an ordinary odd bond the transformed forbidden vector line likewise becomes \((1,1)\); on the final bond it becomes \((1,x)\), \(x=\rho^{2s}\). Applying \(|0\rangle\mapsto|1\rangle,\ |1\rangle\mapsto-|0\rangle\) at every odd site turns the ordinary lines into singlets and identifies the even row space with the symmetric square on every bond. At the seam, the odd forbidden line is the ordinary singlet acted on by \(\operatorname{diag}(1,x)\) on the even bit. Thus the odd quotient can be realized by applying its inverse, proportional to \(D=\operatorname{diag}(x,1)\), to that bit before taking the ordinary symmetric quotient. Invertible scaling or basis changes do not affect rank.

Let \(S\) be the spin-one operators on the symmetric square, and \(\sigma\) the Pauli matrices on an auxiliary bit. Define \(L_a(u)=uI+\sigma_a\cdot S\) and
\[
T_D(u)=\operatorname{tr}_a\!\left(D_a L_{a,0}(u)\cdots L_{a,s-1}(u)\right).
\]
Regrouping the matching moves the first constituent of a symmetric pair into the outgoing auxiliary bit and replaces it with the incoming bit. In the transfer contraction this is the swap between the auxiliary bit and the first constituent, compressed to the symmetric square on the site. The swap of two bits equals \((I+\sigma_a\cdot\sigma_1)/2\); the site compression of \(\sigma_1\) is \(S\). Close the auxiliary trace with \(D\) at the seam. Thus the alternating map has the rank of \(T_D(1)\) (the paired input-output convention can transpose the matrix, and the common scalar \(2^{-s}\) does not matter). The statement can also be obtained by expanding the swap contraction on bit pairs.

## 2. Fuse the two auxiliary bits

For two auxiliary bits \(a,b\), the local product \(L_a(1)L_b(0)\) preserves their antisymmetric line and acts there by \(-2I\). On their symmetric square its compressed action is twice the swap of the symmetric auxiliary and physical spin-one spaces. Here is a direct check. In the site basis \(|00\rangle,|01\rangle+|10\rangle,|11\rangle\) with charges \(m=1,0,-1\), the operator \(L_a(u)\) on auxiliary bit \(b\) has:
- unchanged bit and site charge, coefficient \(u+(-1)^b m\);
- flipped bit \(b'=1-b\), output charge \(m+b'-b\) when in range, coefficient 2 if \(m=0\) and 1 otherwise.

Apply these rules at \(u=0\) on the second bit then \(u=1\) on the first bit. On \((|01\rangle-|10\rangle)\otimes |m\rangle\) the result is \(-2\) times the input. On the nine symmetric-square basis pairs with auxiliary and site charges \((k,m)\), add the two \(01,10\) coordinates and divide by two to read their symmetric output; this gives \(2|m\rangle\otimes |k\rangle\). Equivalently the compressed operator is \(2B^2+2B-2\), with \(B\) the spin scalar product on the two spin-one spaces. Its values on total spin \(2,1,0\) are \(2,-2,2\). Both individual \(L\)'s are self-adjoint in the orthonormal spin basis, so reversing the local product has the same diagonal blocks and the opposite block triangularity.

In the product of the two twisted auxiliary traces, \(L\)'s of distinct auxiliary bits on distinct sites commute, so group them site by site. Use the above triangular blocks and trace with \(D\otimes D\), which preserves the two auxiliary summands. The singlet contributes \((-2)^s\det D\), and the symmetric swap trace is \(2^s\) times the shift with twist \(\operatorname{Sym}^2D\) on the moved site. With the convention moving the first site to the last, this gives both orders:
\[
T_D(1)T_D(0)=T_D(0)T_D(1)=2^s\bigl(\mathrm{Shift}_{\operatorname{Sym}^2D}+(-1)^s xI\bigr).
\]
The transfers preserve the total charge \(Q\) and commute with the twisted shift, the latter by the identity itself. On charge \(Q\), the shift to the \(s\)-th power is \(x^{s+Q}\). For generic \(x\) the only possible zero product sector therefore has \(Q=0\) and shift eigenvalue \(\mu x\) with \(\mu=(-1)^{s+1}\). On the other shift eigenspaces both factors are invertible. On the exceptional eigenspace the ranks of the two factors sum to at most its dimension.

To translate back to the original rotation blocks, on charge zero the even row gauge weights a word of charges \(q_j\) by \(\rho^{2\sum j q_j}\) times a factor depending only on letter multiplicities. In fact the charged basis vectors after the odd-site transformation have multipliers \(-\rho^{2j+1}\) and \(\rho^{-2j}\), and the charge-zero vector has multiplier 1. Moving its first letter to the last changes the scale by \(x^{q_0}\) at total charge zero, exactly the factor of \(\mathrm{Shift}_{\operatorname{Sym}^2D}/x\). Hence the exceptional eigenvalue is the original rotation eigenvalue \(\mu\). An opposite shift convention yields \(\mu^{-1}=\mu\) and the same sector.

