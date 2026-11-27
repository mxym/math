# Which abelian integer rings have orthogonal canonical bases?

For a number field \(K\) let \(L_K\) be \(\mathcal O_K\) with its usual, unweighted canonical Euclidean metric, counting both members of every complex pair:
\[
B_K(x,y)=\sum_{\sigma:K\hookrightarrow\mathbb C}\sigma(x)\overline{\sigma(y)} .
\]
The sum is real and symmetric. Call a Euclidean lattice rectangular if it has an orthogonal integral basis, without requiring the basis vectors to have equal lengths.

**Theorem.** For a finite abelian extension \(K/\mathbb Q\), \(L_K\) is rectangular if and only if all of the following hold:

1. \(G=\operatorname{Gal}(K/\mathbb Q)\) is a \(2\)-group.
2. The prime \(2\) is totally ramified in \(K/\mathbb Q\).
3. Either \(G\) is cyclic, or \(K\) contains \(\mathbb Q(i)\).

When \(G\) is noncyclic and the first two conditions hold, \(G\cong C_2\times C_{2^r}\) for some \(r\ge1\). In this case failure of the third condition already gives a specific two-dimensional nonrectangular orthogonal summand, described below. Conditions 1 and 2 are also necessary for an arbitrary finite Galois extension of \(\mathbb Q\), without the abelian hypothesis.

This gives a criterion for independent integer coordinates for the centered spherical discrete Gaussian in the canonical metric of an abelian integer ring. In any integral basis with Gram matrix \(Q\), its mass is proportional to \(e^{-t z^{\mathsf T}Qz}\). Independence is equivalent to the vanishing of all off-diagonal entries, as can be checked by comparing the masses at \(0,e_i,e_j,e_i+e_j\). The theorem concerns the unweighted metric on the whole ring of integers.

## 1. Necessary conditions for a Galois field

On any rectangular lattice, an isometry permutes the primitive basis axes with signs, preserving their lengths. Indeed the shortest vectors are exactly the signed basis vectors of minimum length; split off their spans and use induction on the orthogonal complement. An isometry of a rectangular lattice fixing an axis and having odd order must have sign \(+1\) on that axis.

Put \(n=[K:\mathbb Q]\). For \(x\in\mathcal O_K\setminus\{0\}\), AM–GM gives \(B_K(x,x)\ge n|N_{K/\mathbb Q}(x)|^{2/n}\ge n\), and \(1\) attains \(n\). If \(L_K\) is rectangular, \(1\) is consequently one of its signed basis axes. The natural linear action of \(G\) on \(K\) has trace zero at every nonidentity element: after complexification it permutes the \(n\) embeddings freely. A nonidentity element of odd order, acting as a signed permutation of the rectangular axes, would have nonnegative contributions from all fixed axes and a strictly positive contribution from the fixed axis \(1\). This contradicts trace zero. By Cauchy's theorem \(G\) is a \(2\)-group.

The fixed sublattice of a rectangular lattice under a group of its isometries is again rectangular. Indeed, on each orbit of unoriented basis axes the integer vectors fixed by the signed action are either zero (an inconsistent sign) or all integer multiples of one signed sum. The signed sums of different orbits are mutually orthogonal. For any subgroup \(U\subset G\), the fixed lattice is the ring of integers of \(K^U\), with the usual canonical metric there multiplied by \([K:K^U]\). This scale follows because each embedding of the subfield has the same number of extensions to \(K\).

The quadratic field \(\mathbb Q(\sqrt d)\) for squarefree \(d\) is rectangular exactly when \(d\not\equiv1\bmod4\). In that case \(1,\sqrt d\) form an orthogonal integral basis in the canonical metric. If \(d\equiv1\bmod4\), the trace of \((1+\sqrt d)/2\) equals one; the orthogonal primitive axis \(1\) would require every \(B_K(x,1)=\operatorname{Tr}(x)\) to be a multiple of \(B_K(1,1)=2\), impossible. Equivalently every rectangular quadratic field has ramified prime \(2\). If the inertia subgroup at a chosen prime above \(2\) in \(K\) were proper, it would lie in an index-two subgroup of the finite \(2\)-group \(G\). Its quadratic fixed field would have unramified prime \(2\), a contradiction. This proves 1 and 2 in general.

## 2. Reducing the abelian metric to a dyadic field and a conductor operator

Assume \(G\) is abelian, a \(2\)-group, and \(I_2=G\). By Kronecker–Weber take \(K\) in a cyclotomic extension with conductor dividing \(2^a M\), \(M\) odd and squarefree. The squarefree choice is possible because the kernel of reduction modulo \(p\) on the odd prime-power unit group is a \(p\)-group, with trivial image in \(G\). The dyadic cyclotomic factor contributes exactly the inertia at \(2\) in the product (the odd factor is unramified there). Hence restriction from the dyadic group surjects onto \(G\). Let \(F\) be the dyadic subfield obtained by quotienting by its kernel, and identify \(\operatorname{Gal}(F/\mathbb Q)\) with \(G\). Let \(T\) be the odd squarefree-conductor subfield obtained by the corresponding restriction on the odd factor, so its Galois group is identified with the image \(H\subseteq G\). In additive notation the fixed subgroup for \(K\) in \(F T\) is precisely
\[
J=\{(-u,u):u\in H\}\subset G\times H .
\]

The fields \(F,T\) are independent subfields of coprime cyclotomic factors. Multiplication identifies \(\mathcal O_F\otimes_{\mathbb Z}\mathcal O_T\) with \(\mathcal O_{FT}\), with the tensor-product canonical pairing. One way to see integrality is first to do it for the full two coprime cyclotomic fields, where the product of their rings is the full ring of integers generated by the coprime roots, and then take the independent kernel invariants. Taking invariants in one factor commutes with tensoring with the other factor's free integral basis. The canonical pairing factors by the product of the embedding sets.

The odd field \(T\) has an explicit normal integral basis \(u\theta\), \(u\in H\), with
\(\theta=\operatorname{Tr}_{\mathbb Q(\zeta_M)/T}(\zeta_M)\).
Indeed for each prime \(p\mid M\) the nonidentity \(p\)-th roots give an integral basis: the only missing ordinary power-basis generator is supplied by the sum of all \(p\)-th roots being zero. The coprime product gives the normal integral basis of \(\mathbb Q(\zeta_M)\), permuted regularly by its group. Summing over kernel orbits gives the invariant basis for \(T\).

Using this odd basis, the map
\[
x\longmapsto v(x)=\sum_{u\in H}(-u)(x)\otimes u(\theta)
\tag{1}
\]
is an integral bijection from \(\mathcal O_F\) onto \(\mathcal O_{FT}^J=\mathcal O_K\), because the coefficient at \(u=0\) determines the other coefficients of any invariant. Define \(r(u)=B_T(\theta,u(\theta))\). Expanding the pairing in the tensor product, grouping by the difference of the two odd group elements and dividing by \([FT:K]=|H|\) gives
\[
B_K(v(x),v(y))=B_F(Cx,y),\qquad C=\sum_{u\in H}r(u)\,u\in \mathbb Q[G].
\tag{2}
\]
The G-action in \(C\) is the dyadic action on \(F\). On a complex character \(\chi\) of \(G\) this operator has eigenvalue
\[
\lambda_\chi=\sum_{u\in H}\chi(u)r(u)
 = \left|\sum_{u\in H}\chi(u)u(\theta)\right|^2
 = f_{\mathrm{odd}}(\chi),
\tag{3}
\]
where \(f_{\mathrm{odd}}(\chi)\) is the product of odd primes at which the character induced from the odd cyclotomic factor is nontrivial. For the middle identity use the fixed embeddings of the periods into \(\mathbb C\); expansion of the squared modulus and summation over one index gives the trace pairing in \(r\). For the final identity expand the period, obtaining the Gauss sum of the pulled-back character with additive root of unity \(\zeta_M\). Split this by the Chinese remainder theorem. At an odd prime the trivial factor contributes squared modulus \(1\), since the sum of all nonidentity roots equals \(-1\). A nontrivial factor contributes squared modulus \(p\), by expanding the square and substituting \(x=uy\): the inner sum over \(y\ne0\) is \(p-1\) for \(u=1\), \(-1\) otherwise. Multiplication by a unit in the additive argument from the CRT does not affect the modulus. These computations also handle \(M=1\). In particular (3) is constant on the rational conjugates of any character, since they have the same kernels on the odd inertia factors.

The standard dyadic cyclotomic lattice itself is rectangular: for \(\mathbb Q(\zeta_{2^a})\), the usual power basis is orthogonal of equal lengths via the trace. Every subfield inherits rectangularness from the signed-permutation invariant argument of Section 1. Therefore \(L_F\) has an orthogonal basis and \(G\) acts by signed permutations on it.

## 3. Cyclic dyadic quotient

If \(G\) is cyclic of power-of-two order, take a generator \(g\) and split its action into orbits on the rectangular axes of \(F\). On an orbit of length \(\ell\) the characteristic polynomial is \(X^\ell-\varepsilon\), where \(\varepsilon\in\{+1,-1\}\) is the product of the signs around the cycle. The axis \(1\) is a singleton of positive sign. Any other positive-sign orbit would add a nonzero independent fixed vector, whereas \(F^G=\mathbb Q\) is one-dimensional. Every other orbit therefore has negative sign and \(\ell\) a power of two: its polynomial is \(X^\ell+1=\Phi_{2\ell}(X)\), irreducible over \(\mathbb Q\).

Thus each such orbit carries one rational character packet, on which (3) is a scalar. The operator \(C\) scales the metric on each orbit and introduces no mixed terms between axes. Equations (1) and (2) therefore give a rectangular integral basis of \(K\). This includes the trivial and quadratic field cases.

## 4. Noncyclic dyadic quotient and the smallest mixed block

The dyadic unit group modulo \(2^a\), for \(a\ge3\), is generated by \(-1\) of order \(2\) and \(5\) of order \(2^{a-2}\), and is their direct product. Its noncyclic quotient \(G\) must thus be \(C_2\times C_{2^r}\), where the image \(\tau\) of \(5\) has order \(2^r\) and the image \(\omega\) of \(-1\) is an independent involution. The kernel on the full dyadic group is then generated by \(5^{2^r}\), so \(F=\mathbb Q(\zeta_{2^{r+2}})\). An integral orthogonal basis of \(F\) is the dyadic power basis; let \(n=2^{r+1}\) be its rank and the common squared basis length.

There are singleton axes \(1,i\). For each \(3\le k\le r+2\), the other axes of exact root order \(2^k\) form an integral summand \(W_k\) of rank \(2^{k-2}\), and the \(W_k\)'s are preserved by both \(\omega\) and \(\tau\). Each basis axis in \(W_k\) is a primitive odd exponent modulo \(2^{k-1}\), with signs interpreted modulo \(2^k\); \(\omega\) pairs the exponents by \(x\mapsto-x\), with no fixed axis. Multiplication of the exponents by \(5\) gives one cycle on each residue class modulo four among these odd exponents. Their common length is \(\ell=2^{k-3}\), since \(5\) generates the units congruent to \(1\bmod4\) modulo \(2^{k-1}\). Each cycle has negative return sign, since \(5^\ell\equiv1+2^{k-1}\bmod2^k\). Thus on each of the two \(\omega\)-eigenspaces in \(W_k\), \(\tau\) has characteristic polynomial \(\Phi_{2\ell}\): projection from one of the cycles to that eigenspace is an isomorphism intertwining its \(\tau\)-action.

For fixed \(k\) these two rational character packets have \(\chi(\omega)=+1,-1\), respectively, and primitive \(\chi(\tau)\) of order \(2^{k-2}\). By (3) let \(f_{k,+},f_{k,-}\) denote their two odd conductors; these are constant within each packet. Therefore on \(W_k\), \(C=a_k I+b_k\omega\) with \(a_k=(f_{k,+}+f_{k,-})/2,\ b_k=(f_{k,+}-f_{k,-})/2\). This is an orthogonal sum, in the marked integral power basis and the metric of (2), of independent two-axis blocks with Gram matrices
\[
n\begin{pmatrix}a_k&\pm b_k\\ \pm b_k&a_k\end{pmatrix}.
\tag{4}
\]
The sign depends on the chosen axis orientations. The singleton axes give independent one-dimensional blocks.

An orthogonal integral summand of a rectangular lattice must be rectangular: its orthogonal projection preserves the full lattice, and for each orthogonal basis vector \(e\) the coefficient of \(e\) in its projection \(Pe\) equals \(\|Pe\|^2/\|e\|^2\in[0,1]\). This is an integer, so \(Pe\) is \(0\) or \(e\). The two-axis lattice in (4) is rectangular exactly if \(b_k=0\). To prove the nontrivial direction, swapping the two basis vectors is an isometry. In a rectangular basis with unequal axis lengths, every isometry preserves each axis, so the primitive vectors \(e_1+e_2,e_1-e_2\) of the two swap-eigenlines would need to form a basis. They have index two. In a square lattice, any equal-length pair that is an integral basis has orthogonal columns: after scaling to the unit square their squared length \(a\) and inner product \(b\) are integers with \(a^2-b^2=1\) by the determinant of the basis. Then \(a=1,b=0\). This proves the claim.

It remains to identify when \(f_{k,+}=f_{k,-}\) for all \(k\). If the odd image \(H\) is contained in \(\langle\tau\rangle\), the two corresponding characters agree on all odd inertia groups, so equality holds throughout. Otherwise at some odd prime \(p\mid M\) a generator of its cyclic inertia image is \(g_p=\omega\tau^j\). Consider just \(k=3\), whose two characters have \(\chi(\tau)=-1\) and opposite values on \(\omega\). Exactly one is nontrivial on \(g_p\). Thus \(p\) divides exactly one of \(f_{3,+},f_{3,-}\), forcing a nonzero \(b_3\). The odd image is therefore admissible exactly when \(H\subseteq\langle\tau\rangle\).

Finally \(i\in F\), and \(\tau\) fixes \(i\) while \(\omega\) negates it. Since \(K=(FT)^J\), \(i\) belongs to \(K\) exactly when all of \(H\) fixes \(i\) under the \(F\)-action, that is, when \(H\subseteq\langle\tau\rangle\). This proves 3 and the theorem. For instance \(\mathbb Q(\sqrt2,\sqrt3)\) has all three quadratic subfields ramified at \(2\), hence \(2\) totally ramified, but the degree-four field itself is not rectangular because it is noncyclic and does not contain \(i\). The condition does allow other noncyclic fields with odd ramification, for example \(\mathbb Q(i,\sqrt6)\), whose three quadratic subfields all ramify at \(2\).

Independence here does not mean that the coordinates have identical laws. In fact a scaled cubic \(L_K\), where all these axis lengths are equal, is possible only for the full \(2\)-power cyclotomic fields (including the degree-one case). To see this, a minimum-length integral basis would consist of roots of unity by equality in AM–GM and Kronecker's theorem. Hence roots of unity generate the field, an observation related to [Fukshansky and Petersen's well-roundedness criterion](https://arxiv.org/abs/1101.4442). Once the field is cyclotomic, total ramification of \(2\) excludes any odd conductor factor. Conversely the standard dyadic power basis has equal lengths.

## Context

[Bolaños and Mantilla-Soler, *The Trace Form over Cyclic Number Fields*](https://arxiv.org/abs/1904.10080) compute equivariant trace Gram data in the tame cyclic case. [Zhang, *Integral Trace Forms of Cyclic Number Fields without Tameness*](https://arxiv.org/abs/2610.29876), especially §§4–7, uses dyadic characters and period resolvents to compare integral trace forms \( \operatorname{Tr}(xy)\), and more generally compares abelian trace forms via character conductors and parity. The equivariance also makes that comparison relevant to the positive canonical metric in the abelian setting. Here the issue is existence of an orthogonal integral basis, rather than isometry of two trace forms: the separate odd-conductor operator on a dyadic invariant lattice gives a cyclic criterion and an explicit noncyclic obstruction. The power-basis orthogonality of the full dyadic field and the Gauss-sum identities are standard. [Tran, Le and Tran, *Well-Rounded Ideal Lattices of Cyclic Cubic and Quartic Fields*](https://arxiv.org/abs/2303.16968) also constructs orthogonal examples using selected nontrivial ideals, a condition distinct from requiring this property of the whole integer ring.

This is a classification of unweighted Euclidean integer-ring geometry in the stated field family. It does not apply as written to a general ideal, a twisted metric, wrapped noise, or the behavior or security of a concrete algorithm.

Replay with `node verify-abelian-canonical-orthogonal.js`. The last run passed 142,352 exact checks, including direct Ramanujan-sum traces of the invariant basis, conductor-eigenvalue products, and the binary Gram blocks across generated dyadic and odd quotient data.
