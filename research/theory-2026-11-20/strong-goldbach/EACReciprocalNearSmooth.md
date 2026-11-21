# Reciprocal terminal signatures cannot recur at near-smooth centers

Fix a finite set of primes \(F\). A sequence of even centers is near-smooth if \(N\to\infty\) and \(N_F=N^{1-o(1)}\). Use the genuine all-composite terminal factorization equations
\[
 N-x_i=\prod_j x_j^{A_{ij}},\qquad B=I-A,
\]
where the \(x_i\) are distinct odd unit primes at most \(N/3\). The nonnegative integral matrix \(A\) is irreducible and loopless, and all row sums are at least two. Support is *reciprocal* when \(A_{ij}>0\) if and only if \(A_{ji}>0\); the two multiplicities need not be equal.

**Theorem.** No fixed reciprocal terminal signature, of any finite size and arbitrary fixed multiplicities, can occur on an unbounded near-smooth sequence. No label is required to be prescribed or polynomially large. Equivalently for each fixed reciprocal signature and \(F\) there is a positive constant \(\epsilon\) such that all sufficiently large realizing centers satisfy \(N/N_F\ge N^\epsilon\) (a compactness consequence, not an explicit exponent). With a fixed size cap, any near-smooth sequence of reciprocal terminals would consequently require unbounded row multiplicities and a subpolynomial minimum. This does not exclude growing signatures, directed supports in general, or Goldbach exceptions.

We prove also a curve criterion: at corank one of \(B\), a fixed signature, not necessarily reciprocal, is impossible on any near-smooth sequence of physical points lying on a fixed irreducible algebraic curve. Unlike the [finite-torus criterion](EACFiniteTorusNearSmooth.md), this argument needs no special-fiber transversality or multiplicity bound; the curve hypothesis must instead be independently secured.

## 1. Why a reciprocal physical realization lies on a curve

The undirected reciprocal support is a tree: a largest label \(u\) on any simple undirected cycle would have two distinct smaller parents, whereas every smaller parent must equal the remainder of \(N\) modulo \(u\). The support is connected by definition. Consequently there is a positive rational diagonal \(\Delta\) such that \(\Delta A\) is symmetric: along each tree edge prescribe \(\Delta_j/\Delta_i=A_{ij}/A_{ji}\).

Recall the [bounded-terminal path lemma](EACFiniteTorusNearSmooth.md): on a near-smooth sequence of all-composite terminals of bounded size, no label can have bounded order in \((\mathbb Z/N)^\times/\{\pm1\}\). This has no assumption on exponents or the minimum label. In particular \(\ker_{\mathbb Q} B\) is not contained in any coordinate hyperplane: if all kernel vectors had zero \(i\)-th coordinate, an integer multiple of \(e_i\) would be in the integral row lattice of the **fixed** \(B\), giving bounded order via the actual unit-residue equations. This also excludes zero nullity. A finite union of proper subspaces cannot cover a vector space over \(\mathbb Q\), so choose a right one-eigenvector \(v\) of \(A\) nonzero everywhere.

For any other right one-eigenvector \(u\), assign to an oriented edge \(ij\) the number \(\Delta_i A_{ij}(u_i v_j-v_i u_j)\). The numbers are antisymmetric by detailed balance and their sum at each vertex is zero by the two eigenvector equations. A divergence-free flow on a finite tree is zero (remove leaves in turn). Hence \(u_i/v_i\) is the same at all vertices and \(\operatorname{nullity}B=1\).

At this point every label must tend to infinity: a bounded coordinate along a subsequence would yield a fixed odd unit prime in a bounded factor-closed set with composite complements. The [fixed-and-moving seed theorem](PrimeOrbitMovingSeed.md) then gives nullity at least two, since \(N_F\ge N^{3/4}\) eventually. Because each vertex occurs in a product containing at least two factors, \(\max x_i/N\le1/\min x_i\to0\). This does not assert a fixed power gap.

The Jacobian of the equations in the \(x\)-coordinates differs by invertible row and column scalings from
\[
 A + E,\qquad E=\operatorname{diag}(x_i/(N-x_i)).
\]
It is similar to the real symmetric matrix \(A_0+E\) with \(A_0=\Delta^{1/2}A\Delta^{-1/2}\). The positive diagonal \(E\) tends to zero in operator norm. For the fixed \(A_0\), its nonzero eigenvalues therefore keep their signs for large realizations; each original zero eigenvalue moves strictly above zero, by the minimum-eigenvalue inequality for the positive definite perturbation. Thus the physical Jacobian is nonsingular. In the \(k+1\) variables \((x_1,\ldots,x_k,N)\) the solution variety is locally a smooth curve there. There are finitely many geometric components, and infinitely many of these rational tuples would be dense in one geometric curve defined over \(\mathbb Q\). This supplies the curve criterion's hypothesis without presuming nonsingularity of \(A\) or a finite augmented torus.

## 2. The differential pencil excludes every corank-one curve branch

Suppose that an unbounded near-smooth sequence of a fixed corank-one \(B\) lies on a fixed irreducible physical curve. The integral-curve argument of [the finite-torus theorem, §2](EACFiniteTorusNearSmooth.md) uses only this curve hypothesis once it is established. In detail: Siegel gives genus zero and at most two places at infinity; in the two-puncture case a parameter whose divisor is their difference is a unit with bounded finite valuations in a fixed field of degree at most two, and the number-field Subspace Theorem rules out a power-sized \(N_F\) for its nonconstant Laurent polynomial \(N\). With one puncture all coordinates are rational polynomials in a bounded-denominator parameter. The nearest-root Subspace Theorem makes \(N\) a polynomial with one distinct root. Rescale and translate to \(N=C T^D\), with \(C\) a positive \(D\)-th-power-free integer and \(T\) integral at the actual points. The Gauss-norm and constant-term arguments of the same proof now give distinct primitive irreducible \(P_i\in\mathbb Z[T]\), of positive degrees \(d_i<D\), with positive leading coefficients, \(P_i(0)=\sigma_i\in\{\pm1\}\), and \(x_i=P_i(T)\). Positivity of all degrees uses exactly the fixed-seed/nullity contradiction above; a further factor in every row then gives \(d_i<D\). None of this requires a bound on \(D\).

Modulo \(T^D\), formal logarithms of the signed unit-normalized factor equations give \(B\log(P_i/\sigma_i)=0\). Consequently for a primitive integral generator \(v\) of \(\ker B\) there is a single formal unit \(U(0)=1\) such that \(P_i/\sigma_i=U^{v_i}\bmod T^D\). The \(v_i\) are nonzero and pairwise different: otherwise the corresponding polynomials would be constant or two sign-normalized polynomials would coincide, the latter forcing actual equality by positive leading coefficients. Differentiation gives, for any distinct \(i,j\),
\[
 \frac{P_i'}{v_iP_i}-\frac{P_j'}{v_jP_j}=O(T^{D-1})\quad(T\to0).
\]
After putting over \(P_iP_j\), the numerator is a polynomial of degree at most \(d_i+d_j-1\). It is nonzero, since proportional logarithmic derivatives of distinct irreducible polynomials in characteristic zero are impossible (consider a simple root of one).

Order the degrees \(d_1\le d_2\le\cdots\). The row of vertex 1 has at least two factors, neither vertex 1, forcing \(2d_2\le D\). The preceding numerator for 1 and 2 has vanishing order at least \(D-1\), hence \(d_1+d_2\ge D\). Thus \(d_1=d_2=D/2=m\). Every degree is at least \(m\) and every vertex occurs with another factor in some degree-\(D\) row, so **all degrees equal \(m\)** and all row sums are exactly two.

Write the numerator for the pair \(i,j\) as \(c_{ij}T^{2m-1}\), \(c_{ij}\ne0\). Adding the three derivative differences around \(i,j,h\) gives identically
\[
 c_{ij}P_h+c_{jh}P_i+c_{hi}P_j=0.
\]
There are at least three vertices: a one-eigenvector for an irreducible matrix with zero diagonal and row sums at least two has both signs, each supporting a cycle of length at least two. Fixing \(i,j\) in this triple relation shows the span of all \(P_h\) has dimension at most two.

Let \(r=\operatorname{ord}_0(U-1)\le m\). If \(2r<2m\), the coefficients of \(1,T^r,T^{2r}\) in \(U^a\) are polynomials in \(a\) of respective degrees zero, one and two, with nonzero leading coefficients. At three different \(v_i\) they give a rank-three Vandermonde evaluation matrix. The congruences modulo \(T^{2m}\), unaffected in rank by the signs \(\sigma_i\), contradict the dimension-two span. Therefore \(r=m\) and \(P_i=l_i T^m+\sigma_i\) with positive \(l_i\).

Every row has two children, counting multiplicity. At least one constant is negative since each \(-\sigma_i\) is the product of its two child signs. In a negative-constant row the child signs must coincide; if both were positive the product's coefficient at \(T^m\) would be positive while that of \(CT^{2m}-P_i\) is negative. Thus the negative-sign set is forward closed, and strong connectivity forces all signs negative. The same coefficient comparison now gives \(l_i=l_j+l_h\) for all rows, impossible at the smallest \(l_i\). This proves the curve criterion and the reciprocal theorem.

The reciprocal geometry and earlier all-height restrictions of limited or homogeneous multiplicity are separate; the argument here is for fixed signatures on near-smooth sequences and uses no bound such as five on the actual row multiplicities.