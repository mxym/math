# Real Euclidean border ranks of the maximal Hankel obstruction and real jets

## Scope and sources

Jianze Li, https://arxiv.org/html/2611.13823v1, §2.3 (2.2), defines the real Hankel quartic H_* by (H_*)_{ijkl}=δ_{i+j+k+l,10} for 1-based indices in {1,2,3,4}. The paper claims real ordinary and symmetric **exact** ranks 10 and 11, respectively; these claims are not premises of the independent argument below. No real Euclidean border-rank claim is made there. https://arxiv.org/html/2610.24982v1 concerns complex border rank and direct sums; §1.2 credits Nie–Ye with single-tensor border equality in even order and a range of odd orders, and Holden with the all-orders complex result. See https://arxiv.org/abs/1706.03631 for Nie–Ye's generic exact-rank statement and broader even-order complex border theorem. Neither complex statement controls Euclidean closure over the reals. The Lovitz 27-variable cubic is a different tensor and the calculations here are independent of it.

Real symmetric rank throughout permits signed coefficients c v^{⊗2m}. The sign cannot be absorbed in a real even root. Without signs, the middle flattening is positive semidefinite and stays so under limits. In particular, H_* is not in the closure of any such unsigned decompositions: the antidiagonal submatrix below has three negative eigenvalues.

## Exact calculation: H_* and repeated sums

Write v(t)=(1,t,t²,t³). In zero-based indexing H_*=[t^6]v(t)^{⊗4}. The following curve consists of tensors of real symmetric rank at most seven for real ε≠0:

  A(ε) = (720 ε^6)^(-1) Σ_{j=0}^6 (-1)^(6-j) binom(6,j) v(jε)^{⊗4}.

For k<6 the sixth forward difference annihilates t^k, for k=6 it equals 6! ε^6, and after normalization all k>6 contributions tend to zero. Thus A(ε)→H_*. For the ordinary lower bound take the (12)|(34) matrix flattening. In each half choose (0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3), representing sums 0,...,6. The chosen 7×7 minor is precisely the reversal permutation matrix, determinant (-1)^21=-1. Matrix rank ≤r is closed and every tensor CP summand contributes matrix rank at most one. Therefore ordinary and signed symmetric real Euclidean border ranks both equal seven; the same proof gives complex ranks seven. For H_*^{⊕k}, use k block-supported copies of the same minor for a 7k minor and approximate each block separately, establishing both real and complex border ranks 7k.

## Real jet theorem

Let the order be 2m with m≥2, dimension n≥2, and D=m(n−1). Define H(L)_{i_1,…,i_{2m}}=L(t^{i_1+…+i_{2m}}) for L on real polynomials of degree ≤2D. Suppose L(f)=Σ_a Σ_{j=0}^{e_a-1} c_{a,j} f^{(j)}(t_a)/j!, with distinct real centers t_a, c_{a,e_a-1}≠0, and r=Σ_a e_a≤D+1. Then real ordinary and signed symmetric Euclidean border ranks equal r, as does real border rank restricting to Hankel Vandermonde approximants.

Upper bound: at each center approximate the jth normalized derivative by Δ_h^j/(j!h^j), using only the shared e_a nodes t_a+kh, k=0,…,e_a−1; the terms combine to at most e_a signed point evaluations. A point evaluation gives v(t)^{⊗2m} with v(t)=(1,t,…,t^{n−1}). Take h→0. Lower bound: choose one m-index tuple for each attainable sum i=0,…,D in both halves; the resulting middle flattening is the matrix of (p,q)↦L(pq). Evaluation of Taylor coefficients through all jets is surjective on degree ≤D by Hermite interpolation, equivalently the Chinese remainder theorem and r≤D+1. In these jet coordinates the bilinear form is block diagonal, each block indexed by 0≤i,j<e_a with entry c_{a,i+j}, interpreted as zero for i+j≥e_a. Reversing columns makes each block triangular with diagonal c_{a,e_a-1}≠0; hence the form has rank r. Projective supports can be moved away from infinity by a real PGL₂ change, whose action on the n homogeneous degree-(n−1) monomials is invertible.

For a single supported antidiagonal moment L=[t^s] with 0≤s≤2D, simultaneous reflection of all indices sends s to 2D−s. Reduce to s≤D and apply the theorem with a single jet of length s+1. Formula: min(s,2D−s)+1.

## Spectral converse in the shorter grouped-flattening range

Allow complex jet centers and coefficients, paired by conjugation so L is real; all top coefficients are nonzero. Put g(t)=∏_a (t−t_a)^{e_a}, a real polynomial of degree r. Suppose r≤(m−1)(n−1)+1. Then ordinary real Euclidean border rank equals the complex flattening bound r if and only if all zeros of g are real. This is also equivalent to real signed symmetric border rank being r. It is not a comparison of potentially larger ranks.

Proof: group the modes into blocks of sizes (m−1), m, and 1. In each larger block pick one coordinate for each sum 0,…,r−1. In the last block use coordinate 0 for B0=(L(t^{i+j})) and coordinate 1 for B1=(L(t^{i+j+1})). On C[t]/g the pairing L(pq) is nondegenerate by the same block argument over C, so B0 is invertible. If M represents multiplication by t on the quotient in the monomial basis, B1=M^T B0, giving B1 B0^(-1)=M^T with characteristic polynomial g. If H(L) were a Euclidean limit of real ordinary-rank ≤r tensors, the compressed B0,k would be invertible eventually. Each paired slice then admits B0,k=U_k diag(w0,k)V_k^T and B1,k=U_k diag(w1,k)V_k^T with r columns and invertible U_k,V_k, all w0,k nonzero. Hence B1,k B0,k^(-1) is conjugate over R to a real diagonal matrix. Passing to characteristic polynomials shows g is real-rooted, since the set of monic real-rooted polynomials of fixed degree is closed (e.g. roots uniformly bounded by a coefficient bound, then take a convergent sorted root list). The converse is the real jet theorem. The complex flattening bound equals r since the upper finite difference construction also works over C.

The certificate is elementary, so novelty has not been established; it is an audited family calculation, not a solution of universal real border Comon. The next material case is a conjugate-supported moment where both real ranks exceed the complex bound: determine whether they can differ, rather than treating the obstruction to the common lower bound as a gap.


## Intrinsic singular-middle theorem (extends the shorter pencil range)

For any nonzero real even-order Hankel tensor of order 2m≥4 and dimension n≥2 let D=m(n−1), and let C=(L(t^{i+j}))_{0≤i,j≤D} have rank r≤D. Then the following are equivalent:

1. Its real ordinary Euclidean border rank is r.
2. Its real signed symmetric Euclidean border rank is r.
3. Its real border rank by signed Vandermonde tensors is r.
4. The degree-r minimal homogeneous apolar polynomial of the generating functional L splits over R (multiplicities permitted).

If splitting fails, all three real border ranks are strictly larger than the common complex value r. No claim is made that the three enlarged real ranks agree.

### Intrinsic generator and jet representation

Homogenize L as a linear functional on S_{2D} where S=R[X,Y]. Define I_j={f in S_j : L(f S_{2D−j})=0}. Then I_D=ker C is nonzero. Choose a nonzero g in I_a of least degree a≤D. Suppose f in I_D is not divisible by g, and h=gcd(g,f) has degree c<a. The coprime binary forms g/h and f/h generate all homogeneous forms of degree k≥(a−c)+(D−c)−1. Indeed their two spaces of multiples intersect in multiples of their product, so dimensions total k+1 in that range. In degree k=2D−c the inequality holds, and multiplication by h shows h S_{2D−c}⊂g S_{2D−a}+f S_D. This gives h∈I_c, contradicting minimality. Therefore I_D=g S_{D−a} and rank C=a=r. The same gcd argument shows uniqueness of g up to scale, either directly in degree a or by canceling powers X^{D−a},Y^{D−a} in I_D. Choose a real projective change so all complex roots of g are finite; the induced linear transformation on our individual n-dimensional factors is invertible and real. Normalize the dehomogenized g to be monic. Apolarity implies that L vanishes on multiples of g of degree≤2D, so it factors through R[t]/g. A decomposition over C by the Chinese remainder theorem gives its expression as complex jets at the roots with conjugate-paired constants; all highest coefficients are nonzero, since otherwise deleting the top multiplicity at the root and its conjugate would give a lower-degree real annihilator. The balanced flattening image U is spanned over C by the jets of orders 0 through e_a−1 of v(t)^{⊗m} at each root, by nondegeneracy of the local jet pairings. In particular U is contained in the linear Hankel subspace K of (R^n)^{⊗m}. The real-jet finite difference result immediately proves (4)⇒(3)⇒(2)⇒(1).

### Real Segre contact obstruction: proof of (1)⇒(4)

Take any real ordinary-rank ≤r sequence H_k converging to H. For all sufficiently large k the balanced flattenings have exactly rank r: a nonzero r×r minor persists, and rank ≤r holds. Their column spans U_k tend to U, for instance by selecting the same stable independent columns giving bases. Each U_k is spanned by r real, linearly independent decomposable vectors: flattening a CP decomposition into r outer products gives these left factors and they must span dimension r.

The real projective decomposable points in K are precisely [v(t)^{⊗m}] for real projective t. Indeed a nonzero decomposable vector in the symmetric subspace has proportional factors (exchange any two modes, and contract all remaining modes nontrivially). For the common vector x in affine chart x_0=1, Hankel entries with the same sum force x_j=x_{j−1}x_1 for j≥2, giving x=(1,t,…,t^{n−1}). If x_0=0 and the least nonzero coordinate j satisfies j<n−1, compare tuples (j,j,j,…,j) and (j−1,j+1,j,…,j); the contradiction leaves only the endpoint at infinity. For any representative sum coordinates 0,…,D a polynomial p of degree≤D is the pullback of a linear functional ℓ_p on the entire ambient space to v(t)^{⊗m}. Restricted to U, ℓ_p vanishes exactly if its first e_a Taylor coefficients at every root vanish. Since deg g=r≤D, ℓ_g is available, and ℓ_{t^{D−r}g} also vanishes on U and evaluates nonzero at infinity by its nonzero degree-D coefficient. Hence the real projective decomposable points in U are precisely the finite real roots of g, with none at infinity.

Fix one such real root t_a of multiplicity e. Work in the product chart with x_{b,0}=1 for every mode b. Choose m(n−1)−1 linear equations vanishing on K whose Segre restrictions are:
- x_{b,j}−x_{1,j}=0 for b>1 and 1≤j≤n−1,
- x_{1,j}−x_{1,j−1}x_{2,1}=0 for 2≤j≤n−1.
The equations come from pairs of entry tuples of equal index sum. Their Jacobian in all coordinates except t=x_{1,1} is invertible: first solve the equality equations for modes b>1, then solve the remaining equations triangularly in increasing j. Also impose ℓ_g, which vanishes on U and restricts to g on the resulting curve. Perturb the coefficient vector of each selected linear equation by orthogonal projection onto U_k^⊥. The coefficients converge to the originals and the perturbed equations vanish on U_k. By the parameter-dependent implicit function theorem, the first m(n−1)−1 perturbed restrictions have as their local common zero set a graph over t, in a fixed neighborhood of the root. The restriction of the last perturbed equation to the graph converges in C^e on a sufficiently small closed t-interval to g(t); this follows from analytic dependence on graph parameters. Because g^(e)(t_a)≠0, the perturbed restriction has nonzero e-th derivative throughout a smaller interval for large k. Repeated Rolle implies at most e distinct roots there. Each root gives at most one decomposable projective point, by uniqueness in the graph.

Compactness of the real projective Segre implies that for all large k every decomposable point in U_k lies in the union of the chosen neighborhoods of the real roots, since every accumulation point lies in U. Thus the r distinct independent CP left factors force at least r real-root multiplicity in g. This can happen only when it splits over R. This is a rank-saturation result for the intrinsic middle catalecticant, not a universal real border-Comon theorem.

### Relevant earlier real binary work

Seigal–Sturmfels, Real Rank Two Geometry, https://arxiv.org/abs/1609.09245, characterize Euclidean ordinary and symmetric border rank ≤2; negative real hyperdeterminant already detects the conjugate pair exclusion at rank two. Comon–Ottaviani, https://arxiv.org/abs/0909.4865, and Blekherman–Sinn, https://staff.math.su.se/shapiro/ProblemSolving/BleckSinn.PDF, discuss hyperbolic binary forms having maximal real Waring rank. Ordinary border bounds of order d for strictly hyperbolic binary forms follow directly by border substitution and Rolle; do not ascribe novelty without checking ordinary and border parts separately. Real signed Vandermonde border on the Hankel locus corresponds to degree-2D binary apolarity under moment polarization; real Waring approximation in n variables and unrestricted ordinary CP approximation are not required to stay Hankel. The Segre contact argument is precisely what excludes those unrestricted approximations at the singular flattening bound.

### Optional check: real binary hyperbolic family

For a strictly hyperbolic binary degree-d form (d distinct projective real zeros), ordinary real Euclidean border rank is d. The upper bound is the classical signed real binary Waring bound d. For the ordinary lower bound induct on d. Given rank-≤r approximants choose in the last factor a unit real covector annihilating one nonzero summand (restrict to the 2D factors, then pass to a convergent subsequence). The contracted approximants have rank at most r−1 and converge to the contraction of the target by a unit covector. For a symmetric tensor this is, up to nonzero normalization, a directional derivative of its form. In coordinates making that direction the x direction, dehomogenize at y=1. If infinity is not a zero, the dehomogenized polynomial has d distinct finite real roots; its derivative has d−1 by Rolle. If infinity is a zero, the polynomial has degree d−1 with d−1 distinct finite real roots, and the derivative has d−2 such roots plus an infinity zero of multiplicity exactly one as a form of degree d−1. Thus the contracted target is again strictly hyperbolic and induction gives r≥d. This subsumes the conjugate-pair tensor Re(c v^⊗d) for c≠0 when the real and imaginary parts of v are independent: in its real two-dimensional span its form is up to a real linear change Re((x+iy)^d), with d distinct real zeros. Its complex ordinary and symmetric border ranks are both two by its displayed expression and one-vs-rest flattening. This is an ordinary and symmetric real rank increase over the complex ranks, not an ordinary/symmetric gap over the reals. For d=1 the pair's complex rank is of course one, so the rank-two statement is for d≥2.

## Three exact border-rank values on one quartic

Let \(v(t)=(1,t,t^2)\) and
\[
H=\operatorname{Re}(v(i)^{\otimes4})+\tfrac12v(0)^{\otimes4}.
\]
The complex ordinary and symmetric Euclidean border ranks are both **3**; the real ordinary and signed symmetric Euclidean border ranks are both **5**; the real signed Vandermonde Euclidean border rank is **8**. The real symmetric approximants need not be Hankel, whereas the Vandermonde approximants must be sums of real moment-curve powers. This example does not separate ordinary and symmetric border rank over the same field.

* **Complex, 3.** Expand the real part as two conjugate powers. The three vectors \(v(i),v(-i),v(0)\) are independent by the Vandermonde determinant, so in this basis the tensor is diagonal with three nonzero entries. A one-versus-three flattening therefore has rank three.
* **Real ordinary and signed symmetric, 5.** The basis \(\operatorname{Re}v(i),\operatorname{Im}v(i),v(0)\) displays a strictly hyperbolic binary quartic and a scalar block on an independent line. The real additive bound below gives the ordinary border lower bound five. A real signed Waring decomposition of the binary quartic has four terms, and the scalar adds one.
* **Real signed Vandermonde, 8.** The linear binary moment isomorphism of [Nie and Ye](https://arxiv.org/abs/1706.03631) sends Hankel moments \(h_j\) to \(\sum_{j=0}^8\binom8j h_jX^{8-j}Y^j\). It sends real Vandermonde powers to real binary powers projectively, including the point at infinity as a limit. Here the corresponding form is \(\operatorname{Re}(X+iY)^8+\tfrac12X^8\). At \((X,Y)=(\cos(j\pi/8),\sin(j\pi/8))\) its signs alternate, since the magnitude of the perturbation is at most \(1/2\). The eight consecutive open intervals on the real projective circle give eight distinct real zeros. The same signs persist in an open neighborhood, so the [strictly hyperbolic binary Waring rank theorem](https://arxiv.org/abs/0909.4865) gives real Waring rank eight throughout that neighborhood, including at the form itself. This proves both the Euclidean border lower bound and the projective upper bound. A summand at infinity, if present, can be approached using finite real slopes, since \(t^{-8}(X+tY)^8\) tends to \(Y^8\).

For an explicit decomposition in the last step, for \(q=4,8\) the Fourier expansion of \(\cos^q\) gives
\[
\operatorname{Re}(X+iY)^q
=\frac{2^{q-1}}q\sum_{j=0}^{q-1}(-1)^j
  \big(\cos(j\pi/q)X+\sin(j\pi/q)Y\big)^q .
\]
Indeed on the unit circle the weighted sum discards all the Fourier modes except the two of frequencies \(\pm q\); homogeneity extends the identity. For the octic the \(j=0\) coefficient absorbs the additional \(X^8/2\).

### Ordinary real Euclidean border rank with independent scalar blocks

In \(d\ge2\) modes take a strictly hyperbolic binary degree-\(k\) core, \(1\le k\le d\), on \(k\) active binary modes, tensored with a nonzero vector in each remaining mode. Form the direct sum with \(s\) nonzero scalar blocks, each on its own independent line in every mode. The real ordinary Euclidean border rank is \(k+s\).

The upper bound uses the real binary Waring bound \(k\) and the \(s\) scalar terms. For the lower bound induct on \(k+s\). At \(k=1\) a one-versus-rest flattening has rank \(1+s\). For \(k\ge2\) project the rank-\(\le r\) approximants into the stated mode spaces and choose a nonzero summand, with its factor in one active mode represented by a unit vector \(e_j\). After passing to a subsequence, \(e_j\to e\). If a fixed map \(P\) in the selected mode kills \(e\), then applying \(P(I-e_j e_j^\top)\) kills the selected summand and tends to applying \(P\). Thus the transformed target has border rank at most \(r-1\); no bounds on the coefficients of the approximants are needed.

* If \(e\) has a nonzero coordinate along a scalar block, let \(\alpha\) extract that coordinate and take \(P=I-e\alpha/\alpha(e)\). This is the identity on the binary core and on the other scalar blocks. In a second mode project off the chosen scalar line. This removes just that block, irrespective of how its first-mode factor changed. The resulting target has parameters \((k,s-1)\).
* Otherwise \(e\) is in the binary plane. In that plane take a rank-one map killing \(e\), and extend by the identity on the scalar lines. Acting on the binary core takes a nonzero directional derivative in its homogeneous binary form and supplies a fixed nonzero factor in the selected mode. Thus it becomes a degree-\(k-1\) core with one more inactive mode. The real projective Rolle argument above preserves strict hyperbolicity; the scalar blocks remain independent. The parameters are \((k-1,s)\).

In both cases induction gives \(r-1\ge k+s-1\). Notice that the approximants have been ordinary rank decompositions throughout; no symmetry or Hankel assumption was used for the lower bound.

### A family with the same separation

For even \(d\ge4\) and \(n\ge s+2\), now put \(v(t)=(1,t,\dots,t^{n-1})\). With \(z\notin\mathbb R\), distinct real \(a_j\), \(c\ne0\), and real \(b_j\ne0\), take
\[
 \operatorname{Re}(c\,v(z)^{\otimes d})+
       \sum_{j=1}^{s} b_j v(a_j)^{\otimes d}.
\]
The complex ordinary and symmetric border ranks equal \(2+s\), and the real ordinary and signed symmetric border ranks equal \(d+s\). The Vandermonde determinant on the \(s+2\) nodes gives the independent lines and plane needed in the real argument. The real signed Vandermonde border rank equals \(d(n-1)\) whenever all \(\lvert b_j\rvert\) are sufficiently small. Indeed the unperturbed binary form \(\operatorname{Re}(c(X+zY)^{d(n-1)})\) is an invertible real transform and scaling of a harmonic power, hence has distinct real projective zeros. The sufficiently small perturbations preserve that open property. These are exact values in the displayed family; publication priority for the family or the scalar-block argument is not asserted.
