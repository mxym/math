# Nonsplit and bounded-exponent distance upper bounds

This is a supplement to the already archived [split-elementary Fourier-cube proof](https://github.com/mxym/math/blob/b9ca8e3573888ffc25cae820bf0545f6efcb1dda/research/split-quasi-abelian-distance-collapse/PROOF.md). We restate that argument only to make its two extensions (torsion cosets and trace descent) self-contained. The split-elementary theorem, its c/0105 refutation, and the split quotient lift are prior to this supplement.

## 1. Model and Fourier convention

Let F=F_q, let G be a finite abelian group of order N, and write R=F[G]. Identify its elements with coefficient functions x:G→F in the standard group basis; multiplication is convolution (xy)(g)=Σ_a x(a)y(g−a). A quasi-G code C of index ell is any R-submodule of R^ell, viewed as an F-linear code of length ell N with Hamming weight equal to the sum of the coefficient Hamming weights. Its rate is dim_F(C)/(ell N), and its relative minimum distance is Δ(C)=d_min(C)/(ell N). The systematic ensemble of rank k, 1≤k<ell, is the row span of (I_k | A) over R, with independent uniform entries of A in R. It has rate exactly k/ell.

When the group exponent E is coprime to the characteristic, choose a finite extension K=F_Q of F that contains the E-th roots of unity. The character group D=Hom(G,K*) has N elements, written additively so that χ_(b+w)=χ_b χ_w. We use

    xhat(w)=Σ_g x(g) χ_w(g),
    x(g)=N^(-1) Σ_w xhat(w) χ_(-w)(g).                     (1)

Indeed, the sum over G of a nontrivial character is zero: translate the sum by an element on which the character is not one. The trivial sum is N, invertible in K. This proves (1) by orthogonality (and the N distinct characters follow by decomposing the finite abelian group into cyclic factors). Convolution becomes pointwise multiplication. Thus (1) identifies K[G] with K^D as K-algebras. Fourier coordinates are not the coordinates in which distance is measured.

## 2. Deterministic result

**Theorem 1.** Let C be a quasi-G code of rate at least ρ>0, and suppose the exponent E of G is coprime to q. Fix a prime r dividing E, and let m be the dimension of the elementary r-torsion subgroup D[r] over F_r. Put M=(Q^ell−1)/(Q−1) and B=max{1,log₂(M/ρ)}. If 1≤d≤m and

    2^d B < (m−d) log₂ r,                                 (2)

then Δ(C) ≤ (1−1/r)^d. Consequently, for fixed q,E,ell,ρ, as |G| grows through groups of exponent dividing E, Δ(C)→0. More specifically, for G=(Z/2)^m over any odd F_q,

    Δ(C) ≤ min{1, 8 max{1,log₂(((q^ell−1)/(q−1))/ρ)}/m}       (m≥1).     (3)

For (I_k | A) over this binary group, (3) can replace its right-hand side by min{1,(ell−k+1)·8(ell−k)log₂(q)/(ell m)}.

**Cube lemma.** In a subset A of an F_r-affine m-space having density α, choose independent uniform variables x and h_1,…,h_d over that space and its underlying vector space respectively. The probability that all x+Σ_i ε_i h_i (ε_i∈{0,1}) belong to A is at least α^(2^d). Directions here are sampled independently as random variables; they need not yet be linearly independent. To prove the bound, for a nonnegative real f let T_d(f) be the arithmetic mean over (x,h_1,…,h_d) of the product of f at the corners. T_0(f)=E f. For d≥1 the product gives T_d(f)=E_h T_(d−1)(f(x)f(x+h)). By induction and Jensen this is at least

    E_h (E_x f(x)f(x+h))^(2^(d−1))
       ≥ ((E_x f(x))²)^(2^(d−1)) = (E f)^(2^d).

The probability of linearly dependent directions is at most Σ_(i=0)^(d−1) r^(i−m) < r^(d−m), by revealing each direction and counting its predecessors' span. Thus an actual independent cube exists if α^(2^d)>r^(d−m).

**Proof of Theorem 1.** Extend scalars to C_K=K⊗_F C inside K[G]^ell. Its K-dimension is the F-dimension of C, e.g., by extending a basis of C to an ambient F-basis. It is a K[G]-submodule. Under (1) it is a direct product of K-linear constituents L_w≤K^ell: the multiplier that is 1 at a given w and 0 elsewhere isolates that w's component. Since Σ_w dim L_w≥ρ ell N, at least ρN of the L_w are nonzero. Pick one line from each nonzero L_w. Some common line occurs on at least ρN/M frequencies; fix a nonzero vector v on that line. In one coset of D[r] its density is at least ρ/M, by averaging over cosets.

By (2) and the cube lemma this class contains a cube b+{Σ ε_i h_i} with h_i linearly independent over F_r. In coefficient space define

    u(g)=χ_(-b)(g) ∏_(i=1)^d (1−χ_(-h_i)(g)).             (4)

All 2^d corners are distinct. Expanding the product and using (1) shows that uhat is supported precisely on those corners, there equal to N(-1)^(Σε_i), including in characteristic two (N is nonzero). The ℓ-block vector (v_1u,…,v_ell u) belongs to C_K, since at the corners its frequency vector is a scalar multiple of v∈L_w, and it vanishes elsewhere. The map g↦(χ_(h_i)(g))_i from G to (μ_r)^d is onto: its image is an F_r-subspace, and a nonzero linear functional annihilating a proper image would give a nontrivial linear dependence between the h_i. Hence all fibers have the same size N/r^d, and the product in (4) is nonzero at exactly N(1−1/r)^d points.

If K=F we already have a nonzero codeword. Otherwise take a nonzero coefficient a of (v_j u)_j and choose γ∈K such that Tr_(K/F)(γ a)≠0. Such γ exists: the trace map is represented by the nonzero polynomial Σ_(i=0)^(s−1)X^(q^i) of degree less than q^s, where s=[K:F], and multiplication by a is bijective. Applying this trace coefficientwise to γ(v_j u)_j gives an element of C, as seen by writing the input as a K-linear combination of an F-basis of C. It is nonzero and the trace introduces no nonzeros outside the original coefficient supports. This proves the distance bound.

For fixed q,E choose one Q that splits all groups of exponent dividing E. If |G|→∞, at least one of the ranks m_r grows in maximum across the finitely many primes r dividing E: the r-primary group with rank m_r has order at most r^(m_r v_r(E)). For each large such rank m, d=floor(log₂(m log₂ r/(4B))) satisfies (2) eventually, since d=O(log m), and (1−1/r)^d tends to zero uniformly over those finitely many primes. For r=2, Q=q, and m>8B, the same d has 1≤d≤m/4 and 2^d>m/(8B), giving (3). Indeed B≥1 by definition, and log₂(m/4)≤m/4 for the m>8B branch. If m≤8B the bound Δ≤1 is enough.

**Baseline check: the prior split systematic specialization.** For G=(Z/2)^m, set h=ell−k and color the binary character group by the vector of h Fourier values of the first row entries a_1,…,a_h of A. A color has density at least q^(−h). With B'=h log₂ q it contains the affine subspace b+W of dimension d above, since in the binary case the cube is the whole subspace translate. Write H=W^⊥. The alternative coefficient representative

    u_b(g)=χ_b(g) 1_H(g)

has wt(u_b)=|H|=N/2^d, and uhat_b(w)=Σ_(g∈H)χ_(w+b)(g) equals |H| exactly on b+W and is zero elsewhere, by character orthogonality and −b=b. If a_j's transform has constant value λ_j on the cube, (1) gives u_b a_j=λ_j u_b. Taking input (u_b,0,…,0) in the systematic generator therefore gives weight at most (h+1)N/2^d. This gives the sharper constant for m>8B'. For m≤8B' the same conclusion with the claimed min follows from the always valid bound d_min≤(h+1)N (any nonzero first-block input produces one systematic and at most h parity blocks).

This recovers the prior negative conclusion for all fixed odd q, ell and k in the binary group; it is not a new refutation. The bound permits q to vary: in this particular systematic case it is O(h log₂ q/m), so it does not force deterioration in the concrete large-field regime where log₂ q is comparable to or much larger than m.

## 3. Uniform systematic ensemble: independent quotient bands

**Theorem 2.** Let F=F_q, let r be any prime different from the characteristic, and suppose the finite abelian group G has a quotient V≅(Z/r)^m. For independent uniform A in the systematic ensemble above, put h=ell−k. For 1≤d≤m/2,

    Pr[Δ(C)>2/(ell r^d)] ≤ (1−q^(−h(r^d−1)))^(r^(m−d)).  (5)

Consequently for fixed q,r,k,ell and m→∞, Δ(C)=O(1/m) with probability at least 1−exp(−r^(m/2)) for all sufficiently large m. This conclusion also holds for q even and a nonsplit elementary quotient.

We first prove (5) for G=V. Choose K=F_(q^s), with s the multiplicative order of q modulo r, and a primitive r-th root ζ in K. For w,g∈F_r^m use χ_w(g)=ζ^(w·g). An F-valued x has xhat(qw)=xhat(w)^q. Every such compatible collection is the transform of an F-valued x: take the inverse transform in (1), then the q-th power of each inverse coefficient is itself by reindexing via w↦qw. At zero the value lies in F; each nonzero orbit of multiplication by q has length exactly s, since q^j w=w with w≠0 is equivalent to q^j≡1 mod r. The transform therefore identifies F[V] bijectively with F times one copy of K per nonzero orbit. The corresponding coordinates of a uniform element are independent uniform field elements. In particular the nonzero part of a d-dimensional F_r-subspace W is a union of (r^d−1)/s orbits.

There are r^(m−d) d-dimensional subspaces W in the dual having pairwise intersection {0}. For a direct construction decompose the dual vector space as U⊕L with dimensions d,m−d, identify L with F_(r^(m−d)), and fix an injective F_r-linear map i:U→L. For each λ∈L take W_λ={(u,λ i(u)):u∈U}. Equality in two graphs with λ≠λ' forces u=0, and all W_λ are distinct since d≥1.

For each such W, require that the transforms of all h first-row parity entries vanish at every nonzero member of W. This event has probability (q^s)^(−h(r^d−1)/s)=q^(−h(r^d−1)). The events are mutually independent: the orbit coordinate sets are disjoint, and none contains 0. Let H=W^⊥, and choose x_0∉H. The nonzero vector

    z=1_H−1_(x_0+H)

has weight 2|H|=2r^(m−d), including in characteristic two, since the two cosets are disjoint. Its transform is |H|1_W(w)(1−χ_w(x_0)), hence vanishes outside W\{0}. On the required event all h parity products z a_j vanish, so the codeword with first systematic input z and other inputs zero has relative weight 2/(ell r^d). This proves (5). It is an upper bound on distance, not an algorithm for a decoding problem.

For a quotient π:G→V, the homomorphism of group algebras P(x)(v)=Σ_(g:π(g)=v)x(g) sends a uniform x to a uniform element, as those coordinate sums use disjoint nonempty fibers. Let I(z)(g)=z(π(g)). Then (I(z)x)(g)=Σ_b z(π(g)−π(b))x(b)=I(z P(x))(g). The coefficient weights of I are multiplied by |ker π|. Thus any word in the systematic quotient code lifts to one upstairs by applying I to each systematic input, with exactly the same relative weight. This argument is valid without dividing by |ker π|. Applying (5) to the quotient proves it upstairs.

For large m choose d=floor(log_r(m log_q(r)/(4h))). Then d≥1, d≤m/4 eventually, and r^d> m log_q(r)/(4hr). The product r^(m−d) q^(−h(r^d−1)) is at least r^(3m/4−d)≥r^(m/2). The right side of (5) is therefore at most exp(−r^(m/2)). Its distance threshold is at most 8hr/(ell m log_q(r)). For every fixed field q choose some fixed r unequal to its characteristic (r=2 if q is odd, r=3 if q is even), and take V itself. This adds q=2 to the all-groups counterexamples for the uniform systematic model; for q>2 the archived split deterministic theorem already disproves the general assertion. Theorem 1 supplies a complementary deterministic conclusion for the whole coprime bounded-exponent family, but with a weaker exponent in m when r>2.

## 4. Reading of the primary questions

- Bombar–Couteau–Couvreur–Ducros discuss a growing-|G| extension of Gaborit–Zémor, with k and ell constant and the systematic form enforced. At any fixed positive rate below 1, the ordinary GV target is a positive constant relative distance. The earlier split-elementary result already disproves the universal extension for q>2 in this code-ensemble sense. The present contribution extends the obstruction to general coprime bounded exponent and supplies q=2 counterexamples as well. See SOURCES.md for the distinction between their informal statement and AICR's formalization.
- Li–Liu–Xing–Yao–Yuan ask whether QA codes are asymptotically good at fixed index c and field size p, in the discussion of G=(Z/2)^m and p odd. In this stated group family the archived split-elementary result already answers negatively, even for arbitrary fixed-index positive-rate submodules of that group algebra. Theorems 1 and 2 give different refinements (deterministic rate dependence and a finite uniform-ensemble tail). No claim is made to settle tight probability lower bounds, other growing cyclic/group families, or the large-field concrete guarantees.
- These are statements solely about Hamming distance of mathematical code families. They neither assert an algorithm to find a low-weight codeword from an implementation nor imply recovery of an encoded secret, a distinguishing procedure for a deployed system, or insecurity of any cryptographic primitive.
