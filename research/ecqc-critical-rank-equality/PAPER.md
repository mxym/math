# Critical-rank equality in the pure-state ECQC bound

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. mxymmxym1@gmail.com.
ORCID 0009-0000-3864-3536. October 13, 2026.

This is an AI-assisted research manuscript. No external funding, human referee
review, or certification of historical priority is asserted. Copyright 2026
Yongxian Zhang; all rights reserved for the separately authored original material.

## 1. Definitions and the exact new scope

Let p be an odd prime, F_p its prime field, and ζ=exp(2πi/p). The canonical
complete mutually unbiased bases are the computational basis M_∞ and

    b_(a,j) = p^(-1/2) Σ_x ζ^(a x²+jx) |x>,       a,j in F_p.

The **same** basis is measured on both parties. The extended complementary
quantum correlation score E is the sum of the p smallest measured classical
mutual informations among these p+1 settings. All logarithms are natural.
This is the specialization of Iqbal's Conjecture 3.1, equation (6), to the
identical canonical families: its labels pair Alice's M_i^A with Bob's M_i^B.
No Bob-conjugated measurement convention is inserted. Iqbal's explicit
five-dimensional example uses the same D^aF family on both parties.
For a pure state with marginal entropy h, quantum mutual information is Q=2h.
The established Holevo inequality gives I_M≤h and hence E≤(p/2)Q.

The prior companion in this repository proved that nonproduct equality forces
a flat Schmidt spectrum and that its rank r is either p or at most (p+1)/2.
It also classified all full-rank equality states. The present manuscript
classifies **all equality states at the largest permitted deficient rank**,

    r=(p+1)/2.

Ranks strictly below r remain outside this classification. This does not settle
the optimal ratio at p≡3 mod4, p≥7, and no smaller supremum is inferred from
nonattainment at a particular rank.

Write R|x>=|-x> and P_+=(I+R)/2. For u,v in F_p define the Weyl displacement

    W_(u,v)|x> = ζ^(v(x+u/2)) |x+u>.

Changing this harmless global phase convention changes none of the rays below.
Every Weyl displacement permutes the outcomes within each canonical basis;
therefore independent displacements on Alice and Bob preserve every I_M.

**Theorem.** Let |ψ> be a pure state of Schmidt rank (p+1)/2. Then

    E(ψ)=(p/2)Q(ψ)

holds exactly in the following cases, up to overall phase:

1. p≡1 mod4. Choose any s with s²=-1 and put

       |Φ_p> = [2(p+1)]^(-1/2) Σ_x (|x,sx>+|x,-sx>).

   The equality states are precisely (W_(u,v)⊗W_(u',v'))|Φ_p>.
   The two choices s and -s give the same state.
2. p=3. Put e_+=(|1>+|2>)/√2 and

       |Φ_3> = (|0>⊗e_+ - e_+⊗|0>)/√2.

   The equality states are precisely its independent two-party Weyl orbit.
3. p≡3 mod4 and p≥7. No such equality state exists.

In cases 1 and 2 there are exactly p⁴ distinct rays. Each has

    Q=2 log r,       I_M=log r for all M,       E=p log r.

Consequently, at p≡3 mod4 and p≥7 every **rank-deficient equality state**,
if one exists, has rank at most (p-1)/2. This is an attainment obstruction,
not a statement that the unrestricted optimal ratio is smaller than p/2.

## 2. Boundary equality forces a displaced parity marginal

We detail the input from Holevo equality rather than postulating a state oracle.
For a pure state and any rank-one measurement on Alice, Bob's conditional
states are pure. If its measured mutual information attains h, equality in
Holevo implies that the nonzero conditional rank-one projectors commute. Such
projectors have parallel or orthogonal ranges. Equality of E with ph also
forces every one of the p+1 settings to attain h: each of the p smallest terms
is at most h, and the remaining term is at least those p terms and at most h.

The complete-MUB identity, for Hermitian A,B, is

    Σ_(M,j) Tr(A E_(M,j)) Tr(B E_(M,j)) = Tr(AB)+Tr(A)Tr(B).       (1)

It follows by orthogonally decomposing the real vector space of trace-zero
Hermitian matrices into the p+1 diagonal trace-zero subspaces, each of dimension
p-1. If a marginal had distinct positive spectral projectors P_λ,P_μ, the
commuting conditional-state criterion would force every product of their
diagonal weights to vanish. Equation (1) would then give
0=Tr(P_λ)Tr(P_μ), a contradiction. Thus each marginal equals P/r for an
orthogonal projector P of rank r.
Here the nonzero conditional vectors partition into mutually orthogonal ray
classes; their average has these rays as eigenvectors. Therefore each measured
vector's projection onto the Schmidt support lies in just one positive
eigenspace. This is the pointwise bridge giving the vanishing products used
with (1), including cases where several ray classes share one eigenvalue.

In any measurement basis, the projected vectors P b_j are parallel or
orthogonal. After reordering the labels, their Gram matrix P consists of
nonzero rank-one projection blocks and zero rows. Let T=I-P, q=p-r,
n_0 count the zero rows, and m_i≥2 be the sizes of the nonsingleton blocks.
Then

    q=n_0+Σ_i(m_i-1),
    t=#{j:T_jj>0}=n_0+Σ_i m_i≤2q.

The trace of T is q. Cauchy gives, in each basis,

    Σ_j T_jj² ≥ q²/t ≥ q/2.                                   (2)

Applying (1) to T,T gives total diagonal-square sum q+q². At the rank in
the theorem, q=(p-1)/2, so this equals (p+1)q/2. Therefore equality holds
in both inequalities (2), in **every** measurement basis.
For arbitrary q>0, the same comparison first gives (p+1)q/2≤q+q²,
and hence r≤(p+1)/2; this also proves the deficient-rank bound used in
the theorem's final corollary.

Equality t=2q forces n_0=0 and every m_i=2. Equality in Cauchy forces
all nonzero diagonal entries of T to be 1/2. Thus P has precisely one
singleton block [1] and (p-1)/2 two-by-two rank-one blocks, whose diagonal
entries are 1/2. In particular A=2P-I is a unitary Hermitian matrix of trace
one and, in **every canonical basis**, is monomial: its two-by-two blocks
have zero diagonal and off-diagonal phases; its singleton is [1].

**Lemma (three-basis monomial rigidity).** A trace-one Hermitian involution
A that is monomial in the computational, Fourier, and M_1 bases, and has
exactly one nonzero diagonal entry in the computational basis, is a Weyl
displacement of parity.

**Proof.** Write A_xy=θ_x 1_(y=f(x)), where f is a permutation and |θ_x|=1.
Let F_xj=p^(-1/2)ζ^(jx). Monomiality of F*AF means that each function
x↦θ_x ζ^(k f(x)) is a scalar character. At k=0 this gives
θ_x=e^(iθ)ζ^(bx). Dividing the k=1 and k=0 relations gives
f(x)=sx+t, with s≠0. In M_1=D_1F coordinates, where D_1 has diagonal
ζ^(x²), the corresponding functions have phase exponent

    (s²-1)x²+(2st+b)x+t²+k(sx+t).

They too must be scalar characters. Taking the second difference at -1,0,1
gives 2(s²-1)=0, hence s=±1. Slope +1 has either zero or p fixed points;
the prescribed singleton rules it out. Therefore f(x)=t-x. At its unique
fixed point x=t/2, the diagonal entry is +1, so
θ_x=ζ^(b(x-t/2)). It follows directly that

    A=W_(t/2,b/2) R W_(t/2,b/2)*.

This proves the lemma. □

Applying it separately to the two marginals and undoing their displacements
reduces the classification to states whose marginals are P_+/r on both
parties. No assumption that the initial state is a stabilizer state is used.

## 3. The reduced Fourier matrix and its distinguished first column

Choose one representative of every nonzero pair {x,-x}. In the even parity
subspace H_+, use the orthonormal basis e_0=|0> and
e_[x]=(|x>+|-x>)/√2. Its dimension is r=(p+1)/2. Write the amplitude
matrix of a state with both marginals P_+/r as V/√r on H_+⊗H_+, where
V is an r-by-r unitary matrix.

The computational measurement restricted to H_+ is this orthonormal basis
with every nonzero label split into two duplicate outcomes. The finite M_a
measurement similarly consists of an orthonormal reduced basis with duplicated
nonzero labels: parity exchanges b_(a,j) and b_(a,-j), while b_(a,0) is fixed.
Its reduced basis transformation is D_a^+ F_+, where D_a^+ has diagonal
ζ^(a x²) and F_+ is the restriction of F to H_+.

Duplicate labels add independent local randomness and leave mutual information
equal to that of the reduced projective measurements. Because V is invertible,
attainment of log r in a reduced pair of bases requires its amplitude matrix
to be monomial: all r conditional states are orthogonal, and vanishing classical
conditional entropy forces disjoint row supports. This is an actual consequence
of the Born law and h=log r, rather than an extra premise.

The reduced Fourier matrix F_+ is real symmetric and F_+²=I. Its distinguished
row and column satisfy

    F_(0,0)=1/√p,
    F_(0,[x])=F_([x],0)=√(2/p)   (x≠0).                       (3)

Every entry in its column 0 is nonzero. Thus column 0 is the only column
whose row-0 entry has modulus 1/√p.

**Lemma (diagonal conjugation rigidity).** Let D be a diagonal unitary matrix
on H_+. If F_+ D F_+ is monomial, then D is scalar.

**Proof.** Put B=F_+DF_+. Then D F_+=F_+B. As B is monomial, its column
0 is a unit phase times some coordinate vector, so column 0 on the right
is a phase times a column of F_+. Comparison of row-0 moduli using (3)
forces that column to be column 0. Comparing all its nonzero entries now
forces every diagonal entry of D to be the same phase. □

The monomial amplitude conditions at settings 0 and 1 are

    B_0=F_+ V F_+,
    B_1=F_+ D_(-1)^+ V D_(-1)^+ F_+.

If V_xy=θ_x 1_(y=f(x)), their product B_1 B_0* is

    F_+ diag[ζ^(-x²-f(x)²)] F_+.

It is monomial. The lemma and injectivity of powers of ζ show that

    x²+f(x)²=κ                                               (4)

is independent of the even-subspace label x.

## 4. Prime-field obstruction and all phases

The squares of the even-subspace labels are exactly the quadratic residues,
including zero, each once. Thus f induces a permutation σ of that full set Q_p,
and (4) reads q+σ(q)=κ. For p≥5,

    Σ_(q in Q_p) q = (1/2) Σ_(x in F_p) x² = 0.

Alternatively, multiplication by 4 permutes Q_p, so its sum equals four times
itself; since p≠3, the sum is zero. Summing (4), and using |Q_p|=(p+1)/2≠0
in F_p, gives κ=0. Since 1∈Q_p, also -1=σ(1)∈Q_p. Hence p≡1 mod4 is
necessary.

Choose s²=-1. Equation (4) now forces f([x])=[sx] for every nonzero orbit
and fixes label 0. Let U_s^+ be this permutation on H_+. It commutes with
F_+: the usual Fourier identity changes s to s^(-1)=-s, which induces the
same permutation in even parity. Write V=D_θ U_s^+. Monomiality of B_0
then implies that F_+D_θF_+ is monomial. The diagonal-rigidity lemma makes
D_θ scalar. Hence V is U_s^+ up to overall phase, yielding exactly |Φ_p>.

For p=3 the residue set is {0,1}; summing (4) gives κ=1, so f swaps the
two labels. Now

    F_+ = 1/√3 [[1,√2],[√2,-1]],    V=[[0,a],[b,0]], |a|=|b|=1.

The diagonal entries of F_+VF_+ are ±√2(a+b)/3; its off-diagonal entries
are (2b-a)/3 and (2a-b)/3. A diagonal monomial result would require
2b-a=2a-b=0, impossible for nonzero a,b. An anti-diagonal monomial result
therefore requires b=-a. This is exactly the even-subspace singlet |Φ_3>.
All its finite-setting amplitudes are scalar multiples of the same
anti-diagonal matrix, because D_(-a)^+ V D_(-a)^+=ζ^(-a)V.

## 5. Actual Born laws, sufficiency, and counting

For p≡1 mod4, the computational amplitude of |Φ_p> is

    C_xy = [1_(y=sx)+1_(y=-sx)] / √[2(p+1)].

Its squared norm is one: the sum of the squared numerators is 2(p+1).
Direct multiplication gives CC*=C*C=P_+/r, so the Schmidt spectrum is
1/r with multiplicity r and zero otherwise.

For **every** finite M_a setting the actual amplitude is

    (D_aF)* C overline(D_aF)_(j,k)
      = [1_(j+sk=0)+1_(j-sk=0)] / √[2(p+1)].                  (5)

Indeed each of the two supports reduces the double sum to a geometric sum
with quadratic coefficient -a(1+s²)=0. It equals p on the indicated line
and zero elsewhere. The computational law and (5) have the same block
structure: a singleton outcome (0,0) of mass 2/(p+1)=1/r, and r-1 paired
blocks, each of four outcomes of mass 1/[2(p+1)]=1/(4r). The latent block
is uniform on r labels and is determined by both local outcomes. Within
each paired block the two local duplicate labels are independent. Therefore
the mutual information is exactly log r. This proves all scores and
sufficiency directly from the true quantum measurements.

For p=3 the computational law is the two-block singlet law from the earlier
qutrit paper; the reduced-basis argument above applies in every finite
setting as well and gives log2. Equivalently, its numerator matrix is

    [[0,1,1],[-1,0,0],[-1,0,0]] / 2.

Undoing Weyl displacements preserves all measured mutual informations.
There are p² distinct displaced parity operators: their unique diagonal
singleton determines u, and their off-diagonal phases determine v.
Hence the pair of marginal support projectors identifies all p⁴ pairs of
displacements. The preceding necessity argument gives exactly one ray for
each such pair. Thus no double counting of roots s,-s or Weyl parameters
occurs, and the number of rays is p⁴.

## 6. Literature and verification boundaries

The original score is Iqbal, *On the CQC Conjecture*,
[arXiv:2509.08286v2](https://arxiv.org/abs/2509.08286v2), Conjecture 3.1.
Unrestricted mixed-state failures were already proved by Wang, Wang and Chen,
[arXiv:2608.03828](https://arxiv.org/abs/2608.03828). The present result is a
classification at one precisely specified rank, not a first disproof of ECQC.

Parity, Weyl displacements, and their phase-point interpretation are classical.
Gross, *Hudson's theorem for finite-dimensional quantum systems*,
[quant-ph/0602001v3](https://arxiv.org/html/quant-ph/0602001v3), Theorem 6(5),
identifies the phase-point operator at the origin as parity and proves Clifford
covariance. Durt–Englert–Bengtsson–Życzkowski,
[1004.3348v2](https://arxiv.org/html/1004.3348v2), discusses generalized Bell
states, MUBs and the parity/Wigner eigenspaces. These are credited as background;
their parity constructions are not presented as inventions of this paper.

The external entropy input is Holevo's theorem and the necessary commuting-state
condition; see Ruskai, *Inequalities for quantum entropy: a review with conditions
for equality*, [quant-ph/0205064v2](https://arxiv.org/abs/quant-ph/0205064v2),
Sections 7.2–7.3. All specialized rigidity, field and Born-law steps are proved
above. The previous full-rank theorem and rank gap are recorded in
`research/ecqc-stabilizer-saturation`; its immutable publication is unchanged.

Primary-source screening on October 13, 2026 found the classical parity machinery
and the previously cited ECQC papers. It did not certify priority of the present
critical-rank classification. An exhaustive literature review and external
refereeing are still separate work.

The Lean companion proves the universal prime-field residue-reflection
obstruction (Section 4) from actual quadratic residues for **all primes p≥5**,
including impossibility at p≡3 mod4, and the matrix distinguished-column
rigidity lemma with its explicit entrywise hypotheses.
It does not formalize Holevo equality, the complete-MUB saturation bridge, the
monomial/Fourier lemmas, Born transforms, or the full quantum classification.
The exact checker recomputes actual finite-prime amplitudes, marginal matrices
and symbolic logarithmic scores; its finite ranges support those certificates
and are not the proof of the arbitrary-prime theorem. Neither kind of checking
is external peer review.
