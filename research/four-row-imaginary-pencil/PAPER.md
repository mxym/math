# Sharp four-row norms for purely imaginary permanent–determinant pencils

**Yongxian Zhang (张永贤)**
School of Computer Science and Engineering, South China University of Technology.
Email: mxymmxym1@gmail.com. ORCID: 0009-0000-3864-3536.
13 October 2026.

OpenAI AI assistants assisted research, discovery computation, exact verification
and writing. No external funding or external human referee review.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.

## 1. Main theorem on the actual complex matrices

For a complex 4×4 matrix A, write P(A)=per A, D(A)=det A and

    R(A)=Π_(i=1)^4 (Σ_(j=1)^4 |A_ij|²)^(1/2).

**Theorem 1.** For **every** complex 4×4 matrix A and every real t,

    |per A+i t det A| ≤ max{3/2, |t|+1/√3} R(A).            (I1)

The least possible constant is the displayed one. More precisely, if

    V_t={ |per A+i t det A|/R(A) : A∈C^(4×4), R(A)>0 },

then V_t has greatest element max{3/2,|t|+1/√3}; the optimum is attained.
The bound includes matrices with zero rows. No assumption that an optimizer
is unitary, sparse, real, or a block-diagonal matrix is used in the upper bound.

Let β=3/2−1/√3>0. The sharp constant is 3/2 on the entire interval
|t|≤β, and |t|+1/√3 outside it. This determines the **whole purely imaginary
axis**, rather than a finite table of coefficients. The general coefficient
λ∈C with both nonzero real and imaginary parts remains unclassified here.
The complete equality classification on this axis is proved in
[EQUALITY.md](EQUALITY.md): below the transition only flat rank-one matrices
occur; at the transition they coexist with oriented Fourier3 direct sums;
above it only the oriented Fourier-block class occurs. Zero rows give trivial
equality. Higher matrix orders are not claimed.

The permanent-only endpoint 3/2 and the real-coefficient norm are already
known; they are not attributed to this paper as new. The substantive new
step is a universal, phase-sensitive inequality at the nonreal boundary
iβ. Its proof is the exact finite matrix identity in Section 3, with positive
Gram factors checked over Q(√3,i). The identity implies an inequality for
**all** complex matrices, not just the matrices used during discovery.

## 2. Two elementary endpoint estimates

We record both estimates used to extend the boundary certificate:

    |per A|≤(3/2)R(A),      |det A|≤R(A).                    (I2)

They can be proved together without an external conjecture. For a,b∈C⁴ let

    U=Σ|a_j|², V=Σ|b_j|², η=|Σ a_j overline(b_j)|²,
    τ=Σ |a_j|²|b_j|²,
    S(a,b)=Σ_(j<k)|a_jb_k+a_kb_j|²,
    W(a,b)=Σ_(j<k)|a_jb_k−a_kb_j|².

Expansion gives S=UV+η−2τ and W=UV−η. Cauchy–Schwarz gives
η≤UV and η≤4τ, hence S≤(3/2)UV and W≤UV.

Split A into row pairs (a,b) and (c,d). The two-row Laplace expansions and
Cauchy–Schwarz give

    |per A|²≤S(a,b)S(c,d),
    |det A|²≤W(a,b)W(c,d).

Complementation permutes the six two-column subsets; the determinant expansion
adds only unit signs. This proves (I2), including the vanishing-row cases.
The permanent endpoint is also the n=4 case of Carlen–Lieb–Loss's classical
Hadamard-type permanent inequality; the determinant estimate is Hadamard's.

## 3. The exact boundary certificate

Set H=(C⁴)^(⊗4), indexed by tuples x∈{0,1,2,3}⁴, and define the explicit
coefficient tensor

    T_β=Σ_(σ∈S₄) (1+iβ sgn σ)|σ(0),σ(1),σ(2),σ(3)>.

If u(A)=overline(A_(0,*))⊗...⊗overline(A_(3,*)), then

    <T_β,u(A)> = overline(per A+iβ det A),
    ||u(A)||² = R(A)².

Thus the desired boundary inequality is exactly nonnegativity of
<u(A),[(9/4)I−|T_β><T_β|]u(A)> for product tensors.

Let G contain the **288** pairs (r,c)∈S₄×S₄ of equal parity. It acts unitarily
on H by

    g_(r,c)|x> = |c(x_(r(0))),c(x_(r(1))),c(x_(r(2))),c(x_(r(3)))>.

Every g maps product tensors to product tensors, preserves their norm, and
fixes T_β: the two permutation parities multiply to one. For S⊆{0,1,2,3},
Γ_S means the ordinary matrix partial transpose in precisely those tensor
factors. This is a completely defined linear operation on 256×256 matrices.

The accompanying `imaginary_boundary_certificate.json` supplies seven matrices
N_j, seven Hermitian matrices Z_j, their exact factorizations Z_j=L_j Δ_j L_j*,
the index set F_j in which each N_j is embedded, and transpose subsets S_j:

| j | S_j | rows of N_j | columns of N_j = size of Z_j |
|---|---|---:|---:|
| 0 | ∅ | 6 | 5 |
| 1 | ∅ | 12 | 3 |
| 2 | ∅ | 24 | 13 |
| 3 | {0} | 10 | 6 |
| 4 | {0} | 18 | 11 |
| 5 | {0,1} | 28 | 21 |
| 6 | {0,1} | 12 | 7 |

Let Ñ_j be the 256-row matrix obtained by inserting the supplied rows at the
listed distinct basis indices F_j and zero rows elsewhere. Put Q_j=Ñ_j Z_j Ñ_j*.
The exact identity is

    (9/4)I−|T_β><T_β|
      = (1/288) Σ_(g∈G) Σ_(j=0)^6 g Γ_(S_j)(Q_j) g*.       (I3)

Each diagonal entry of every Δ_j is **strictly positive**. Therefore every
Z_j, and hence every Q_j, is positive semidefinite. The certificate contains
no variable matrix A and no sampled value of t: (I3) is one exact identity
between explicitly specified algebraic matrices.

**How its exactness is established.** Each complex scalar is encoded as four
rational strings [a,b,c,d], representing a+b√3+i(c+d√3). The checker uses
Fraction arithmetic and the sole multiplication identity (√3)²=3. It verifies
all seven L_j Δ_j L_j* identities and signs of their diagonal factors. Signs
of a+b√3 are determined exactly: if a,b have opposite signs, compare a²
and 3b² with rational arithmetic; otherwise their common sign suffices.
It then constructs the embedded Q_j, performs **all 288** group actions
explicitly, and checks **all 65,536 entries** of (I3). This verification does
not rely on the smaller symmetry-orbit system used during discovery.

The proof checker and scalar arithmetic are provided as short, inspectable
standard-library source files. Their output is a certificate replay of an
algebraic identity, not extrapolation from finite parameter evaluations. The
supplied Gram factorizations, not numerical solver eigenvalues or solver status,
are the positivity proof. Corrupted Gram entries, a negative factor and the
wrong boundary coefficient are rejected.

**Why (I3) proves the original inequality.** For any product vector w,

    <w,Γ_S(Q)w> = <w^(bar S),Q w^(bar S)> ≥0               (I4)

when Q is positive semidefinite. Here w^(bar S) conjugates just the S factors;
(I4) follows by expanding matrix entries. Apply it with w=g* u(A) to every
term in (I3). Since g* preserves product structure, the right side is
nonnegative for **every** complex A. Therefore

    |per A+iβ det A|≤(3/2)R(A).                            (I5)

No arbitrary positive-partial-transpose state is substituted for A in this
argument. The partial-transpose matrices are explicit tools in a sum-of-squares
identity on the original product vectors. The complete norm theorem is a
written proof with exact algebraic certificates; it is **not a Lean theorem**.

## 4. Extension to every real parameter

For 0≤t≤β put θ=t/β∈[0,1]. Then

    per A+i t det A
      =(1−θ)per A+θ(per A+iβ det A).

The triangle inequality, (I2) and (I5) bound this by (3/2)R(A). For t≥β,

    |per A+i t det A|
      ≤|per A+iβ det A|+(t−β)|det A|
      ≤[3/2+t−β]R(A)=[t+1/√3]R(A).

Replacing A by its entrywise conjugate proves the negative-t cases as well:
permanent, determinant and row norms all conjugate in the expected way.
These arguments prove the upper bound (I1) for the **entire** real t-axis.
They are scalar inequalities applied to the actual matrix objectives, not
an unproved reduction of the set of maximizing matrices.

## 5. Explicit sharp witnesses

The all-1/2 matrix has all four row norms one, permanent 3/2 and determinant
zero. It gives the first branch at every t.

Put ω=(-1+i√3)/2 and

    F₃=(1/√3)[[1,1,1],[1,ω,ω²],[1,ω²,ω]].

The identity 1+ω+ω²=0 shows its rows are orthonormal. Direct six-term
expansion gives

    per F₃=−1/√3,        det F₃=−i.

For t≥0 take A=overline(F₃)⊕[1]. Its rows have norm one,
per A=−1/√3 and det A=i, so

    |per A+i t det A|=t+1/√3.

For t≤0 take F₃⊕[1]. It gives |t|+1/√3. At each real t, choosing the
larger of this witness and the flat matrix proves attainment of the constant
in (I1). This completes Theorem 1, including the greatest-value assertion.

## 6. Relation to prior results and limits of this paper

Carlen, Lieb and Loss, *An inequality of Hadamard type for permanents*,
[math/0508096](https://arxiv.org/abs/math/0508096), Methods and Applications
of Analysis 13 (2006), 1–18, proves the classical permanent-only constant.
The [repository's earlier four-row work](../../preprints/four-row-permanent-determinant-2026-10/README.md) proves
|per A|+c|det A|≤max{3/2,1+c}R(A) for all c≥0 and classifies equality;
it also gives the exact norm for every real pencil coefficient. Those results
do **not** imply (I1) by the triangle inequality: at t=1 they give only 2,
whereas the sharp imaginary constant is 1+1/√3.

The [earlier three-row full complex norm](../../notes/complex-permanent-determinant/PAPER.md) has five branches; its Fourier witness
motivated the second branch here. We give the actual embedded witness explicitly.
The present boundary certificate is a separate four-row argument and does
not assume a four-row unitary-optimizer theorem. Existing frozen sources,
releases and Lean packages have not been changed.

Targeted primary-source screening checked Carlen–Lieb–Loss and the OpenAI/math
September 26 four-row permanent/permutation-moment manuscript. Searches did not
establish historical priority of this imaginary-axis statement. The result is
presented as the precise theorem proved here, without a first-solution claim.

The full complex-plane candidate

    max{3/2,|1+λ|,|1−λ|,|λ+i/√3|,|λ−i/√3|}

remains **unproved** for four rows in this paper. Numerical product optimization
is only discovery evidence. A numerical gap in a fully-PPT relaxation near a
different complex-coefficient transition is not a counterexample among actual
matrices, and is not used in Theorem 1. No higher-order tradeoff or
experimental confirmation is asserted. The imaginary-axis equality proof is
complete in the linked supplement; its support rigidity follows from the
actual first positive Gram factor, not from a unitary-optimizer hypothesis.

## 7. Reproduction and exact verification scope

```bash
python3 check_certificate.py --negative-controls
python3 check_equality_structure.py
```

Only Python 3.10+ and its standard library are required. The project contains
the exact boundary data, scalar arithmetic, full-matrix verifier, theorem-to-proof
map and source hashes. Windows and WSL replays are recorded separately with
the actual certificate and checker source hashes. They run the same exact
checker in two environments, not two independent implementations or an external
referee process. The discovery program used SDP and floating point to find
candidate numbers; the published proof/replay needs neither.

The exact algebraic check proves (I3) and positive factors; Sections 2, 4 and 5
provide the elementary analytic endpoint, extension and sharpness arguments.
Together they prove the stated full imaginary-axis theorem. The equality
supplement gives the complete equality classification, and its checker verifies
the actual difference Gram block, exhaustive support obstruction and three-row
boundary algebra. There is no Lean
formalization, kernel replay or peer-review claim for this new package.
