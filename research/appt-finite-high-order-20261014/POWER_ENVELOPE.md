# Exact finite power extrema on the outer APPT polytope and on qubit–qudit states

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. Research proof, 14 October 2026.
No external funding. OpenAI AI assistants assisted. Original material all
rights reserved. Ordinary mathematical proof; no complete Lean or external
human peer review is claimed.

## 1. Statements and exact physical scope

Use natural logarithms and, for α>1, set

    S_α(ρ)=log Tr(ρ^α)/(1−α).

For any integer D≥4 let O_D be the compact set of ordered probability vectors
λ_1≥...≥λ_D≥0 satisfying

    λ_1≤λ_(D−2)+λ_(D−1)+λ_D.                            (P1)

For 1≤j≤D−3 define the spectrum and its power sum

    π_j=(3 [j times], 1 [D−j times])/(D+2j),
    F_(D,α)(j)=(j3^α+D−j)/(D+2j)^α.                    (P2)

**Theorem P.** For every integer D≥8 and every real α≥2,

    max_(λ∈O_D) Σ_i λ_i^α=max_(1≤j≤D−3) F_(D,α)(j).    (P3)

All maximizing ordered spectra are π_j with j maximizing P2, except that
when D=8 and α=2, the uniform rank-six spectrum is one additional outer
maximizer. There are no other equality vectors.

**Theorem Q.** For every n≥4, D=2n, and every real α≥2, on the actual
all-global-unitary APPT and absolutely separable (ASEP) density sets,

    min_APPT S_α=min_ASEP S_α
      =log[max_(1≤j≤D−3) F_(D,α)(j)]/(1−α).             (P4)

All equality states, and only those states, are

    ρ=(I+2P)/(D+2j),                                    (P5)

where P is any orthogonal projection of rank j maximizing P2. The outer
rank-six exception is not an actual APPT spectrum. P4 is an exact finite
formula, with no dimension or order limit. In general m≥3, P3 remains an
upper bound on power sums; this manuscript does not claim that every π_j
is physically APPT there.

The vertex classification and the α=2 purity optimization are prior results
of [Tran, Lemma 2.1 and Theorem 2.2](https://arxiv.org/html/2609.18568v1).
Needed elementary comparisons are included below. The step from purity to
every real power α≥2 uses size-biased convex comparison. ASEP in Theorem Q
uses the published qubit–qudit equivalence in
[Johnston, Theorem 1](https://arxiv.org/html/1309.2006).
These are disclosed mathematical inputs, not hidden Lean assumptions or
claims to have newly discovered the vertices, purity, or APPT=ASEP theorem.

## 2. Physical necessity and the singular exception

For a density on C^m⊗C^n with m,n≥2, an actual rank-two Schmidt witness places
λ_D and λ_(D−2) in its diagonal slots, λ_1 in its negative pair and λ_(D−1)
in its positive pair. Positivity for every pair of nonnegative Schmidt
coefficients forces

    (λ_1−λ_(D−1))²≤4λ_D λ_(D−2).                       (P6)

Equivalently the symmetric 2×2 form with diagonals λ_D, λ_(D−2) and
off-diagonal −(λ_1−λ_(D−1))/2 is positive semidefinite. A negative eigenvector,
if one existed, can be chosen with two entries of the same sign, so the
nonnegative-coefficient tests suffice. All four eigenvalue slots are distinct.
The equal-coefficient test gives P1. Thus every actual APPT spectrum lies in
O_D; no equivalence with this linear relaxation is presumed.

If λ_D=0, P6 forces λ_1=λ_(D−1). Ordering and trace one then give the unique
singular spectrum (1 [D−1 times],0)/(D−1). In particular uniform rank D−2
is not APPT. This excludes the additional D=8, α=2 outer vertex.

## 3. The known vertices and the needed purity gaps

The vertices of O_D are the following three families:

    R_r=(1 [r times],0 [D−r times])/r,  r=D−2,D−1,D;
    T_i=(2 [i times],1 [D−1−i times],0)/(D−1+i),
        1≤i≤D−3;
    π_i as in P2, 1≤i≤D−3.                             (P7)

For completeness, the ordered probability simplex has coordinates
x_i=i(λ_i−λ_(i+1)), λ_(D+1)=0. They are nonnegative, sum to one, and express
λ as Σ_i x_i R_i, now allowing all 1≤i≤D. The functional in P1 has values
−1/i for i≤D−3, zero at i=D−2, 1/(D−1) at i=D−1, and 2/D at i=D.
Intersecting this simplex with its nonnegative half-space keeps R_(D−2),
R_(D−1),R_D. A new vertex has the cut equality and exactly two positive
x-coordinates of opposite functional signs: three positive coordinates
would admit a nonzero perturbation preserving both sum and cut equality.
The cut edge joining i≤D−3 to D−1 gives T_i; the cut edge joining i to D
gives π_i. Each has enough active equalities to be a vertex. This reproduces
the prior vertex argument solely to make the proof self-contained.

Choose the known purity-optimal index

    J=D/4                 if D≡0 (mod 4),
      (D−1)/4             if D≡1 (mod 4),
      (D+2)/4             if D≡2 (mod 4),
      (D+1)/4             if D≡3 (mod 4).                (P8)

Set Q=D+2J and M=Σ_i(π_J)_i²=(D+8J)/Q². For D≥8,

    M>Σ_i(T_j)_i² for all j;
    M>1/(D−2) for D≥9,  M=1/6 for D=8.                 (P9)

Here is an explicit verification of just those prior purity gaps. The
continuous maximum of (D−1+3x)/(D−1+x)² occurs at x=(D−1)/3 and is
9/[8(D−1)]. Since |D−4J|≤2 and Q>D,

    M=4/(3D)−(D−4J)²/(3DQ²)>4(D²−1)/(3D³).

Subtracting 9/[8(D−1)] or 1/(D−2) from the last lower bound gives positive
denominators and numerators, respectively,

    5D³−32D²−32D+32,
    D³−8D²−4D+8.

At D=8+s and D=9+s these become
5s³+88s²+416s+288 and s³+19s²+95s+53, respectively, all positive for s≥0.
Direct substitution gives the D=8 equality. These are credited comparisons
from Tran's purity proof, rather than new purity results.

## 4. Size-biased convex comparison eliminates T and R

For any probability vector λ, its size-biased probability measure is

    ν_λ=Σ_i λ_i δ_(λ_i),
    E_(ν_λ) X=Σ_i λ_i²,
    E_(ν_λ) X^(α−1)=Σ_i λ_i^α.                          (P10)

Zero entries contribute no mass. Suppose ν is supported at the two endpoints
b<a and η is supported inside [b,a], with E_νX>E_ηX. Every increasing convex
f with positive endpoint secant slope satisfies

    E_η f≤secant_f(E_ηX)<secant_f(E_νX)=E_ν f.           (P11)

If instead every point in the support of η is strictly below E_νX, monotonicity
and Jensen give E_ηf<f(E_νX)≤E_νf. Apply these facts to f(x)=x^(α−1), which
is increasing and convex for every real α≥2.

The endpoints of ν_(π_J) are 1/Q and 3/Q, and its mean is M. The endpoints
of ν_(T_i) are 1/(D−1+i) and 2/(D−1+i). They lie inside [1/Q,3/Q] whenever

    (4J−D+3)/3≤i≤2J+1.                                (P12)

P9 and P11 exclude these T_i strictly for all α≥2. For i>2J+1 the largest
endpoint is at most 2/(Q+1), which is strictly smaller than M, since

    (D+8J)(Q+1)−2Q²=Q(4J−D+1)+6J>0.                   (P13)

In the four residue classes, 4J−D+1 is 1,0,3,2, respectively. The second
comparison after P11 therefore excludes every such T_i.

The only indices missed by P12 are i=1 when D≡2 or 3 (mod 4). Here use
π_(J−1). Its support contains that of T_1: writing D=4h+2 or 4h+3 gives
J−1=h≥2, and 1/(D+2h)≤1/D≤2/D≤3/(D+2h). Its purity is strictly larger
than the purity (D+2)/D² of T_1. After removing positive factors from their
common-denominator numerators, the signs are those of

    6h³−2h²−4h−1     for D=4h+2,
    16h³+4h²−12h−6   for D=4h+3.                       (P14)

The first inner polynomial at h=2+t is 6t³+34t²+60t+31; the second at
h=1+t is 16t³+52t²+44t+2. Thus P11 excludes T_1 as well. This comparison
does not require π_(J−1) to maximize the α-power sum.

Finally ν_(R_r) is the point mass at 1/r. For D≥9, P9 and Jensen give

    E_(ν_(π_J)) f≥f(M)>f(1/(D−2))≥f(1/r).              (P15)

For D=8, the last comparison is strict for r>6. For r=6 and α>2, strict
convexity of f makes Jensen strict because ν_(π_J) has two distinct support
points. For α=2 it is exactly equal. Every maximizing vector of O_D is a
vertex, because Σλ_i^α is strictly convex for α>1. P7 and all the strict
comparisons prove P3 and its complete equality statement.

## 5. Actual attainment and all qubit–qudit equality states

On C²⊗C^n take any unit test vector w, and write H=(ww*)^Γ. Its negative
part has at most one eigenvalue, of magnitude s_1s_2≤1/2, from the Schmidt
coefficients s_1²+s_2²=1. For every orthogonal projection P,

    <w,P^Γw>=Tr(PH)≥−Tr(H_−)≥−1/2.

Consequently I+2P^Γ≥0. A global unitary replaces P by another projection,
so every density P5 is APPT. Johnston's Theorem 1 makes it ASEP as well,
for every n, including n≥4 where PPT for a single state would be insufficient.

Every maximizing j in P2 is therefore attained on the actual two physical
sets. Necessity P1 and Theorem P give the matching upper bound. Section 2
excludes the extra outer singular vertex. All remaining equality spectra
are π_j; the spectral theorem expresses every density with that spectrum
as P5 for a rank-j projection, and conversely every such projection works.
This proves P4 and the full equality classification without restricting
eigenvectors or using sampled unitary tests.

## 6. Explicit integer-rank calculation

Put Z=3^α−1. For α≥2, Z>2α: equality fails already at α=2, and the derivative
of 3^α−1−2α is positive there and thereafter. Extending P2 to real x≥0,

    d/dx log F_(D,α)(x)
      =[D(Z−2α)−2(α−1)Zx]/[(D+Zx)(D+2x)].             (P16)

It is positive below, and negative above, the unique critical point

    x_*=D(3^α−1−2α)/[2(α−1)(3^α−1)].                  (P17)

Clip floor(x_*) and ceil(x_*) to the integer interval [1,D−3], remove
duplicates, and evaluate P2 there. The larger value gives every maximizing
j; ties give both states P5 and no convex combinations of distinct ordered
spectra. Strict convexity in Section 4 excludes such combinations.

If α≥D/2+1, then x_*<D/[2(α−1)]≤1. The real function is strictly decreasing
on [1,D−3], hence j=1 is the unique maximizing rank. For every actual
bipartite pair with D≥8 this already proves the unique pole spectrum in the
finite high-order band; its ASEP attainment in all dimensions is supplied
in [POLE_SEPARABILITY.md](POLE_SEPARABILITY.md).

## 7. Boundaries

Theorems P and Q treat real α≥2, not only integer powers. Q covers n≥4;
the two smaller qubit–qudit dimensions have separate arguments in
[FINITE_SPIKE_PHASE.md](FINITE_SPIKE_PHASE.md) only for stated high-order
bands. General finite minima at lower orders for m≥3 are not determined.
The prior α=2 purity, vertex classification and white-noise endpoints are
credited. No verified historical-first or additional major-conjecture count
is claimed. This ordinary proof has no complete Lean formalization; inherited
audits do not certify its new optimization or equality statements.
