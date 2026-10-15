# Exact finite APPT power envelope at every real order above one

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. Research proof, 14 October 2026.
No external funding. OpenAI AI assistants assisted. Original material all
rights reserved. Complete ordinary proof of the displayed domain, not
complete Lean, external human peer review, or verified historical priority.

## 1. The exact finite statement

Let O_D consist of ordered probability spectra λ with
λ_1≤λ_(D−2)+λ_(D−1)+λ_D. Define

    π_j=(3 [j times],1 [D−j times])/(D+2j),
    F_(D,α)(j)=(j3^α+D−j)/(D+2j)^α,  1≤j≤D−3.

**Theorem L.** For every integer D≥15 and every real α>1,

    max_(λ∈O_D) Σ_i λ_i^α=max_(1≤j≤D−3) F_(D,α)(j).     (L1)

Every maximizing ordered spectrum is π_j with a maximizing index, and there
are no other equality spectra. In particular, for actual qubit–qudit states
on C²⊗C^n, every n≥8 and every real α>1 satisfy

    min_APPT S_α=min_ASEP S_α
      =log[max_j F_(2n,α)(j)]/(1−α).                    (L2)

All equality states are (I+2P)/(2n+2j), with P any orthogonal projection of
a maximizing rank. Only the clipped floor and ceiling of

    x_*=D(3^α−1−2α)/[2(α−1)(3^α−1)]                    (L3)

need be compared. Ties between those integer ranks are retained.

The earlier [power envelope](../appt-finite-high-order-20261014/POWER_ENVELOPE.md)
treated D≥8 and α≥2. Here logarithmic convex comparison closes the entire
1<α<2 interval when D≥15. At α=1 the known von Neumann entropy conclusions
remain credited to [Tran 2609.18568v1](https://arxiv.org/html/2609.18568v1),
whose Lemma 2.1 supplies the outer vertices. The needed entropy comparisons
below are explicit, rather than an assumption that a purity comparison
also works for every smaller power. D=8,...,14 and 1<α<2 are outside L1;
small-qubit intermediate orders and general subcritical finite minima are
not determined by this continuation.

## 2. Logarithmic size bias and two elementary comparisons

For any probability spectrum λ, put

    ν_λ=Σ_(λ_i>0) λ_i δ_(log λ_i).

This is a probability measure even for a singular spectrum. Its mean is
minus the natural-log von Neumann entropy, and

    E_(ν_λ) exp(βX)=Σ_i λ_i^(1+β),   β>0.               (L4)

First suppose ν is supported at b<a and η is supported inside [b,a], with
E_νX>E_ηX. For every increasing convex f with positive secant slope,

    E_η f≤secant_f(E_ηX)<secant_f(E_νX)=E_ν f.           (L5)

Second suppose η has support c<d and ν support b<a, ordered c<b<d<a.
In addition to the strict mean gap, assume

    E_ν(X−b)_+≥E_η(X−b)_+.                              (L6)

Then the stop-loss difference E_ν(X−t)_+−E_η(X−t)_+ is nonnegative for all
real t. Below c it is the positive mean gap. On [c,b] it is linear and its
end values are nonnegative. On [b,d] it is again linear with nonnegative
values at b and d; on [d,a] only the ν term remains; above a both vanish.
For an increasing twice differentiable convex f on [c,a], the identity

    f(x)=f(c)+f'(c)(x−c)+∫_c^a f''(t)(x−t)_+ dt

therefore gives E_νf>E_ηf when f'(c)>0, because the mean gap is strict.
Both facts apply to f(x)=exp(βx) for every β>0. No sign is being transferred
from a finite set of tested powers.

## 3. Prior vertices and strict entropy-mean gaps

The known complete vertices of O_D are

    R_r=(1 [r times],0 [D−r times])/r,  r=D−2,D−1,D;
    T_i=(2 [i times],1 [D−1−i times],0)/(D−1+i),
        1≤i≤D−3;
    π_i, 1≤i≤D−3.                                      (L7)

Their complete elementary ordered-simplex-cut derivation is reproduced in
the earlier POWER_ENVELOPE Section 3. Choose its known purity index

    J=D/4,(D−1)/4,(D+2)/4,(D+1)/4

in residue classes D≡0,1,2,3 modulo four, respectively. Set Q=D+2J and
r=D−4J∈{0,1,−2,−1}. D≥15 implies J≥4. The geometric entropy size of π_J is

    G_J=exp S_1(π_J)=Q·3^(−3J/Q).

We will use the strict inequalities

    G_J<(15/16)(D−1),
    G_J<D−2,
    exp S_1(π_(J−1))<(15/16)(D−1) when D≡2,3.           (L8)

To prove them for every dimension, temporarily vary J continuously with a
fixed r. The derivative of log[G_J/(D−1)] is

    (2r−6)/[Q(D−1)]−3r log3/Q².                        (L9)

It is negative for r=0,1. For r=−1,−2 it is also negative, using log3<4/3
and Q>D−1. Thus only the first allowed integer in each residue class must
be checked for the first inequality in L8. They are D=16,17,18,15,
respectively, with J=4,4,5,4. The required exact integer comparisons are

    128²<3·75²,
    5^25<3^37,
    448^28<255^28·3^15,
    184^23<105^23·3^12.                                 (L10)

Each is precisely the positive-power form of its displayed G_J bound.
For D≥18, (15/16)(D−1)<D−2. For D=17, the first strict bound in L8 gives
G_J<15=D−2 directly. The remaining cases D=15,16 have, respectively,

    23^23<13^23·3^12,   24²<3·14².                      (L11)

For the exceptional index J−1, write h=J−1 and D=4h+s with s=2 or3.
Its geometric ratio is (6h+s)3^(−3h/(6h+s))/(4h+s−1). The derivative has
the same form as L9 with s in place of r and h in place of J; it is strictly
negative for s=2,3. The first cases are h=4,D=18 and h=3,D=15. The exact
comparisons needed are

    416^13<255^13·3^6,   8^7<5^7·3^3.                   (L12)

All six dimension comparisons and the two R comparisons are explicit
integer inequalities, not fitted numerical estimates.

For T_i, continuous differentiation in its index gives the existing bound

    S_1(T_i)≥log[(e log2/2)(D−1)]
                   >log[(15/16)(D−1)].                 (L13)

Indeed the continuous minimum of log(D−1+x)−[2x/(D−1+x)]log2 occurs at
x=(D−1)(2log2−1) and has the displayed value. For a direct rational lower
bound, e>163/60 and log2>56/81 imply
e log2/2>1141/1215>15/16. The first inequality for e follows from its first
six nonnegative series terms, and the log2 bound from the first two terms
of 2atanh(1/3). The elementary upper bound log3<4/3 used in L9 follows by
integrating, or differentiating the gap in
log(1+y)<y(y+2)/[2(y+1)] at y=2.

Consequently the log measures of π_J, and of π_(J−1) in its stated cases,
have strict mean gaps over every T_i. Also the mean of ν_(π_J) exceeds
−log(D−2), the largest mean of the uniform vertex log measures.

## 4. Every T vertex: support containment and the missed first index

The support of ν_(π_J) is [log(1/Q),log(3/Q)]. The two T_i support points
lie inside this interval exactly when

    (4J−D+3)/3≤i≤2J+1.                                (L14)

The strict entropy-mean gap from Section 3 and L5 therefore exclude all
such T_i from any power maximum at α>1. The only indices below the left
bound are i=1 when D≡2 or3. Use π_(J−1) for those indices; its support
contains [log(1/D),log(2/D)]. This follows from D=4h+2 or4h+3, since
1/(D+2h)≤1/D≤2/D≤3/(D+2h). Its strict mean gap was proved in L8/L12/L13.
Thus L5 excludes these two exceptional first-index cases as well.

## 5. Every T vertex: the log stop-loss comparison

It remains to treat i>2J+1. Put T=D−1+i and u=T−Q=i−2J−1>0. The support
ordering is exactly c<b<d<a from L6, because

    1/T<1/Q<2/T<3/Q.

Here T≤2D−4<2Q. At b=log(1/Q), the two stop-loss values are

    E_(ν_(π_J))(X−b)_+=(3J/Q)log3,
    E_(ν_(T_i))(X−b)_+=(2i/T)log(2Q/T).                 (L15)

We prove the first is strictly larger for every such i. The elementary
logarithm bounds log3>13/12, log2<7/10 and
log t>2(t−1)/(t+1) for t>1 give

    (3J/Q)log3>13J/(4Q),
    (2i/T)log(2Q/T)<i(27Q−13T)/[5T(T+Q)].              (L16)

For log3 the first two positive terms of 2atanh(1/2) suffice. For log2,
2atanh(1/3)<56/81+1/540<7/10 follows by a positive geometric remainder.

Multiply the difference of the rational right sides of L16 by its positive
common denominator. Its sign is that of

    65J T(T+Q)−4Qi(27Q−13T)
      =(18J−56)Q²+Q(−37J−56r+52)u+(377J+52r)u².       (L17)

For J≥4 and r∈{−2,−1,0,1}, the leading coefficient is at least 377J−104,
and |−37J−56r+52|≤37J+4. Its discriminant is strictly negative, because

    4(377J−104)(18J−56)−(37J+4)²
       =25775J²−92232J+23280
       =25775(J−4)²+113968(J−4)+66752>0.               (L18)

The leading and constant coefficients are positive. Thus the quadratic in
L17 is positive for every real u, proving L15 strictly. The strict mean
gap from L13 and the complete stop-loss lemma L6 now exclude every remaining
T_i for every α>1, including 1<α<2.

## 6. Uniform vertices, physical attainment, and integer ranks

For R_r the log measure is the point mass at −log r. L8 and Jensen give,
for every β>0,

    E_(ν_(π_J))e^(βX)≥e^(βE_(ν_(π_J))X)>r^(−β).

Thus all R vertices are excluded strictly. The power objective is strictly
convex for α>1, so every maximizer on O_D must be a vertex. L7 and the full
T/R exclusions prove L1 and all its equality spectra.

Every actual APPT spectrum satisfies the defining inequality of O_D by the
physical rank-two witness. In C²⊗C^n, (I+2P)/(D+2rank P) is all-unitary APPT:
the partially transposed unit test projector has negative trace at most1/2,
so Tr[P(ww*)^Γ]≥−1/2 for every projection and every test w. A global unitary
replaces P by another projection. The disclosed published
[Johnston Theorem 1](https://arxiv.org/html/1309.2006) then gives ASEP.
All these physical bridges are written out in the earlier POWER_ENVELOPE.
They give L2 and every equality state, without any restriction on eigenvectors.

Finally 3^α−1−2α>0 for every α>1: it vanishes at one and has derivative
3^αlog3−2>0 thereafter. The exact log derivative of F_(D,α)(x) is

    [D(3^α−1−2α)−2(α−1)(3^α−1)x]
       /[(D+(3^α−1)x)(D+2x)].

Its single critical point is L3. Strict increase then strict decrease prove
the clipped floor/ceiling rule, including all ties. The α↓1 limit of L3 is
D(3log3−2)/4, agreeing with the credited von Neumann calculation.

## 7. Boundaries

The new theorem concerns D≥15, α>1 and actual qubit n≥8. It is an exact
finite result. For 1<α<2 it neither solves the small-qubit cases nor promotes
an outer vertex to APPT in general m≥3. No assertion about all positive
subunit orders or general APPT=ASEP follows. The earlier α≥2,D≥8 result and
its review retain their exact original scope. This ordinary continuation
does not expand any Lean build, source manifest, axiom list or audit root.
