# Exact all-positive-order pole phase in qubit–qudit APPT entropy

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. Research proof, 14 October 2026.
No external funding; OpenAI AI assistants assisted. Original material all
rights reserved. Ordinary proof, not complete Lean, external human peer
review or verified historical priority. Same APPT research direction.

## 1. Exact transition and physical statements

For every integer D≥8, let τ_D be the unique real solution α>2 of

    [(2·3^α+D−2)/(3^α+D−1)]·[(D+2)/(D+4)]^α=1.         (C1)

Existence and uniqueness are proved below for the entire real-order range,
not established by a numerical root calculation. Set

    t_D=log[(D+4)/(D+2)],  A_D=log2/t_D.

**Theorem C.** For actual C²⊗C^n states with n≥4, D=2n, the pole

    ρ_v=(I+2vv*)/(D+2)

is a Rényi entropy minimizer on either the APPT or ASEP set **if and only if**
α≥τ_D, for every positive real α, with α=1 interpreted as von Neumann
entropy. If α>τ_D all minimizing states have the pole spectrum. At α=τ_D
all equality states are exactly

    (I+2P)/(D+2rank P),  rank P=1 or2.                  (C2)

All such projections and all unit v are allowed. In the optimal band the
minimum is

    [α log(D+2)−log(3^α+D−1)]/(α−1).                    (C3)

For every bipartite pair 2≤m≤n with D=mn≥8, α≥τ_D is also sufficient for
the same exact APPT and ASEP value C3. If m≥3, only the pole spectrum is an
equality spectrum even at α=τ_D. No necessity or partition-specific cutoff
is asserted for m≥3 below τ_D.

The transition satisfies, as D→∞ through integers,

    0<A_D−τ_D=O(D²·3^(−D/4)),
    τ_D=(log2)(D+3)/2−(log2)/[6(D+3)]+O(D^−3).          (C4)

In particular τ_D/D→log2/2. Along even D the qubit pair makes this the exact
worst-partition cutoff for pole optimality; strict uniqueness for every pair
requires α>τ_D. Thus the leading constant log2/2 in a dimension-only eventual
guarantee is sharp, unlike the earlier sufficient D/2+1 bound.

This is a complete criterion for when the pole family is optimal. It does
not compute every subcritical entropy minimum. General APPT=ASEP is not
assumed: the pole's known absolute separability is credited and proved in
[POLE_SEPARABILITY](../appt-finite-high-order-20261014/POLE_SEPARABILITY.md).
The α≥2 finite outer envelope is the inherited ordinary theorem in
[POWER_ENVELOPE](../appt-finite-high-order-20261014/POWER_ENVELOPE.md),
with its explicit prior Tran/Johnston inputs. Its old review does not review
this new continuous-order phase argument.

## 2. The ratio on the whole positive-order axis

Put q=(D+2)/(D+4) and, for real a, define

    R_D(a)=q^a(2·3^a+D−2)/(3^a+D−1),
    g_D(a)=log R_D(a),  X=3^a.

Then R_D is precisely the moment ratio of the actual qubit rank-two
projection density to the pole. Both are all-global-unitary APPT; their
ASEP property follows from the disclosed qubit equivalence. They are not
arbitrary spectra from a relaxation. A direct derivative gives

    g_D'(a)=log q+(log3)h_D(3^a),
    h_D(X)=DX/[(2X+D−2)(X+D−1)],
    sign h_D'(X)=sign[(D−2)(D−1)−2X²].                 (C5)

Since (D−2)(D−1)/2≥21>9 for D≥8, h_D is strictly increasing for 1≤X≤3.
Thus g_D is strictly convex on [0,1]. Its endpoint values are g_D(0)=g_D(1)=0,
so

    g_D(a)<0 for every 0<a<1.                           (C6)

At one,

    g_D'(1)=−t_D+(3D log3)/[(D+4)(D+2)]>0.              (C7)

Indeed t_D<2/(D+2), log3>1 and 3D≥2(D+4) when D≥8. For a≥1 the h function
first increases up to X=sqrt[(D−2)(D−1)/2] and then strictly decreases to
zero. C7 implies that g_D' is positive until a unique zero and negative
thereafter, because its limiting value is log q<0. Consequently g_D first
strictly increases from zero at one and then strictly decreases to −∞.
It has exactly one further zero τ_D>1.

At a=2, positivity of R_D(2)−1 reduces to

    (D+16)(D+2)²−(D+8)(D+4)²
       =4(D²−3D−16)>0.                                 (C8)

For D≥8 this is strict, so τ_D>2. These arguments prove existence,
uniqueness, g_D>0 on (1,τ_D), and g_D<0 on (τ_D,∞).
Also R_D(a)<2q^a for every a, hence

    2<τ_D<A_D.                                         (C9)

## 3. Actual failure of pole optimality below the transition

For 0<α<1, C6 means the actual rank-two projection has a smaller power sum
than the pole; division by 1−α>0 gives smaller Rényi entropy. For
1<α<τ_D, positivity of g_D means it has a larger power sum, and division
by 1−α<0 again gives smaller entropy. At α=1, trace-normalized moments of
both densities equal one, and their log derivatives give

    S_1(ρ_v)−S_1(σ_2)=g_D'(1)>0.                       (C10)

Here σ_2=(I+2Q)/(D+4) for any actual rank-two projection Q. Thus the pole
fails to optimize at every positive α<τ_D, including the order-one point.
These strict physical competitors prove necessity in the full qubit phase
criterion, without a formula for the unknown subcritical optimizers.

## 4. Outer sufficiency and every critical equality spectrum

For α≥τ_D>2, the earlier outer theorem gives the maximum of
F_(D,α)(j)=(j3^α+D−j)/(D+2j)^α over integers 1≤j≤D−3.
As a function of the real rank it has a unique maximum, increases strictly
before its critical point and decreases strictly thereafter. If F(1)>F(2),
its critical point must be less than two, so every integer j≥2 has
F(j)≤F(2)<F(1). If F(1)=F(2), that point lies strictly between one and two,
and every integer j≥3 has F(j)<F(2). By the ratio calculation,

    α>τ_D: only π_1 is an outer equality spectrum;
    α=τ_D: only π_1 and π_2 are outer equality spectra.   (C11)

The extra D=8, α=2 uniform-rank-six outer equality is irrelevant since τ_D>2.
Every actual APPT density belongs to this necessary outer polytope. The
known ASEP pole attains its bound in every bipartite pair, so C3 holds on both
physical sets throughout the stated band. In qubit–qudit dimensions both
π_1 and π_2 are physically attained by every projection of the corresponding
rank, giving exactly C2 at the transition. Strict convexity of the outer
power objective excludes any additional ordered equality spectrum.

## 5. A rational physical control excludes π_2 when m≥3

Embed a 3⊗3 product basis in C^m⊗C^n. Let Q project onto the two orthogonal
unit antisymmetric vectors on pairs (1,2) and (1,3), and put

    w=(2|11>+2|22>+|33>)/3.

This is a unit vector with rational Schmidt amplitudes (2/3,2/3,1/3).
The eigenvalues of (ww*)^Γ on those two antisymmetric vectors are −4/9
and −2/9. Thus

    <w,[(I+2Q)/(D+4)]^Γ w>
       =[1+2Tr(Q(ww*)^Γ)]/(D+4)
       =−1/[3(D+4)]<0.                                 (C12)

The density is PSD and has spectrum π_2, but is not even PPT in this basis.
Every state with spectrum π_2 is globally unitarily equivalent to it, so
no such state is APPT when m≥3. It cannot be ASEP either. Hence C11 leaves
only the pole at the critical order for these pairs. This is an actual
finite negative control, not an assumption that the outer bound is sharp
or that APPT equals ASEP in higher local dimensions.

## 6. Exponential crossing correction and sharp asymptotics

For any fixed c>0, the actual ratio at a=cD obeys

    R_D(cD)→2exp(−2c).                                  (C13)

The first factor tends to two since 3^(cD)/D diverges, and
D log q→−2. In particular c=1/4 gives a limiting value greater than one,
so τ_D>D/4 for all sufficiently large D. At the exact crossing write

    ε_D=D/[2(3^(τ_D)+D−1)],
    0=g_D(τ_D)=log2−t_Dτ_D+log(1−ε_D).

It follows that

    A_D−τ_D=−log(1−ε_D)/t_D>0.                          (C14)

For large D, ε_D≤(D/2)3^(−D/4)≤1/2 and
−log(1−ε_D)≤2ε_D. Also t_D≥2/(D+4). Thus

    0<A_D−τ_D≤[D(D+4)/2]3^(−D/4).

Finally set z=1/(D+3). The exact identity and its positive-series expansion
give

    t_D=log[(1+z)/(1−z)]=2z(1+z²/3+O(z⁴)),
    1/t_D=(D+3)/2−1/[6(D+3)]+O(D^−3).

Combining this with C14 proves C4 and τ_D/D→log2/2. For even D the actual
qubit theorem gives failure at every smaller positive order and attainment
at τ_D, making the universal worst-partition bound exact there. The leading
constant is therefore sharp for a dimension-only guarantee. The proof does
not identify the earlier possible transitions for a fixed m≥3 partition.

## 7. Scope and remaining problem

The all-positive-order criterion concerns pole optimality, not every finite
entropy minimum below its transition. Its sufficiency/equality proof uses
the earlier exact α≥2 theorem in its correct domain. The new necessity and
unique crossing are proved on all positive real orders using actual density
families. The sharper constant and critical equality classification strengthen
the same APPT direction. No extra solved major conjecture, complete Lean,
external human peer review, or historical-first certification is claimed.
