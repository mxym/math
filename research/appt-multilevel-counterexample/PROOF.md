# Working proof: a multilevel counterexample to the general APPT purity formula

Research checkpoint, 10 October 2026. This is a mathematical working note, not a new preprint or Release. The argument below is analytic; the attached exact checker verifies identities and a physical boundary orbit, not all unitaries by finite testing. No Lean or external peer-review claim is made.

## 1. The conjecture being tested

Ahiable--Kothakonda--Winter, *The geometry of absolute separability and other convex matrix properties from spectrum*, arXiv:2608.03390, Conjecture 6.7, predicts that the maximum purity of an absolutely PPT state on C^m tensor C^n equals

    M(m,n) = max{ (D+8)/(D+2)^2,
                  [D(m-1)^2+4mt]/[D(m-1)+2t]^2 },
    D=mn, t=ceil((m-1)n/2), 2<=m<=n, n>2.

This is the exact inner-polytope maximum in their Theorem 6.3. Both statements were checked in primary v2 HTML (revised 18 September 2026), not only in the web cache, which still returned v1. The conjecture and formula are unchanged in v2. We disprove this formula, not the APPT characterization, the qutrit theorem, or APPT=absolute separability.

## 2. A uniform all-unitary positivity lemma

Let m>=4, n>=m, D=mn. Put b=2m-5 and delta=4(m-4). Let P be any orthogonal projection on C^m tensor C^n, and let v be any unit vector in its range. Define

    A = b I + 2 P + delta |v><v|.

Then A is positive definite and (U A U*)^Gamma is positive semidefinite for EVERY global unitary U. Gamma denotes transpose in the second tensor factor. The rank of P is arbitrary; no spectral ordering test is assumed.

Proof. Fix U and a unit test vector psi. Put P'=UPU*, v'=Uv and W=(|psi><psi|)^Gamma. Partial transpose is self-adjoint for the trace pairing, so

    <psi,(U A U*)^Gamma psi> = b + 2 Tr(P' W) + delta <v',Wv'>.       (1)

Write the Schmidt coefficients of psi in decreasing order as s1>=s2>=...>=sm>=0, padding zeros, with sum si^2=1. In Schmidt product bases,

    W = sum_i si^2 |ii><ii|
        + sum_{i<j} si sj (|ij><ji|+|ji><ij|).

Thus its eigenvalues are si^2, +si sj, -si sj, and zeros. Its trace is one; its least eigenvalue is -s1s2. Let N(s)=sum_{i<j}si sj. Since 0<=P'<=I, evaluation in an eigenbasis of W gives Tr(P' W)>=-N(s). The Rayleigh inequality gives <v',Wv'> >= -s1s2. These statements hold for arbitrary P',v', not merely for a chosen commuting orbit. Therefore (1) is at least

    b sum_i si^2 - 2 sum_{i<j} si sj - 4(m-4)s1s2.                  (2)

For arbitrary real x1,...,xm, let T=sum_{i=3}^m xi. The EXACT identity

    (2m-5) sum_i xi^2 - 2 sum_{i<j}xi xj -4(m-4)x1x2
      = (2m-6)(x1-x2)^2
        + 2 sum_{3<=i<j<=m}(xi-xj)^2
        + (x1+x2-T)^2                                             (3)

proves (2)>=0. To check (3), use sum_tail_pairs (xi-xj)^2=(m-2)sum_tail xi^2-T^2 and expand. All coefficients are nonnegative for m>=4. Since U and psi were arbitrary, the all-unitary APPT conclusion follows. Positivity of A is immediate from b>0 and its positive semidefinite summands. QED.

Notice that the relation v in range(P) is needed for the spectrum below, but not for the positivity estimate itself. No equivalence with a finite family of Hildebrand matrices, optimization output, or separability assumption is a premise.

If rank(P)=k, 1<=k<D, the eigenvalues of A are

    6m-19              once,
    2m-3               k-1 times,
    2m-5               D-k times.                                (4)

Let Z=Tr(A)=(2m-5)D+2k+4m-16. The density matrix rho=A/Z is APPT, has trace one and has exactly these normalized eigenvalues (three distinct levels when m>4 and 1<k<D).

## 3. An explicit counterexample in total dimension 380

Take m=10, n=38, k=147. In any fixed product-coordinate ordering choose P to project onto the first 147 coordinates and v to be the first coordinate. Then

    rho = diag(41, 17 [146 copies], 15 [233 copies]) / 6018.        (5)

The multiplicities sum to 380; the numerator trace is 6018. The numerator trace-square is

    41^2 + 146*17^2 + 233*15^2 = 96300.

The lemma proves that this ACTUAL complex density matrix is APPT. Its purity is

    Tr(rho^2) = 2675/1006009.

The two conjectured candidates, with t=171, are

    P1=97/36481,          P2=5/1881.

Both comparisons are strictly positive in exact rational arithmetic:

    Tr(rho^2)-P1 = 3802/36700214329 > 0,
    Tr(rho^2)-P2 = 1630/1892302929 > 0.                            (6)

Consequently Conjecture 6.7 is false in its stated arbitrary-dimensional range. This does not assert that (5) is a global maximizer or that 10x38 is the smallest counterexample dimension.

### A physical boundary orbit and a failing perturbation

The positivity proof does not depend on checking any particular orbit. Nevertheless, there is an explicit exact boundary orbit useful for auditing signs and transposes.

In C^10 tensor C^38, let P' contain all 45 antisymmetric vectors (|ij>-|ji>)/sqrt(2), 0<=i<j<10, and any 102 coordinate vectors |i,j> with j>=10. Let v'=(|0,1>-|1,0>)/sqrt(2). These give rank(P')=147 and v' in range(P'). They are related to the P,v in (5) by a global unitary. For

    psi=(4|0,0>+4|1,1>+sum_{i=2}^9 |i,i>)/sqrt(40),

one has (15I+2P'+24|v'><v'|)^Gamma psi=0. This is also equality in (3). All entries of the projection matrices and of the unnormalized state are rational, even though their displayed basis vectors involve square roots.

If the largest unnormalized eigenvalue 41 is changed to 42, equivalently 24|v'><v'| is changed to 25|v'><v'|, the same normalized test gives expectation -2/30095 after trace normalization. That perturbed state is NOT APPT. The exact checker must reject it; it is not accepted merely because it has three levels and large purity.

### The violation persists in the strict APPT interior

Let eps=1/1000 and rho_eps=(1-eps)rho+eps I/380. For every U,

    (U rho_eps U*)^Gamma >= I/380000.

Its purity equals 1/380+(999/1000)^2(2675/1006009-1/380), namely

    1016479028491/382283420000000.

The differences from P1 and P2 remain positive:

    679698380171/13946081445020000000,
    30523820609/37846058580000000,

respectively. The counterexample is therefore not an artifact confined to a singular partial-transpose boundary.

## 4. An infinite family of counterexamples

For EVERY integer m>=11 set

    n=4m, D=4m^2, k=2m^2-7m+26,

and use (4). These are valid multiplicities: 1<k<D. Define

    f(m)=4m^3-8m^2-5m+18,
    g(m)=4m^4-16m^3+11m^2+26m-16.

Direct expansion of the trace and trace-square gives Z=2f(m), Tr(A^2)=4g(m), and hence purity g(m)/f(m)^2.

Here t=2m(m-1), so P2=1/[4(m^2-1)]. It is strictly larger than the other candidate, because

    P2-P1 = 9/[4(m^2-1)(2m^2+1)^2] > 0.                         (7)

The gap from the conjectured maximum factors as

    g(m)/f(m)^2 - P2
      = (m-10)(4m^3-16m^2-5m+26)
        /[4(m^2-1)f(m)^2].                                      (8)

For m=x+11, x>=0, the cubic factor is

    4x^3+116x^2+1095x+3359 > 0.

The other factors have the indicated signs; f is positive because Z is the trace of a positive definite matrix. Equations (3), (7), and (8) prove violations in an unbounded family, without enumerating dimensions or relying on numerical optimization.

## 5. A two-parameter spectral mechanism, not an isolated example

For b>0, c>=0, d>=0, consider B=bI+cP+d|v><v| with v in range(P). Put a=c+d and q=2b-(m-3)c. The same physical test proves B is APPT whenever the real symmetric matrix with diagonal 2b, off-diagonal -(c+d) on the distinguished pair, and off-diagonal -c elsewhere is positive semidefinite.

On the endpoint difference subspace its eigenvalue is 2b+c+d; on tail-sum-zero vectors it is 2b+c. On the remaining two-dimensional subspace positivity is equivalent to

    2b-c-d >= 0,   q >= 0,
    (2b-c-d)q >= 2(m-2)c^2.                                    (9)

These conditions suffice for every rank k. If binom(m,2)<=k<=D-binom(m+1,2), they are also necessary: align P with all negative witness eigenvectors and enough zero eigenvectors, and v with the most negative one. Any Schmidt vector fits, including rank-deficient ones. Thus both Rayleigh lower bounds used in (1) are jointly attainable. Since the matrix has nonpositive off-diagonal entries, its quadratic form on abs(x) is no larger than on x; positivity on nonnegative Schmidt vectors is equivalent to full real positive semidefiniteness. This proves (9) as an exact membership test for this entire one-spike/plateau spectral subclass in the stated rank interval.

The simple choice b=2m-5,c=2,d=4(m-4) saturates (9). It explains why a spike and a low-contrast plateau can coexist at the APPT boundary. Restricting to two eigenvalues removes precisely this mechanism. The earlier two-eigenvalue theorem is not contradicted.

## 6. Scope and next mathematical question

Completed here: an explicit counterexample to the arbitrary-dimensional maximum formula, a sum-of-squares all-unitary positivity proof, strict-interior counterexamples, an infinite family, and an exact APPT condition for the displayed three-level subclass in its rank regime.

Not completed: the TRUE global maximum in arbitrary dimensions, its maximizers, minimal dimensions admitting a violation, APPT=absolute separability, or a Lean formalization of the new quantum lemma. Refuting the old formula does not supply a new sharp upper bound. Whether these new APPT spectra are absolutely separable is a separate question.

Primary target: https://arxiv.org/html/2608.03390v2 (Theorem 6.3 and Conjecture 6.7). Primary v2 retrieved directly because web cached results exposed only v1. No exhaustive historical-priority claim is made. The proof uses standard finite-dimensional spectral decomposition and Schmidt decomposition, with the required witness spectrum derived above. Research used AI assistance. Previous immutable proof and manuscript releases are unchanged.
