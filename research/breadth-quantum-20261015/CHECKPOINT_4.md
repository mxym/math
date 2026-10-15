# N0 checkpoint 4: exact route boundaries and memory tests

15 October 2026. Yongxian Zhang (张永贤), South China University of
Technology. No external funding. OpenAI AI assistants assisted. Original
material: all rights reserved; external results retain their attribution.
This is an author research log, without independent review or Lean proof.
**The full finite-dimensional NPT bound-entanglement target N0 remains
open in this packet. New major solutions: zero.**

## 1. Hermitian real/imaginary parts do not remove the rank constraint

Write an arbitrary complex rank-at-most-two coefficient operator as
C=H+iK with H,K Hermitian. Both H and K have at most two positive and at
most two negative eigenvalues. Indeed, a positive eigenspace of dimension
greater than two intersects ker C, whereas the quadratic forms of H and K
vanish on ker C. The same argument applies to the negative eigenspaces.
Partial traces preserve Hermiticity and Tr(AB) is real for Hermitian A,B.
Consequently the actual form satisfies

    Q_k(lambda,C)=Q_k(lambda,H)+Q_k(lambda,K).

It would therefore suffice to prove nonnegativity on the larger
Hermitian inertia-(2,2) domain. That sufficient statement is false. On two
qutrit sites put P=|0><0| and

    H=I_3 tensor P-P tensor I_3.

It has inertia (2,2,5), rank four, zero trace, squared Hilbert–Schmidt norm
four, and partial traces 3P-I and I-3P. Hence

    Q_2(lambda,H)=4-12lambda.

This is negative throughout the NPT Werner region lambda>1/3. H is not an
admissible rank-two coefficient operator. For an explicit rank-two
completion, let K have unit symmetric off-diagonal entries between
|i,0> and |0,i>, i=1,2, and zero otherwise. Its partial traces vanish and
Q_2(lambda,K)=4. On each indicated two-dimensional block H+iK equals
[[1,i],[i,-1]], a rank-one nilpotent matrix. Thus the actual coefficient
operator has rank two but

    Q_2(lambda,H+iK)=8-12lambda >= 2   for lambda<=1/2.

The compensating imaginary contribution cannot be dropped. These sparse
modes are closely related to existing canonical-family witnesses, and no
novelty or full-domain impossibility claim is made. Exact symbolic
controls are in EXACT_ROUTE_CONTROLS.json.

## 2. Why a one-qubit memory induction cannot distill a one-copy-
undistillable state

Consider a sequential LOCC protocol which starts with separable memory,
consumes one fresh copy of a fixed one-copy-undistillable state rho in
each round, and retains at most a two-dimensional quantum memory per
party between rounds. This limit counts all retained quantum systems,
including an eventual output pair. Classical transcripts may be arbitrary.
No other quantum resource or simultaneous coherent input block is allowed.

Conditional on any transcript, suppose the memory is separable. Expand
it as a mixture of product states and, if necessary, of local pure states.
Each branch of the next LOCC operation is a sum of product Kraus actions
on rho with locally prepared ancillas. Were the resulting two-qubit
memory NPT, the one-copy Schmidt-rank-two pullback criterion would give
a one-copy negative witness for rho. Therefore that memory is PPT.
PPT implies separability in 2-by-2, so induction applies at every round.
Mixtures over transcripts remain separable, and the closedness of the
separable set also excludes an asymptotic entangled two-qubit output.

The external input PPT=SEP in 2-by-2 is attributed to the Horodecki
separability theorem, [quant-ph/9605038v2](https://arxiv.org/abs/quant-ph/9605038v2).
The same argument applies to a fixed 2-by-3 memory using its corresponding
PPT=SEP theorem. It does not apply to 3-by-3 memory, an unbounded retained
register, or coherent processing of several fresh copies before the
compression. Nor does it cover two witness rays merely because each ray
separately has a small matrix-product representation: the combined local
filter must fit the stated total memory bound. This elementary operational
restriction is not a solution of arbitrary-copy distillability.

## 3. Qutrit memory: exact restricted protocols and a physical control

The sparse canonical witness used here is attributed to
[Tabia–Chen–Hsieh, 2608.08836v2](https://arxiv.org/html/2608.08836v2).
With r=1,2, define

    u_r=(|0,r>+|r,0>)/sqrt(2),
    v_r=(|0,r>-|r,0>)/sqrt(2),
    psi=(u_1 tensor v_1+u_2 tensor v_2)/sqrt(2),

where the Schmidt split groups the two Alice registers versus the two
Bob registers. This is a unit vector of collective Schmidt rank two.
An exact physical negative control uses the existing canonical state

    rho_C=(Delta+(2/3)(I-F))/7,
    Delta=sum_i |i,i><i,i|.

It is positive with trace one and

    <psi,(rho_C^Gamma)^{tensor 2}psi>=-1/882.

This is verification of an attributed result, not a new NPT example.

For the actual d=3 Werner inputs, first compress two copies locally to
qutrits using four specified isometries: the diagonal code |i,i>, the
antisymmetric and symmetric complementary-pair codes, and the modulo-3
sum code sum_a |a,i-a>/sqrt(3). The sixteen pairs of Alice/Bob codes
produce sixteen explicit intermediate states. Apply the above witness to
two independent outputs; this consumes four original Werner copies.

STRUCTURED_MEMORY3.json records the exact unnormalized witness
polynomials. STRUCTURED_INTERVAL_CERTIFICATES.json rewrites every one in
the Bernstein basis after lambda=(2+t)/6. Every coefficient is strictly
positive; the smallest is 11/32. The basis functions are nonnegative and
sum to one for 0<=t<=1. Thus all sixteen specified protocols have positive
expectation throughout 1/3<=lambda<=1/2, not just at sampled points.
The physical normalization and the successful-filter probability are
positive, so neither can reverse the sign. This excludes these sixteen
protocols only.

For the antisymmetric code on both sides an exact entry-by-entry identity
gives the unnormalized output

    S=(1-lambda/2)I+(lambda^2-lambda/2)F.

Its effective Werner parameter is

    lambda_eff=lambda(1/2-lambda)/(1-lambda/2) <= 1/12 < 1/3

for 0<=lambda<=1/2: the numerator is at most 1/16 and the denominator at
least 3/4. This particular output is PPT; at lambda=1/2 it is I/9 after
normalization. It cannot support the proposed NPT recurrence.

A separate 600-computation-second search varied arbitrary complex
3-by-9 local prefilters before the same fixed final canonical witness.
It completed 9,795 finite local optimizations. Best normalized four-copy
values were approximately 0.0392324, 0.0486822 and 0.144 at lambda=0.5,
0.49 and 0.4. The final rank remains at most two algebraically. Gradient
controls passed at about 5e-11. A lambda=0.75 negative control retained
both spectator factors and gave -1/128. These minima are local numerical
outputs, not lower bounds over all filters or evidence for all copies.

## 4. One finite-n positive-map construction has an explicit all-copy
obstruction

The finite-n construction in Section III of
[Müller-Hermes–Reeb–Wolf, 1502.05630](https://arxiv.org/abs/1502.05630)
uses a separable P whose two-qubit block is

    P=I+|00><11|+|11><00|,

and a Choi operator J_epsilon=P-epsilon I. This can give nontrivial
n-tensor-stable positive maps with epsilon chosen depending on n.

For any integer k let each party have a normalized GHZ vector, with the
relative minus sign on Bob's vector. Their joint product has four support
strings and direct multiplication gives exactly

    <GHZ_+ tensor GHZ_-, J_epsilon^{tensor k}
          (GHZ_+ tensor GHZ_-)>
        =(1-epsilon)^k-1/2.                              (U)

The diagonal contribution is (1-epsilon)^k. The two off-diagonal entries
between the all-zero and all-one paired strings give -1/2. For every
fixed 0<epsilon<1, (U) is negative at some finite k, specifically whenever
k>log(2)/[-log(1-epsilon)]. The same witness stays in the embedded
two-dimensional subspaces of higher input/output dimensions. For example
epsilon=1/10 first turns negative at k=7, with expectation
-217031/10000000. The checks also cover epsilon=1/256, whose first
negative k is 178. No finite-n guarantee is contradicted.

This excludes this particular shifted P construction as a fixed
nontrivial all-copy map. It does not exclude other unextendible-product-
basis constructions, general positive maps, or NPT bound entanglement.
The indefinite Choi J_epsilon is not a physical density matrix. Formula
(U) is an author-derived route control, with no novelty/priority claim.
Its exact four-support evaluation is in ALL_COPY_ROUTE_CONTROLS.json.

## 5. A higher-Schmidt-rank boundary still lacks a tensor certificate

To avoid the preceding embedded-qubit obstruction one may inspect the
known orthogonally covariant map family. Write Omega_un=|sum_i i,i>
<sum_i i,i| and put

    J=(1-epsilon)I-(F+Omega_un)/(d+1).

J is invariant under partial transpose. Its maximally entangled
eigenvalue is -epsilon. On unit vectors of Schmidt rank at most r, the
exact minimum of its expectation is

    1-epsilon-(r+1)/(d+1).

Indeed <F><=1 and <Omega_un><=r; the real diagonal rank-r maximally
entangled vector attains both bounds simultaneously. Thus for d=3 and
0<epsilon<=1/4 the corresponding map is two-positive at one copy, and
neither completely positive nor completely copositive. These single-site
coordinates belong to the existing orthogonal-covariance literature;
see [Park–Youn, 2024](https://link.springer.com/article/10.1007/s11128-024-04361-6).
The displayed elementary calculation is not an all-power certificate.

In particular the physical-state condition cannot be ignored: J and its
partial transpose are both indefinite when epsilon>0. One cannot simply
declare J^Gamma a density matrix. An all-copy positive-map theorem, plus
the attributed construction that converts it to physical NPT bound
entanglement, would still be needed. Finite product-vector searches of
J^{tensor k} are recorded separately with their actual limits. They
neither establish tensor-stable positivity nor close gates N3–N5.

## 6. Exact quantifier condition for a compactness route

Fix finite local dimensions and let F_k be the physical states which are
k-copy undistillable under the full complex rank-two criterion. These
are closed subsets of the compact density-matrix set. To see this, the
unit sphere of rank-at-most-two coefficient operators is compact, and
the witness expectation is jointly continuous in the state and vector.
Taking its minimum over that fixed compact vector set preserves
continuity; F_k is the inverse image of [0,infinity).

Moreover F_{k+1} is contained in F_k. Any negative k-copy witness can be
extended by a product vector with positive one-copy expectation. Such a
product vector always exists: the trace of rho^Gamma is one, so at least
one product basis diagonal is strictly positive. Tensoring that product
vector preserves collective Schmidt rank at most two and the strict
negative sign.

For any epsilon>0 the states with

    lambda_min(rho^Gamma) <= -epsilon

form a closed compact set G_epsilon. Thus, in these fixed dimensions, a
uniform-margin existence assertion

    there exists epsilon>0 such that, for every k,
    F_k intersect G_epsilon is nonempty

is equivalent to the existence of a single NPT state in every F_k.
The forward implication is the nested compact intersection theorem; the
reverse implication takes any epsilon smaller than the negative
eigenvalue magnitude of the fixed state. This is a quantifier audit,
without a claimed new result or a demonstrated uniform margin.

Merely finding an NPT member of each F_k, with a margin allowed to tend
to zero, is insufficient: the limit can be PPT. Unboundedly growing
dimensions also give no compact set of fixed finite physical states.
No required uniform margin, all-copy positive-map certificate, or
complete complex rank-two nonnegativity certificate was obtained here.
