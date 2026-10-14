# Complete Hamiltonian Quantum PCP attempt

Original material: Yongxian Zhang; OpenAI AI assistants assisted.
No external funding; all rights reserved. Complete theorem QP0 is not solved.

The complete map was written before any own mathematical stage. It retains
quantum polynomial-time reductions, constant finite local dimension and
locality, polynomial descriptions/precision, general QMA promises and true
expectation-energy soundness against every global entangled witness.
The two-hour stage clock includes230 primary-screen seconds at07:50:02UTC.
Compaction/recovery195seconds and this map/commit preservation are excluded.

Prior inputs are precisely scoped in QUANTUM_PCP_SOURCES.json. The original
QSAT perfect-completeness fork does not establish general QMA; known NLTS
and the new combinatorial-soundness/growing-alphabet theorem are not QP0.
The proof-verification equivalence is prior work and is not recredited or
claimed completely audited in this packet.

No own mathematical argument has been adopted at this map-preservation
boundary. Next: seek a complete true-energy gap amplification or a complete
alternative reduction, with the constant locality/dimension and all-QMA
bridges explicit. Every candidate route remains unproved until those gates
are established. Finite controls and stronger-template obstructions cannot
be reported as full positive or negative results.

## Q1. Exact erasure-intersection expression; no quantitative shortcut

For normalized projective K=sum_i p_i Pi_i, p_i>0, sum_i p_i=1, set
C_K(psi)=sum_(i:<psi|Pi_i|psi> !=0) p_i. Then
min_psi C_K(psi)
=1-max_(S: intersection_(i in S) ker Pi_i != {0}) sum_(i in S) p_i.
Indeed positivity makes zero expectation exactly membership in the kernel.
Every psi gives such a zero set S, and every nonzero intersection supplies a
normalized vector. Mixed states cannot improve the minimum: their supports
must lie in every zero-expectation kernel, and a pure vector in the support
has at least the same zero set. This is elementary finite linear algebra.

Thus combinatorial soundness is an erasure-intersection statement. It does
not give a bound on the smallest singular value of the joint constraint
matrix or on how far a vector lies from the intersections.

## Q2. Complete elementary control for the failed universal conversion

For any delta>0 define one-qubit rational rank-one projections
P_0=[[0,0],[0,1]],
P_delta=[[delta^2,delta],[delta,1]]/(1+delta^2), and K_delta=(P_0+P_delta)/2.
Their two kernels are distinct one-dimensional lines. The combinatorial
minimum is exactly1/2: no vector annihilates both, and a kernel vector
annihilates one. This holds also when arbitrary dummy qubits are adjoined.

The eigenvalues of K_delta are
(1 +/- 1/sqrt(1+delta^2))/2.
The minimum equals
delta^2/[2 sqrt(1+delta^2)(sqrt(1+delta^2)+1)] < delta^2/4.
Take delta=2^-N and pad to N qubits. Descriptions have O(N) bits, every term
has norm1, locality1, physical dimension2 and interaction degree2, yet the
true average energy tends to0 while the combinatorial minimum remains1/2.

This proves that a universal lower bound based ONLY on combinatorial
soundness, locality, local dimension and degree cannot be used. It is NOT
a Quantum PCP counterexample, nor a counterexample to the particular BNZ
output family. The local projectors vary with N; no fixed-term-set impossibility
is claimed. Their norm distance is delta/sqrt(1+delta^2), and at delta=0 the
combinatorial minimum jumps to0. Constant-precision term rounding therefore
does not preserve the combinatorial functional.

A sufficient tailored repair statement would turn every low-energy vector
of the PARTICULAR output family into a vector annihilating all but less
than its guaranteed combinatorial fraction of terms. No such statement,
uniform spectral regularity or erasure-angle bound is proved here. Under
combinatorial soundness this repair gate is as strong as the desired energy
lower bound; simply restating it is not substantive progress.

## Q3. Direct tensor amplification keeps the complete missing resources

For 0<=H<=I and integer t>=1, A_t=I-(I-H)^(tensor t) has
lambda_min(A_t)=1-(1-lambda_min(H))^t, from the product eigenbasis.
If H=(1/m)sum_i Pi_i is projective then A_t is the average over all
m^t tuples of I-tensor_(j=1)^t(I-Pi_(i_j)); each is a projection.
It has locality at most kt and t copies of the input system.
This elementary known construction handles arbitrary entangled output
states because the operator spectrum is a tensor-product spectrum.
It does not give constant locality or a polynomial explicit term list when
t must grow to compensate an inverse-polynomial input gap.

Bergamaschi-Metger-Vidick-Zhang2510.01333v1 provides a prior derandomised,
iterable amplification and streaming formulation. Its read theorem statements
retain locality growth; their definitions use commuting layers and weighted
averages. Their statement is not assumed to be a new constant-locality result.
No complete theorem proof is reaudited or credited as our own.

## Q4. Exact and approximate high-distance-code energy obstruction

Let V:L -> (C^d)^(tensor N) be an isometry and suppose every operator A on
at most k' physical sites obeys V^* A V=c_A I_L. For every k'-local
Hamiltonian K=sum_j h_j, V^* K V=(sum_j c_(h_j)) I_L. Hence ALL encoded
logical states have the same expectation energy. Any attempted construction
requiring a nonconstant logical acceptance Hamiltonian to equal this
compression is impossible. Tensoring a fixed ancillary resource does not
help: partial expectation yields another at-most-k'-site operator.
This is the usual local-indistinguishability property of an exact code,
not a new no-go theorem for arbitrary Quantum PCP reductions.

More quantitatively, if for each h_j there is a scalar c_j with
||V^*h_j V-c_j I||<=eta ||h_j||, then
||V^*((1/M)sum_j h_j)V-((1/M)sum_j c_j)I||
<=eta (sum_j ||h_j||)/M<=eta when ||h_j||<=1.
The encoded energy range is at most2eta. For eta=o(1), such a
witness-wide compression cannot represent a constant acceptance-energy gap.
A general QMA-hard reduction need not have this fixed-code compression,
or preserve energies of all logical states; no full negative conclusion follows.

For a classical encoding E:{0,1}^n->{0,1}^N with minimum Hamming distance
d_min>k', the coherent embedding V|x>=|E(x)> makes every compressed
k'-local operator diagonal in the logical computational basis. Off-diagonal
matrix elements vanish because x!=y codewords differ outside the operator's
support. Thus it cannot preserve logical X information. Repetition gives
the simple instance GHZ+ and GHZ- with equal proper-subset marginals.
This specifically blocks coherent use of an ordinary high-distance
classical proof code as a full two-basis quantum compiler.

## Q5. Local copy comparison loses completeness for entangled witnesses

For two claimed copies of a pure n-site state psi, a single-site swap test
rejects with probability (1-Tr rho_i^2)/2, since
<psi tensor psi|SWAP_i|psi tensor psi>=Tr rho_i^2.
For a product of Bell pairs on the n sites, every rho_i=I/2 and rejection
is1/4 at every site, even for two correct copies. The normalized sum of
these local checks has a constant completeness cost.
A global swap recognizes all honest identical copies, but acts on2n sites.
This blocks only the direct local-swap consistency replacement, not
secret-sharing, code-based protocols or every possible reduction.

## Q6. Interaction-removal route and the full unclosed gates

Sun-Vidick2606.09588v1 is an EXISTING all-QMA qIOP, not a Quantum PCP proof.
Its initial witness commitment, successive return of small code blocks,
private stabilizer audit, then basis/constraint-dependent classical PCPP
response ensure reported measurements concern the same initial state.
Available cubical qLTCs give polylogarithmic query and round parameters;
constant parameters in their overview assume better qLTCs. The proof body
has not been fully audited here.

A proposed static proof must replace both the sequential quantum extraction
and adaptive response with local checks against ONE initial global witness.
Precomputing all classical answers as independent registers is unsound unless
their common-state consistency is proved; a witness can otherwise choose
different assignments for different constraints. Precomputing computational-
and Hadamard-basis readouts is not automatically a single compatible
quantum extension, and the coherent classical-code obstruction above applies
to one naïve implementation. Quantumly incompatible measurements are allowed
in a genuine verifier, so incompatibility alone is not a full impossibility.

The retained complete obligations are:
(1) general-QMA near-perfect completeness, not QMA1/exact-zero substitution;
(2) true expectation-energy soundness against every coherent output state;
(3) constant local dimension and locality, with polynomial description and
precision, without an unproved good-qLTC assumption;
(4) noninteractive static-proof or Hamiltonian compilation preserving the
full gap. Neither BNZ combinatorial amplification nor qIOP interaction has
supplied these four gates in this attempt. Full QP0 remains unproved.

## Q7. Friendly filter balancing and its exact norm sensitivity

In the BNZ overview toy situation of one colluding readout share per
d-share repetition block, with 0<gamma<1/2 noisy readout and d>=3, write
r0=gamma+(1-2gamma)eta, r1=1-r0.
The displayed branch-balance condition
(1-gamma)r0^(d-1)=gamma r1^(d-1)
has the unique solution
r0=1/(1+exp(L/(d-1))),
eta=(r0-gamma)/(1-2gamma), L=ln((1-gamma)/gamma)>0.
It obeys0<eta<1/2. For fixed gamma and d->infinity,
eta=1/2-L/[4(1-2gamma)(d-1)]+O_gamma((d-1)^-3).

For A_eta=diag(sqrt(eta),sqrt(1-eta)) and R(d-1) honest readout
shares, F=A_eta^(tensor R(d-1)) has
ln cond(F)=R(d-1)/2 * ln((1-eta)/eta)
=R L/[2(1-2gamma)]+O_gamma(R/(d-1)^2).
Thus making the block larger does not remove exponential-in-R condition
growth in this TOY exact branch-balancing operator. This calculation
does not reprove the full BNZ soundness analysis or refute their construction.

For any positive invertible F with condition number kappa, the normalized
postselection map rho -> F rho F /Tr(F rho F) has trace-distance bound
||P_F(rho)-P_F(sigma)||_1 <=2 kappa^2 ||rho-sigma||_1.
Expand the difference over one common normalization denominator; each
trace is >=s_min(F)^2 and both the operator trace norm and trace change
are bounded by s_max(F)^2||rho-sigma||_1.

The condition-number dependence cannot simply be omitted. For
F=diag(a,b), kappa=b/a, rho=|0><0| and
sigma=(1-epsilon)|0><0|+epsilon|1><1|,
the input trace distance is2epsilon, whereas the output distance is
2epsilon kappa^2/(1-epsilon+epsilon kappa^2).
Taking epsilon=kappa^-2 makes the input distance vanish and the output
distance tend to1. This is an exact elementary filter-control pair,
NOT a low-energy Hamiltonian counterexample or a Quantum PCP result.

Likewise, the injective teleportation filter Q_delta=P+delta(I-P) on
L disjoint resource pairs has condition number delta^-L. A global
norm-perturbation comparison alone may lose exponentially in L; actual
circuit geometry can improve this bound and must be used if this route
is to prove true energy soundness. ABN's read robust propagation lemma
has depth-dependent loss eta/delta^8+alpha/delta^16 at each backward step;
merely iterating the displayed lemma does not supply a constant-density
logical-fault extraction estimate.

## Q8. Protected readout flags: precise limited-code tension

Exact erasure privacy on a set B means V^*A_B V=c_A I for every operator
supported on B. A postselection operator E_B then has
V^*E_B^*E_B V=c I, so its success probability is independent of ALL
encoded logical states (also of an external reference's logical marginal).
This protects a coherent readout flag against that particular small bad set.

If every k'-site set is protected this way, the same identity makes every
k'-local readout energy scalar on the code. A logical flag projector which
distinguishes encoded0 and1 therefore cannot itself be a k'-local
observable on that protected code. This is the direct algebraic property,
not an obstruction to every more elaborate code/proof construction.

Protecting each small flag block separately is also insufficient for a
generic global postselection argument. Consider a classical correlated
mixture epsilon |0...0><0...0|+(1-epsilon)|1...1><1...1| of logical flags.
A bad operator large enough to read just ONE unprotected logical block
can select the all-zero branch, despite touching only one of arbitrarily
many blocks. Every proper-block privacy guarantee must be checked on the
ACTUAL adversarial support; small density of fully bad blocks alone does
not rule out this toy branch selection. No claim is made that this mixture
satisfies all terms of a BNZ or ABN Hamiltonian.

The active possible escape is a construction-specific coherent-noise or
logical-fault estimate which bounds bad-path WEIGHT rather than demanding
global norm closeness or assuming independent blocks. Such an estimate
has not been established here; its complete endpoint remains QP0.

## Q9. New adversarial fault tolerance is a prior ingredient, not closure

The latest Breuckmann-Golowich-Vazirani2608.16857v2 theorem uses constant
physical qudit dimension and tolerates an almost-linear number of fully
adversarial faults per time step. The read first6pages explicitly retain
a vanishing fault fraction, subpolynomial depth overhead, and noiseless
classical side computation. Its constant-alphabet circuit simulation is
not a gap-preserving constant-alphabet Hamiltonian assignment tester.
The authors explicitly leave the ABN low-energy extraction conjecture
as the main missing connection to even a subpolynomial-gap quantum PCP.

The ABN model's injective parent Hamiltonian is frustration-free before
the output check. Its code-space/rotated-state and noise apparatus avoids
the simplistic exact-code barrier Q4; this was checked in their actual
Section2.5, including Claim2.3's direct local distinction argument.
Thus Q4 is not asserted to invalidate ABN. The main restricted spectral
question is whether small TRUE parent-energy density forces a state to
encode a computation with few logical damaging faults, uniformly in
depth and without uncontrolled conditioning. Neither the displayed old
propagation inequalities nor the new fault-tolerance statement proves it.

All four full-QMA/energy/constant-resource/static-compilation gates remain.
No new complete solution, full negative result, restricted-major credit
or additional formal verification has been obtained.

## Current-task-only user boundary

The user explicitly requested completing current tasks, reporting together,
then temporarily stopping. Finish this SAME QP0 stage with its original
approximately120-effective-minute clock; do not start another candidate
after its preserved outcome. No independent root review pauses this clock.
