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
