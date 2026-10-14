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

## Q10. Fixed Clifford resources do not implement a non-Clifford channel

Suppose E(rho)=Tr_R[C(rho tensor sigma)C^*], where C is one fixed Clifford
unitary, sigma is any fixed (even entangled/mixed magic) resource, and all
unretained outputs are discarded without outcome-dependent operations.
For every output Pauli P, C^*(P tensor I)C is a Pauli tensor product.
Taking the resource expectation gives E^*(P)=c Q, with c real, |c|<=1,
and Q an input Pauli (possibly identity).

If E is a unitary channel U, this implies U^* P U is a Pauli for every P,
so U must be Clifford. Equivalently, a pure fixed resource with decoupled
garbage cannot turn a fixed Clifford circuit into a non-Clifford unitary.
This also handles mixed resources via their channel directly.

For U=diag(1,exp(i*pi/4)) on a qubit,
U^* X U=(X-Y)/sqrt(2). Its operator-norm distance from any scaled single
Pauli cQ is at least1/sqrt(2). Therefore ||E-U(.)U^*||_diamond>=1/sqrt(2),
using the channel's action on an output norm-one observable as a lower bound.
Allowing a classical convex mixture of such fixed circuits enlarges this
Pauli image to the l1 unit ball of Pauli coefficients. Its distance from
(X-Y)/sqrt(2) is at least1-1/sqrt(2): the nearest traceless coefficient pair
is(1/2,-1/2); adding identity cannot improve operator norm.
The mixture of the identity and phase-S channels with weights1/2 attains
that latter bound, since after undoing U it is a dephasing channel with
error probability(1-1/sqrt(2))/2.

This is a LIMITED channel-compilation control, not an exclusion of Clifford
QMA verifiers, adaptive measurement, postselection, non-Clifford local terms
or a general Quantum PCP reduction. Bravyi-Kitaev's actual introductory
magic-state model explicitly permits measurements and adaptation. Moving
non-Clifford operations into fixed resources cannot silently remove those
operations from a Hamiltonian construction.

## Q11. A bounded-copy outcome predicate cannot supply the missing gap

For a fixed Boolean rejection predicate f on t binary outcomes, tested on
independent identical copies whose local-test rejection probability is z,
p_f(z)=sum_(b in {0,1}^t) f(b) z^|b|(1-z)^(t-|b|).
After symmetrizing let c_s in[0,1] be f's average on weight-s strings.
Then p_f=sum_(s=0)^t c_s binom(t,s)z^s(1-z)^(t-s), and
p_f'=t sum_(s=0)^(t-1)(c_(s+1)-c_s)binom(t-1,s)z^s(1-z)^(t-1-s).
The Bernstein weights sum to1, so |p_f'|<=t on[0,1].
A constant separation across a gap epsilon therefore needs t=Omega(1/epsilon).

For full soundness against all entangled copies, the product eigenstate
with all copy eigenvalues equal to the input ground eigenvalue remains
an allowed output witness. Thus this necessary Lipschitz control applies
to this BLACK-BOX fixed outcome-predicate template. It does not constrain
arbitrary input-dependent explicit Hamiltonian reductions, coherent
functional calculus or arbitrary assignment testers.

## Q12. Exact local-trace multiset normalization; an attributed model bridge

Let H=sum_(i=1)^m h_i, with each h_i PSD, supported on at most q sites of
local dimension d, and 0<=H<=I. The explicitly listed terms may repeat.
Write u_i=Tr_local(h_i). Then
||h_i||<=u_i and
sum_i u_i <=d^q Tr_global(H)/d^n <=d^q.
This is the standard local-trace estimate also displayed in BHW Lemma8.

For h_i!=0 set r_i=ceil(m u_i) and A_i=m h_i/r_i. Make r_i copies
of A_i in an output list. Each A_i is PSD and has norm at most1.
With R=sum_i r_i,
1<=R<=m(d^q+1), and the output average is EXACTLY
K=(1/R)sum_(i,j<=r_i) A_i = (m/R)H.
No global operator norm is computed. Every state and every eigenvalue
scales by the same known rational factor. A constant input gap gamma
stays at least gamma/(d^q+1), at the same q-locality.
Rational descriptions and ceiling operations have polynomial bit size.

Zero terms are omitted; if the entire operator is zero or scalar, its
promised branch is decided directly from the explicit scalar/thresholds.
Nontrivial thresholds outside[0,1] are also trivial when forced by PSD
norm bounds. The bridge does NOT amplify an inverse-polynomial input gap.

If a chosen output convention requires distinct term supports, nonconstant
A_i can be paired with a separate auxiliary flag for each occurrence:
B_(i,j)=A_i tensor|0><0|+(I)tensor(I-|0><0|).
Then0<=B_(i,j)<=I and
B_(i,j)>=A_i tensor I,
with equality on the all-zero flag sector. Hence the global minimum equals
that of sum_(i,j)A_i even for arbitrarily entangled flags. Locality is at
most q+1, dimension remains constant, and there are polynomially many flags.
Scalar identity terms are removed with a threshold shift before this optional
distinct-support variant; a wholly scalar instance is already decided.
If an entry acts on fewer than q+1 sites, query padding may be ignored.

BHW's read smoothing proof instead keeps the original m slots and n sites
by regrouping terms, with2q locality. These are different resource conventions.
This direct multiset/flag variant is an elementary normalization of a known
equivalence, with no novelty/priority or full Quantum PCP claim.

## Q13. Complete qualified verifier-to-Hamiltonian reconstruction

Assume a GIVEN single-proof verifier has at most q=O(1) measured-index
queries in the qualified adaptive model, polynomial workspace/circuit size,
and fixed completeness c>soundness s with c-s>0 constant. This is an
assumption about the verifier; no such verifier for all QMA is constructed.

There are m<= (N+1)^q complete index paths, including a halt symbol.
For each path p, the combined event "this path and reject" is a positive
POVM effect R_p on its at-most-q accessed proof qubits. Workspace is
initialized in its prescribed fixed state and contracted out. Therefore
R=sum_p R_p=I-E_accept satisfies0<=R<=I, and for EVERY global proof rho
the rejection probability is Tr(R rho). This includes entangled proofs
and path probabilities depending on the proof.

Each local matrix R_p can be learned by running the path circuit, aborting
before any mismatching query, on computational basis u and the states
(u+v)/sqrt(2),(u+i v)/sqrt(2). Diagonal probabilities and those two
polarization probabilities determine all real and imaginary entries.
Let D0=2^q, choose epsilon<(c-s)/4 and eta=epsilon/(3m).
With raw probability error zeta=eta/(4D0), each Hermitian estimate A_p has
operator error at most eta: off-diagonal real/imaginary errors are at most
2zeta each, hence entry error at most3zeta and row bound at most3D0 zeta.

There are at most K=m D0^2 raw probabilities. T>=K/(4delta zeta^2)
independent repetitions per probability guarantee all errors at most zeta
with probability >=1-delta, by variance<=1/(4T), Chebyshev and a union bound.
For fixed q and fixed delta>0 this is polynomial time and sample size.
All empirical matrices are finite rational Hermitian matrices.

Ensure PSD on EVERY run without computing the global norm. For each
constant-size A_p find a certified rational ell_p<=lambda_min(A_p) with
lambda_min(A_p)-ell_p<=eta. This can be done with a finite rational
Rayleigh-quotient net: empirical ||A_p||<=B0=2D0; a grid on real/imaginary
coordinates of spacing1/L with L>=4 B0 D0/eta approximates every unit
vector after normalization within2D0/L. Its minimum quotient mu obeys
lambda_min<=mu<=lambda_min+eta, so ell=mu-eta is a certified lower bound.
The grid has (2L+1)^(2D0) points, polynomial size because q is fixed.
Rayleigh quotients of nonzero rational vectors are rational; no floating
eigenvalue oracle is needed.

Set B_p=A_p+max(0,-ell_p)I. It is always PSD. On the successful event,
lambda_min(A_p)>=-eta, ell_p>=-2eta and
||B_p-R_p||<=3eta, hence ||B-R||<=epsilon for B=sum_p B_p.
Compute U=max(1,sum_p Tr_local B_p). Always ||B||<=U.
On success the local-trace inequality gives U<=D0(1+epsilon).
Thus H=B/U is an ALWAYS valid PSD local Hamiltonian with0<=H<=I.

For the successful output define
a=(1-c+epsilon)/U, b=(1-s-epsilon)/U.
YES has lambda_min(H)<=a and NO has lambda_min(H)>=b; the gap is at least
(c-s-2epsilon)/(D0(1+epsilon)), a constant. Apply Q12 to get the
explicit constant-relative-gap norm-one list, at locality q (or q+1 with
the optional distinct-support flags). Correctness is uniform over all
witnesses, not just the tomography inputs. Output Hamiltonians need not
be identical on all successful runs; that stronger property is not assumed.

This rederives the randomized all-state reconstruction COMPONENT of the
KNOWN qualified proof-verification-to-LH bridge. It does not independently
prove a fixed-output quantum reduction convention or that QMA has such a
given verifier. The unclosed full target
QP0 is precisely where an all-QMA constant-query construction is missing.

## Q14. The known reverse bridge preserves entangled-proof soundness

For a normalized PSD term-list H=(1/M)sum_i A_i with constant gap gamma
between ground-energy thresholds a<b, verify ell separate registers of one
joint proof, independently selecting one term per register and measuring it.
In YES the prover can give ell independent ground-state copies. In NO,
even conditioned on prior outcomes of an entangled joint proof, the next
register is some density operator with expected rejection at least b.
For binary rejection variables X_j,
E[exp(-t X_j)|previous outcomes] <=1-b+b exp(-t).
Iterating this inequality supplies the usual Bernoulli lower-tail bound.
At threshold(a+b)/2, both errors are <=exp(-ell gamma^2/2), using the
ordinary upper-tail bound for the honest product witness.
Choose ell=ceil(2 ln3/gamma^2), a constant. Queries are at most ell q,
proof length ell N is polynomial, and soundness assumes NO independence.
Trivial PSD threshold branches are handled directly. Measurement precision
can be chosen below a fixed fraction of gamma. This is prior standard
energy-verification/amplification, not a new major theorem.

## Q15. Actual identity-chain numerical discovery; no universal inference

One finite floating spectral run constructed the actual one-wire ABN
identity-chain parent terms:
Lambda=delta P_Bell+(I-P_Bell);
h_in=Lambda(|1><1| tensor I)Lambda;
h_mid=(Lambda tensor Lambda)(I-I tensor P_Bell tensor I)(Lambda tensor Lambda);
h_last=(Lambda tensor I)(I tensor(I-P_Bell))(Lambda tensor I).
All are positive contractions on2,4,3 consecutive qubits respectively.
For depth D there are2D+1 qubits and D+1 terms. Global Z parity commutes
with each term. The exact filtered Choi construction has an even-parity
zero-energy state, while the odd-parity spectrum probes the limited
wrong-input-bit sector for this identity layout.

The18 finite cases used delta=.2,.5,.8 and depths1..6. Even-sector minima
were within1.5e-15 of zero numerically; odd minima stayed positive in
these cases. No rigorous lower bound, asymptotic scaling or generic ABN
fault-extraction counterexample follows. In particular the one-wire sector
does not by itself establish a forbidden fault DENSITY in the many-wire
adversarial model. The exact program and observed floats are preserved in
QUANTUM_PCP_IDENTITY_SPECTRAL_CONTROL.py / .json. This is auxiliary discovery,
not a solved class or full Quantum PCP result.


## Q16. Joint classical sharp flags are an additional restricted requirement

This section concerns a compiler demanding ONE common-state joint flag law
for all proposed sharp checks. Quantum PCP itself does not require such a
compiler and allows incompatible measurements selected in different runs.

For two projective measurements {P_a},{Q_b}, a positive joint POVM
{G_ab} with marginals P_a,Q_b exists if and only if every P_a commutes with
every Q_b. Indeed 0<=G_ab<=P_a and <=Q_b imply
P_a G_ab=G_ab=G_ab P_a and Q_b G_ab=G_ab=G_ab Q_b.
Summing gives P_a Q_b=G_ab=Q_b P_a. Conversely use G_ab=P_a Q_b.
For instance SWAP_12 and SWAP_23 do not commute on three qubit registers:
their two product orders send |010> to |001> and |100>. Their associated
symmetric-subspace sharp checks cannot all be precomputed as joint flags.

There is also a direct error floor. Suppose one binary joint POVM has
marginals A,B approximating projectors P,Q with operator errors <=epsilon.
Its canonical dilation V psi=sum_ab sqrt(G_ab)psi tensor|ab> is an isometry
with commuting flag projections Phat,Qhat and
A=V^*Phat V, B=V^*Qhat V. Put Pi=VV^*, and
L_P=(I-Pi)Phat V, L_Q=(I-Pi)Qhat V.
Then ||L_P||^2=||A-A^2||<=3epsilon, likewise for Q, because both A,P
are contractions and ||A^2-P^2||<=2epsilon. Commutativity upstairs gives
[A,B]=-L_P^*L_Q+L_Q^*L_P, hence ||[A,B]||<=6epsilon.
Also ||[P,Q]-[A,B]||<=4epsilon, so ||[P,Q]||<=10epsilon.
For P=(I+X)/2,Q=(I+Z)/2 the commutator norm is1/2, forcing epsilon>=1/20.

These are direct elementary calculations, not an audited general
measurement-compatibility literature theorem. A custom encoded witness or
a verifier selecting one incompatible context can evade the joint-flag
requirement. No full QP0 impossibility follows.

## Q17. Literal local equality testing cannot reproduce global SWAP

Let psi_+=(|0^n>+|1^n>)/sqrt(2) and
psi_-=(|0^n>-|1^n>)/sqrt(2). They are orthogonal, yet their density matrices
have identical marginals on EVERY proper subset of the n data qubits.
Thus psi_+ tensor psi_+ and psi_+ tensor psi_- have identical marginals
on every set of fewer than n sites of the two literal registers.

Every sum of k<n-local observables has identical expectation on these
two states. The same holds for a qualified measured-index adaptive
q<n-query verifier: each complete-path effect accesses a proper subset
of each register, so its probability is identical. A global SWAP instead
accepts the equal pure pair with probability1 and the orthogonal pair
with probability1/2. This rules out the literal, unencoded replacement
of that comparator by fewer-than-n data queries, not Quantum PCP.
Encoding, additional checked proof structure and input-dependent
constructions are outside this restricted control.

## Q18. An elementary trace gate for overly strong query parameters

For a GIVEN q-query measured-index verifier, its accepting effect E is a
sum of positive effects on at most q proof qubits. For every positive
q-local effect A on N qubits,
||A||<=Tr_local A<=2^q Tr(A)/2^N.
Consequently ||E||<=2^q Tr(E)/2^N, by triangle inequality and positivity.
If a YES input admits acceptance >=c, the maximally mixed proof accepts
with probability at least c/2^q. On a NO input it accepts at most s.
When c/2^q-s has a positive inverse-polynomial lower bound, sampling this
explicit mixed proof distinguishes the input in BQP. If ALL QMA had such
verifiers with these parameters, this would imply QMA=BQP; no separation
is asserted. The original existential parameters need not satisfy this
strong inequality, so this is not a refutation of QP0.

The analogous Hamiltonian calculation is also exact. For
H=(1/M)sum_i h_i, 0<=h_i<=I, at most q sites of dimension d,
A=I-H is a sum of positive q-local effects. If lambda_min(H)<=a then
Tr(H)/d^N<=1-(1-a)/d^q. If lambda_min(H)>=b then Tr(H)/d^N>=b.
Thus b>1-(1-a)/d^q, with an efficiently resolvable margin, makes that
particular promise distinguishable by the explicitly computable trace.
It does not cover arbitrary constant-relative-gap thresholds.

One cannot improve the query budget for free by ordinary error reduction.
For a t-copy accepting-AND procedure the acceptance ratio changes from
s/c to (s/c)^t, while the queried proof size becomes tq; comparison with
2^(-tq) retains the same exponent inequality. General majority
amplification also increases the query bound. This restricted calculation
does not preclude a more efficient structural error reduction.

## Q19. Keep the quantum reduction qualification in complexity consequences

QP0 permits quantum polynomial-time reductions, not just classical
deterministic transformations. A smaller classical target class therefore
cannot automatically be composed using the closure facts for classical
reductions. For example one cannot infer that LH in NP refutes QP0 merely
by assuming QMA differs from NP. The precise reduction convention and
the simulation of its quantum output computation must be supplied.
An arbitrary BQP computation with an NP oracle gives a BQP^NP upper
bound; a suitable fixed quantum-output transformation followed by a
classical-certificate test can give QCMA under its actual error/size
conditions. Neither statement proves a needed class separation.

BHW's conditional QPCP-to-QCMA theorem is an attributed prior result.
Only the actual statement and selected learning/rounding/oracle passages
listed in the source record were read, not its entire proof. Q13's own
random tomography outputs need not coincide across successful runs.
No unique successful classical-output certificate is asserted here, and
no generic closure of QCMA under arbitrary random quantum reductions is
adopted. The following direct witness-validation route states its own
qualification instead.

## Q20. A known conditional QPCP-in-QCMA bridge via witness validation

Assume the constant-relative-gap Local Hamiltonian problem at the relevant
fixed locality and local dimension is in QCMA. Given a constant-query
QPCP verifier with c>s and q fixed, its rejection effects R_p are as in
Q13, with R=sum_p R_p=I-E_accept and D0=2^q.
Put nu=(c-s)/100. Merlin supplies a polynomial-bit classical packet
of rational Hermitian PSD matrices C_p on the known path supports, plus
a classical QCMA certificate for the local Hamiltonian specified below.
Check their local positivity exactly in constant dimension and require
S=sum_p Tr_local C_p<=2D0. Then U=max(1,S) and
H_C=(sum_p C_p)/U define a valid PSD local operator 0<=H_C<=I.

Its absolute thresholds are
a=(1-c+4nu)/U, b=(1-s-4nu)/U,
with gap >=(c-s-8nu)/(2D0).
Q12 converts this to a polynomial explicit norm-one multiset having a
constant relative gap at the same locality (or q+1 if an optional
distinct-support convention requires flags). All factors and thresholds
are rational functions of the packet. Only a classical polynomial-time
transformation is needed after the packet has been supplied.

A quantum verifier with NO quantum witness independently learns all
R_p to the following cumulative entry norm within nu/4, with failure
probability delta=.01:
Delta_row(A,B)=sum_p D0 max_(u,v)
              (|Re(A_p-B_p)_(uv)|+|Im(A_p-B_p)_(uv)|).
This dominates sum_p ||A_p-B_p|| and obeys triangle inequality.
Constant local dimension and polynomially many paths make the sampling
and precision polynomial, using the path-local tomography from Q13.
The learning-good event controls all packets simultaneously.
Accept a supplied packet for further checking only if
Delta_row(C,estimated_R)<=nu.

For honest YES there exist PSD rational packets with
Delta_row(C,R)<=nu/4 and S<=2D0: sufficiently precise PSD-shifted
tomography as in Q13 supplies such matrices with polynomial bit length.
These pass validation on the good event and
lambda_min(sum C_p)<=1-c+nu/4<aU.
For ANY accepted packet on that event,
||sum C_p-R||<=5nu/4<2nu.
A NO input consequently satisfies
lambda_min(sum C_p)>=1-s-2nu>bU, so the derived packet instance is
genuinely in the NO branch even though Merlin selected the packet.

Run the hypothesized QCMA verification algorithm on this explicit
constant-gap instance, using the remaining classical certificate.
Its error may be amplified to delta using the same classical
certificate and fresh verifier workspace. For YES there is an honest
packet and certificate succeeding with probability >=1-2delta.
For NO every certificate succeeds with probability <=2delta,
including the learning-failure contribution. This is a uniform QCMA
verifier and proves the stated CONDITIONAL containment for the qualified
QPCP model. It avoids requiring identical random Hamiltonian outputs.

This is a rederivation of a known conditional bridge, not a new major
result. The assumption that all constant-gap LH is in QCMA is not proved,
nor is an all-QMA constant-query verifier constructed. The complete QP0
gates are unchanged.


## Q21. Direct positive compression estimate and its remaining depth loss

Let 0<=h<=I and let G<=P be nested projections with
P h P>=g(P-G), g>0. For any density operator rho set
alpha=Tr(h rho) and eta=Tr((I-P)rho). Purify rho, if necessary.
The triangle inequality gives
||sqrt(h)P psi||<=(sqrt(alpha)+sqrt(eta)).
Consequently
Tr((I-G)rho)<=eta+(sqrt(alpha)+sqrt(eta))^2/g.
In particular the upper bound is
(1+2/g)eta+2alpha/g. No independent spectral gap of h is needed.
For any t>0 one can also use
[1+(1+1/t)/g]eta+[(1+t)/g]alpha.
This is a direct all-state operator inequality, including arbitrary
entanglement with an external reference.

Apply it CONDITIONALLY to the displayed ABN compressed propagation
formula (their Eq56, actually read), not to an unproved global decoder.
Write L=4^k, u=L^(-1/2)sum_e |e>, D=Lambda^tensor k with
Lambda=diag(delta,1,1,1), 0<delta<=1.
The compressed matrix is
C_k D(I-|u><u|)D, C_k=L delta^(2k)/(1+3delta^2)^k.
Its kernel is the span of phi_0^tensor k, since it is D^(-1)u.
The nonzero spectrum of D(I-uu^*)D equals that of
(I-uu^*)D^2(I-uu^*) restricted to u-perpendicular.

D^2 has its unique smallest entry delta^(2k) at the all-I coordinate,
and every other entry is at least delta^(2k-2). For a unit vector
y perpendicular to u, Cauchy-Schwarz gives |y_0|^2<=(L-1)/L.
Therefore the nonzero compressed gap has the explicit lower bound
g_k(delta)>=
delta^(4k-2)[1+(L-1)delta^2]/(1+3delta^2)^k.
Using P for the right k good resource pairs and G for both sides good,
the preceding general inequality transfers purity with this g_k.
For k=1 the compressed gap is exactly delta^2.

For completeness the small-delta exponent can be determined directly.
The weights delta^(2(k-r)) have multiplicities binomial(k,r)3^r.
The determinant lemma shows that the lowest nonzero eigenvalue lambda
of D(I-uu^*)D is the unique root between delta^(2k) and
delta^(2k-2) of
sum_(r=0)^k binomial(k,r)3^r/[delta^(2(k-r))-lambda]=0,
for 0<delta<1. Scale lambda=c delta^(2k-2); as delta tends to0,
the first two groups give -1/c+3k/(1-c)=0, and the remaining groups
vanish in the scaled equation. Monotone bracketing around the unique
root yields c tending to1/(3k+1). Thus the exact compressed gap is
[4^k/(3k+1)+o(1)]delta^(4k-2).
At delta=1 all nonzero eigenvalues of the compressed matrix are1.

For k=2, putting e=delta^2, the two exceptional eigenvalues of
D(I-uu^*)D have characteristic polynomial
z^2-[(15e^2+10e+7)/16]z+e(1+3e)^2/16.
The remaining nonzero eigenvalues are e (multiplicity5) and1
(multiplicity8). The grouped determinant numerator
(z-e)(z-1)+6(z-e^2)(z-1)+9(z-e^2)(z-e)
was independently expanded symbolically and matched this polynomial
after multiplication by16, residual0. This algebraic control does not
certify a full Hamiltonian reduction.

These estimates improve a SINGLE transfer step. Their direct repeated
bounds still multiply the downstream error by a factor greater than1.
They do not establish a depth-independent energy-density-to-fault bound,
an efficient decoder, or the uniform full-QP0 constant promise gap.
No restricted circuit class is promoted to a major result.

## Q22. Local postselection escape for a sparse output-check template

Let H_parent=sum_i h_i be a frustration-free parent Hamiltonian with
M positive contraction terms, and H_out=sum_j o_j have P positive
contraction terms supported inside a region R. Let K_R project onto
their common kernel. Suppose some parent ground state psi satisfies
K_R psi !=0. Then phi=K_R psi/||K_R psi|| has zero output energy.
Every parent term disjoint from R commutes with K_R, so it still
annihilates phi. If B_R is the set of parent terms meeting R,
the variational principle gives
lambda_min((H_parent+H_out)/(M+P))<=|B_R|/(M+P).
No lower bound on the postselection probability is required: the remaining
term expectations are at most1 on the NORMALIZED phi.

Thus a bounded-degree parent with a small accessible accepting region
cannot obtain a constant normalized NO energy from this template
whenever the accepting projection has nonzero ground-state weight.
Repeating the same output penalty does not remove the displayed escape.
A construction can evade the premise by macroscopic protected readout,
different parent structure, or an accepting kernel orthogonal to its
whole ground space. This is not a general Quantum PCP impossibility.

The related elementary count bound is also useful: any parent ground
state has total output energy at most P, so the normalized minimum is
at most P/(M+P). A spectral gap of the parent alone does not change
these variational bounds. Full energy soundness must handle all states,
not only the honest parent ground states.

## Q23. Mixed-channel Choi support alone permits selective branches

For a channel M(rho)=sum_a K_a rho K_a^*, its Choi support is spanned by
the vectorizations |K_a>>. A projector penalty checking only membership
in that support also accepts each nonzero individual |K_a>>.
That resource corresponds, up to scaling, to the selective submap
rho -> K_a rho K_a^*, which need not be trace preserving.

For example dephasing has Kraus operators |0><0| and |1><1|.
Its Choi support is span{|00>,|11>}. The pure resource |00> passes
the support penalty and implements selection of the0 branch.
More generally any PSD penalty having EXACT zero expectation on a
mixed Choi state must annihilate every vector in its support, by
positivity. Hence extra zero-energy support checks on that mixed
state alone cannot enforce its decomposition weights.

This obstructs a proposed substitution of general measured/adaptive
processes by checks of mixed Choi support only. A purified environment,
proper branch consistency or protected syndrome construction can change
the premise. No fully general Clifford/instrument compiler or QP0
impossibility follows. BGV's actual fault formalism explicitly handles
certain nonphysical faults and postselected classical-function gates;
it cannot be replaced by a naive independent-noise argument.

## Q24. Merely coding the measurement record does not amplify its energy

Consider the specific record template with a data projector Pi_i and
a corresponding flag f_i:
A_i=(I-Pi_i) tensor|1><1|_(f_i)+Pi_i tensor|0><0|_(f_i).
It is a positive (k+1)-local projector enforcing the sharp check's
data/flag relation. Suppose additional classical encoding/check terms
on the flags and auxiliaries are frustration-free on the all-zero
record, with some auxiliary zero-record state z.

For every data state rho, rho tensor|0...0><0...0| tensor|z><z|
has consistency energy sum_i Tr(Pi_i rho), and zero classical energy.
The variational minimum of the combined normalized Hamiltonian is
therefore at most lambda_min(sum_i Pi_i)/M_total.
The encoding can be arbitrarily redundant; the all-zero sector remains.

This direct record-only construction leaves the original small quantum
energy in place. It does not invalidate ABN's different coherent tensor
network, nor every possible coding/assignment-testing construction.
Input-dependent threshold computation or additional quantum checks
must be analyzed separately; no generic permitted quantum reduction is
refuted by this template calculation.

## Q25. Exact support flattening can destroy general-QMA completeness

The two-projector input of Q2 also gives a fully legal inverse-polynomial
promise control. For every integer N>=4 pad to N qubits, using
H_delta=P_0+P_delta on one qubit and identity extension on the rest.
All entries have polynomial rational descriptions.
lambda_min(H_delta)=1-1/sqrt(1+delta^2).

Use common thresholds a=1/(4N^2), b=1/(2N^2).
For delta_Y=1/(2N), lambda_min<=delta_Y^2/2=1/(8N^2)<a.
For delta_N=2/N,
lambda_min>=delta_N^2/[2(1+delta_N^2)]
=2/(N^2+4)>b.
Both inputs have the same inverse-polynomial absolute promise gap b-a.

For both positive deltas the exact support projector of the local
sum H_delta is I. Thus replacing that local sum by its zero-cutoff
support projector produces the SAME operator for the legal near-zero
YES and NO pair. A branch-independent common output-threshold rule
cannot distinguish them with a constant gap.
This is a failure of that exact-kernel flattening recipe, not arbitrary
spectral cutoffs or input-dependent quantum reductions. The variable
constraint set is not a counterexample to BNZ's stated fixed-set theorem.

## Q26. Numerical accuracy is not fixed-output coarse rounding

Absolute scalar estimation error alone does not determine a fixed
coarse binary prefix without a boundary margin. At p=1/2, take
a Bernoulli sample mean from M=2r fair trials. The probabilities of
being below and above p are each
[1-binomial(2r,r)/4^r]/2.
Both tend to1/2 even while the estimation error tends to0.
With arbitrarily high probability the estimate is inside any fixed
small neighborhood of p, yet ordinary binary truncation returns the
two codes on opposite sides of this boundary. The same elementary
issue occurs at a boundary of any interval coarse quantizer.

The displayed BHW Algorithm1 variation and complete AppendixC were
actually read, including the pinned v3 PDF pp51-52.
Their numerical-error-to-correct-prefix step is not adopted as a
certified unique-output argument here. This is a direct control of
that simple inference, not a refutation of the conditional containment
theorem or an independent full-paper audit. Our Q13 is a randomized
common-witness reconstruction component; it need not always output
the same Hamiltonian. Q20's explicit classical-packet validation proves
its own conditional containment without relying on that property.
A full QP0 construction must meet its chosen quantum-reduction convention.

## Q27. A complete sufficient energy criterion, with its core unproved

Suppose a uniform polynomial-time construction for ALL QMA promises
produces constant-locality/dimension positive contraction term lists
H_P=(1/M)sum_i p_i and H_O=(1/P)sum_j o_j.
Assume there are fixed known positive rational epsilon_0,beta_0 such that:
in every NO input, for EVERY global density operator rho,
Tr(H_P rho)<=epsilon_0 implies Tr(H_O rho)>=beta_0.
Assume every YES input has a state with both energies <=eta, where
eta<=min(epsilon_0,beta_0)/8.
Polynomial description/precision, and the intended reduction-success
convention, are part of the construction hypothesis.

Then F=(H_P+H_O)/2 has YES energy <=eta.
For any NO state either its parent energy exceeds epsilon_0, or its
output energy is at least beta_0; therefore its F energy is at least
min(epsilon_0,beta_0)/2. The gap is at least
3 min(epsilon_0,beta_0)/8, a universal positive constant.

There is an exact equally weighted list realization: make P copies of
each parent term and M copies of each output term. Its2MP terms are
still positive contractions at the same constant locality/dimension
and its normalized sum is F. This polynomial duplication fixes the
relative list sizes WITHOUT supplying the unproved energy premise.
Distinct-support conventions can use the optional Q12 flags.

This conditional criterion covers general near-perfect completeness
rather than requiring exact-zero QMA1. It identifies the needed
all-state physical soundness statement. Q21's propagated bounds, BGV's
fault-tolerance theorem with classical-side and vanishing-fraction
qualifications, BNZ's combinatorial theorem, and the read ABN
ground-space spectral comparison do not establish this premise.
The criterion is an elementary sufficient condition, not a solution.

## Final complete-stage outcome: full QP0 remains unresolved here

The SAME original stage ended2026-10-14T10:11:06Z at7201effective
seconds (120m01), including230premap primary seconds and6971seconds
of mathematics/relevant source followup. All recovery/preservation
intervals are recorded separately; requested service time was0.
No full reduction, proof, complexity separation or refutation was obtained.
The four complete gates remain:
1. Every general-QMA promise, without substituting exact-zero/QMA1.
2. True expectation-energy soundness against every coherent/entangled state.
3. Constant locality/dimension and polynomial construction/precision,
   without an unproved code/instant-decoder or reduction-output convention.
4. Static noninteractive proof/Hamiltonian consistency, without replacing
   it by an interactive, game, cryptographic, or classical-flag surrogate.

Q1-Q27 are auxiliary controls, conditional criteria or explicitly
attributed/rederived prior bridges. They do not increment the count of
complete major problems solved. No new Lean/kernel/full-primary audit,
external message or publication was performed by this role.
Under the explicit finish-current-task instruction this role now
preserves its material, reports to the parent, and becomes idle.
No new target is activated or screened pending explicit user resume.
