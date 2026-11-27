# Optimal one-way fidelity in equal-dimension blind stabilizer recovery

## 1. Setting and claim

A prime-\(p\) stabilizer code has an isometric encoder \(W:Q\to ABC\),
where \(Q\) consists of \(m\ge1\) \(p\)-level qudits. The target \(B\)
also consists of exactly \(m\) such qudits; let \(d=p^m\).
The helper \(A\) and the unavailable region \(C\) may contain any
number of qudits. We assume erasure of each of \(A,B,C\) separately
is exactly correctable. In a blind helper scheme with at least two
ordinary shareholders, take \(A\) to be the helper, \(B\) any target
of the specified size, and \(C\) the other shareholders. Blindness
gives recovery by \(BC\), the helper with the target gives recovery by
\(AB\), and the helper with any other shareholder gives recovery by
\(AC\). This verifies all three assumptions. The same conditions can
also be considered directly with a grouped target that can operate
jointly within \(B\).

The one-way procedure consists of an arbitrary POVM by \(A\)
with a finite classical message \(y\) sent to \(B\), then an
arbitrary CPTP recovery \(\Lambda_y:B\to Q\). Local ancillas
and any local refinement of the measurement can be absorbed in
this description. If the helper groups private outcomes, \(y\)
and its summed effect are the actual message and POVM effect.
No additional shared entanglement, access to \(C\), postselection,
or reply from \(B\) is permitted. Mixing strategies by independent
shared classical randomness cannot improve a fixed-alphabet fidelity
upper bound, since the fidelity is affine in the resulting channel.

The figure of merit is the entanglement fidelity for the maximally
mixed secret: use \(|\Phi\rangle_{RQ}=d^{-1/2}\sum_i|i,i\rangle\),
and take the average over all actual messages of the conditional
output overlap with \(\Phi=|\Phi\rangle\langle\Phi|\).
This is the squared fidelity with the pure normalized reference
state, not its square root.

The full logical Pauli space is \(\mathcal L\), dimension \(2m\)
over \(\mathbb F_p\), with symplectic form \(\Omega_\mathcal L\).
The next section defines a canonical linear isomorphism
\(b:\mathcal L\to V_B\).
Set
\[
 D(v,w)=\Omega_B\big(b(v),b(w)\big)-\Omega_\mathcal L(v,w),\quad
 2r=\operatorname{rank}D,\quad q=2m-r.                         \tag{1}
\]

**Theorem.** With at most \(L\ge1\) possible classical messages
the optimal entanglement fidelity equals
\[
                  F_e^{(L)}=\min\{p^{-r}, L/d^2\}.             \tag{2}
\]
Unconstrained optimum is \(p^{-r}\), with minimum support
\(p^q\) and minimum Shannon entropy \(q\log_2 p\) of the
sent message among deterministic choices of procedure (or
conditional on any freely preshared classical seed). Perfect
recovery is equivalent to \(r=0\).

## 2. Cleaning and uniqueness of the target projection

For each region \(J\), \(V_J\) denotes its Pauli-label space,
embedded in the full label space \(V=V_A\oplus V_B\oplus V_C\).
Use the convention
\(\Omega((x,z),(x',z'))=z\cdot x'-x\cdot z'\), so for
\(P(x,z)=X^x Z^z\) the commutator phase is
\(\omega^{\Omega((x,z),(x',z'))}\), \(\omega=e^{2\pi i/p}\).
All statements concerning labels are independent of scalar Pauli
phases. Let \(S\subset V\) be the stabilizer subspace and
\(S_J=S\cap V_J\). Then \(\mathcal L=S^\perp/S\) and its
symplectic form is the induced nondegenerate one.

Erasure of \(J\) is correctable exactly when
\(S^\perp\cap V_J=S_J\). Indeed the Pauli operators on \(J\)
span its operator algebra. Their compression to the code is
zero outside \(S^\perp\), a scalar for stabilizers, and a
nonidentity logical operator for labels in \(S^\perp\setminus S\).
This is the erasure Knill–Laflamme condition. For completeness,
a scalar-compression condition on every operator of the erased
system is equivalent to its reduced channel being constant:
all output expectation values are scalar times input trace.
Its complement on retained systems is then reversible, which can
be seen by Schmidt decomposing the code basis vectors against the
common erased state. The off-diagonal matrix elements of the
erased channel vanish: the retained Schmidt vectors for distinct
codewords and positive Schmidt indices are mutually orthogonal.
A local isometry on the retained part sends them to the logical
basis times the Schmidt index, and discarding the index recovers
the input. The converse follows because a recovery of a unitary
identity channel leaves its environment independent of the input,
as is immediate from a purification of the identity Choi state.

Since \(C\) erasure is correctable, every logical label has a
representative supported on \(AB\). To verify the cleaning step,
let \(\pi_C\) be coordinate projection. In the nondegenerate
space \(V_C\), \((\pi_C S)^\perp=S^\perp\cap V_C=S_C\).
For \(\ell\in S^\perp\), the projection \(\pi_C\ell\) is orthogonal
to \(S_C\), so it is in \(\pi_C S\) by taking the double
orthogonal. Subtract a stabilizer with that projection.

On representatives supported on \(AB\), the \(B\)-projection
defines a map
\(\mathcal L\to V_B/\pi_B(S_{AB})\).
It is independent of the representative because differences
are in \(S_{AB}\). It is injective: if the \(B\)-projection
vanishes in this quotient, subtract an \(AB\)-supported stabilizer
to clean it off \(B\) too, leaving a representative on \(A\).
Since erasure of \(A\) is correctable, such a label is trivial
in \(\mathcal L\). The source and \(V_B\) both have dimension
\(2m\). Thus \(\pi_B(S_{AB})=0\), or
\(S_{AB}=S_A\); in particular \(S_B=0\).
The induced \(B\)-projection \(b:\mathcal L\to V_B\) is
therefore an isomorphism, without any representative ambiguity.

Choose a linear section of cleaned representatives into
\(S^\perp\cap V_{AB}\), and denote its \(A\)-part by \(a_v\).
Each \(a_v\) is orthogonal to \(S_A\). The induced map
\(\mathcal L\to S_A^\perp/S_A\) (orthogonal taken within \(V_A\))
is injective: if \(a_v\in S_A\), remove it by a stabilizer,
leaving a logical representative on \(B\), which is trivial
because erasure of \(B\) is correctable.
The commutator identity of cleaned representatives gives
\[
                    \Omega_A(a_v,a_w)=-D(v,w).              \tag{3}
\]

## 3. The conditional twisted Pauli algebra

Choose a logical Pauli unitary \(U_v\) for each \(v\), with
identity at zero, and choose Pauli operators \(A_v,B_v\) of
labels \(a_v,b(v)\) whose product implements \(U_v\) on the code.
This only fixes the combined scalar phase. On basis labels
used for simultaneous measurements one can choose \(U_v,B_v\)
of order \(p\) and assign the residual scalar to \(A_v\), so
\(A_v\) is of order \(p\) as well. In characteristic two the
usual rephasing to Hermitian binary Paulis is allowed.
The code's pure Choi state has stabilizers
\(U_v^*\otimes A_v\otimes B_v\), with identity on \(C\), since
\((U_v^*\otimes U_v)|\Phi\rangle=|\Phi\rangle\);
here * is entrywise complex conjugation in the reference basis.
Let \(P_A\) be the stabilizer projection associated to \(S_A\)
on the helper, with \(d_A'=\operatorname{Tr}P_A\).
Put \(H_v=U_v^*\otimes B_v\) on \(RB\). Then, ordering the tensor
factors as \(RB,A\), the reduced Choi state is
\[
          \rho_{RBA}=\frac1{d^2 d_A'}\sum_{v\in\mathcal L}
                              H_v\otimes P_A A_v.            \tag{4}
\]
To get this formula, expand the Choi stabilizer projector as the
average over the code stabilizers together with the \(2m\)
independent logical Bell generators. Tracing out \(C\) keeps
exactly those elements trivial there. For each reference label
\(v\), the retained elements are the chosen cleaned representative
times all elements of \(S_{AB}=S_A\). The stabilizers with
label in \(S_A\) sum to \(|S_A|P_A\), where \(|S_A|\) denotes
cardinality \(p^{\dim S_A}\); normalizing gives (4).
For \(v\ne0\), \(a_v\notin S_A\), so
\(\operatorname{Tr}(P_A A_v)=0\) by Pauli trace orthogonality.
It follows that
\[
                           \rho_{RB}=I/d^2.                  \tag{5}
\]
This also follows from privacy of \(B\) and \(S_B=0\).

Each actual message effect \(E_y\) leaves an unnormalized
conditional state \(\sigma_y\) on \(RB\) obtained by inserting
\(E_y\) in the helper trace in (4).
It is positive, \(\sum_y\sigma_y=I/d^2\), and
\(p_y=\operatorname{Tr}\sigma_y=\operatorname{Tr}(E_yP_A)/d_A'\).
If \(p_y>0\), \(\rho_y=\sigma_y/p_y\) is a density operator
in the algebra \(\mathscr A=\operatorname{span}\{H_v\}\).
The \(H_v\)'s are projective Pauli products with independent
labels (their \(R\)-part is injective), multiply up to
scalar with label \(v+w\), and have commutator form \(D\).
Consequently their span is a unital *-algebra. Every nonidentity
\(H_v\) is traceless.

Here is the needed spectral structure without an irreducibility
assumption. Take a basis of the radical of \(D\), dimension
\(2m-2r\), and phase its \(H_v\)'s to order \(p\).
They commute with the whole algebra. Every joint eigenspace
has dimension \(d^2/p^{2m-2r}=p^{2r}\): its character-average
projector has that trace because all nonzero Pauli labels are
traceless. On each such space, symplectic pairs for a complement
to the radical give \(r\) commuting shift operators and \(r\)
commuting clock operators with standard Weyl commutation.
The simultaneous clock eigenspaces are cyclically permuted
by the shifts. They therefore all have the same dimension
\(p^{2r}/p^r=p^r\). Choosing a basis of the first eigenspace and
transporting it by those commuting shifts writes the nondegenerate
Weyl generators as clock and shift matrices on a \(p^r\)-dimensional
factor tensored with the identity on a multiplicity space of
the same dimension. The generators of the radical are scalars
on this joint eigenspace. Thus the algebra acts blockwise as
\({\rm M}_{p^r}\otimes I_{p^r}\).
Equivalently every eigenvalue within any block occurs with
multiplicity at least \(p^r\).
Since the normalized conditional \(\rho_y\) has trace one,
\[
                         \|\rho_y\|_\infty\le p^{-r}.        \tag{6}
\]

For a CPTP \(\Lambda_y\), the positive operator
\(T_y=(\mathrm{id}_R\otimes\Lambda_y^\dagger)(\Phi)\)
has trace one: using \(\operatorname{Tr}_R\Phi=I_Q/d\) and
unitality of the adjoint gives
\(\operatorname{Tr}T_y=\operatorname{Tr}I_B/d=1\).
Equal secret and target dimensions are important here.
By (5) and (6) the message's fidelity contribution obeys
\[
        \operatorname{Tr}(\sigma_y T_y)
                  \le\min\{1/d^2,\ p_y p^{-r}\}.             \tag{7}
\]
Summing proves the upper bound (2) for any allowed measurement
or receiver map, with private outcomes already coarse-grained.
Equality at the unconstrained optimum requires
\(p_y p^{-r}\le1/d^2\) for each positive message, so \(p_y\le p^{-q}\).
Consequently there are at least \(p^q\) such messages and
\(H(Y)=\sum_y p_y\log_2(1/p_y)\ge q\log_2 p\).
The same statement holds conditional on a freely preshared seed
at equality, since the optimum bounds every conditional procedure.

## 4. Attainment by commuting Pauli measurements

Choose a maximal \(D\)-isotropic subspace \(K\subset\mathcal L\)
of dimension \(q=2m-r\): take the radical together with one
vector from each of \(r\) nondegenerate symplectic pairs. Let
\(v_1,\ldots,v_q\) be a basis. By (3) the corresponding \(A_{v_i}\)
commute, so the helper can jointly measure them, after assigning
the order-\(p\) phases described above. All \(p^q\) eigenvalue
tuples have probability \(p^{-q}\) on \(A\), since the code Choi
marginal on \(A\) is \(P_A/d_A'\) and any nontrivial product
of the \(A_{v_i}\)'s has label outside \(S_A\).
In the Choi state, every \(H_{v_i}\otimes A_{v_i}\) stabilizes
the state. Thus each such outcome \(y\) leaves the \(RB\)
state supported on the reciprocal joint eigenspace of the
commuting \(H_{v_i}\). Those \(p^q\) eigenspaces are orthogonal,
each of rank \(d^2/p^q=p^r\) by the Pauli trace argument.
The normalized state on that space is precisely the corresponding
projection divided by \(p^r\): it has trace one and (6) bounds
every eigenvalue by \(p^{-r}\).

For each outcome the target can choose a unitary mapping a
maximally entangled vector in this projection to \(|\Phi\rangle\).
Indeed, \(b(v_i)\mapsto v_i\) preserves the symplectic form
on the subspaces \(b(K)\) and \(K\) since \(D|_K=0\).
An isometry between subspaces of a nondegenerate alternating
space extends to one of the full symplectic spaces, including
for degenerate subspaces and \(p=2\). To see this, choose a
symplectic basis for the nondegenerate part of the subspace and
then a basis of its radical. In the orthogonal complement of
the first part choose partners dual to the radical vectors.
The partners may be made mutually orthogonal by adding linear
combinations of radical vectors (adjust one off-diagonal entry
at a time, using their duality); the resulting hyperbolic pairs
can then be completed by a symplectic basis of their nondegenerate
orthogonal complement. Perform the same extension for the
image basis and map the full bases to each other.

A symplectic isometry of the Pauli-label spaces is implemented
by a Clifford unitary: after rephasing the images of the standard
shift and clock generators to order \(p\), they obey the same
commutation relations. Their joint clock eigenbasis has one
vector per eigenvalue tuple (by the same Pauli trace argument),
and transporting one vector by the commuting shifts constructs
a unitary identification with the standard representation.
If the secret's given encoding basis differs from the chosen logical
Pauli basis, follow this identification by the fixed basis conversion
into the given secret basis; \(U_{v_i}\) below acts in that basis.
Thus this fixed identification on \(B\) brings \(H_{v_i}\) to
\(U_{v_i}^*\otimes U_{v_i}\) up to phases that are \(p\)th roots
of unity. A Pauli on the output then adjusts the eigenvalue of
each of these commuting correlations to one.
Indeed commutation with the independent \(v_i\)'s gives a
surjective linear map from Pauli labels to \(\mathbb F_p^q\)
by nondegeneracy, so every required eigenvalue tuple is realizable.
The order-\(p\) phase convention ensures there are no additional
phase cases. The resulting support contains \(|\Phi\rangle\)
because every \(U_{v_i}^*\otimes U_{v_i}\) fixes it.
This attains conditional fidelity \(p^{-r}\).

For an alphabet smaller than \(p^q\), divide the \(p^q\)
outcomes into \(L\) nonempty groups and send only the group
label. In each group the target applies the unitary for one
chosen representative outcome. The pullback of \(\Phi\)
under that decoder lies in the representative eigenspace,
orthogonal to all other eigenspaces in the group. Thus its
unconditional contribution is exactly
\(p^{-q}p^{-r}=1/d^2\) per group, giving \(L/d^2\).
If \(L\ge p^q\), send the ungrouped outcome. This proves
(2) in both regimes, including the message entropy and
support optima. For \(r=0\), unit entanglement fidelity
means the output Choi state is \(\Phi\), hence the corrected
channel is exactly the identity.

## 5. Source examples and a printed Pauli correction

When \(p=2,m=1\), every invertible map on the two-dimensional
label space is symplectic: any such map has determinant one
in \(\mathbb F_2\). Thus \(r=0\), four messages suffice,
and fewer cannot give perfect recovery, agreeing with the
setting of the previously established single-target recovery
in Chitambar et al., arXiv:2609.00234v1, Corollary 2.

For the qutrit Example 3 of that work (PDF p. 6), use
column order \(A_1,A_2,B_1,B_2,B_3\).
The printed fourth stabilizer row ends with \(Z\).
With the Pauli convention above, it has symplectic pairing
\(2\) with the second stabilizer row in the order
(second, fourth), so the printed rows do not all commute.
Keep the other rows and both printed logical rows fixed.
Changing the final entry of the fourth row to \(X\) gives
the following commuting code data, where the last two rows
are logical generators:
\[
\begin{array}{c|cc|ccc}
 & A_1&A_2&B_1&B_2&B_3\\ \hline
 S_1&Z&Z&X&X&I\\
 S_2&XZ^{-1}&X^{-1}Z^{-1}&I&X&Z\\
 S_3&X&X&XZ&XZ&I\\
 S_4&Z&XZ^{-1}&I&XZ&X\\ \hline
 \ell_1&I&I&X^{-1}Z^{-1}&XZ&X\\
 \ell_2&I&I&XZ^{-1}&X^{-1}Z&XZ
\end{array}
\]
The small exact check verifies this is the unique change of
one entry of row 4 compatible with those fixed rows.
It also verifies stabilizer dimension four, centralizer
dimension six, and logical minimum weight three: the span
of the six displayed rows has \(729\) labels and the
stabilizer span has \(81\). Every logical coset outside
the stabilizer has minimum weight at least three, with
equality somewhere. Thus erasure of any two qutrits is
correctable. The two logical rows have pairing \(1\).
Cleaning off the two non-target Bobs gives the following
unique \(B_i\)-pairs, in exponent coordinates \((x,z)\)
over \(\mathbb F_3\):
\[
\begin{array}{c|cc|c|c}
 \text{target}&b(\ell_1)&b(\ell_2)&\Omega_B&F_e^{(\infty)}\\\hline
 B_1&(2,2)&(1,2)&1&1\\
 B_2&(1,1)&(2,1)&1&1\\
 B_3&(2,0)&(2,2)&2&1/3
\end{array}
\]
For \(B_1,B_2\), the cleaned helper spans equal the commuting
measurement spans identified in the source.
The source's \(B_3\) discussion excludes the analogous
Pauli-pair measurement; applying the theorem to the
corrected code proves the exact optimum \(1/3\) among
all allowed helper measurements and receiver maps.
This calculation is separate from the proof of the theorem.

## 6. Effective helper-size bound and its attainability

The number of effective helper qudits is
\(n_A-\dim S_A\), since the local stabilizer support
has that logarithmic dimension in base \(p\).
The injective image of \(\mathcal L\) in \(S_A^\perp/S_A\)
has dimension \(2m\) and form \(-D\), by (3).
Its radical, of dimension \(2m-2r\), belongs to its own
orthogonal complement in the nondegenerate quotient.
It follows that \(n_A-\dim S_A\ge2m-r=q\).

This lower bound is realizable for any prescribed isomorphism
\(b:\mathcal L\to V_B\) with both spaces of dimension \(2m\).
Embed the presymplectic space \((\mathcal L,-D)\) injectively
into \(q\) helper qudits' Pauli space, using \(r\) full
hyperbolic pairs for the nondegenerate part and \(2m-2r\)
independent clock axes for the radical. For a basis of
\(\mathcal L\), define \(2m\) order-\(p\) Pauli stabilizers on
\(RAB\) with labels \((U_v^*,a_v,b(v))\). They commute because
the three alternating forms sum to zero, and are independent
by their reference labels. Their normalized projector has
rank \(p^q\). Purify it on \(q\) additional qudits \(C\) by a
stabilizer purification: map the commuting generators to \(2m\)
standard clock axes by the symplectic basis extension and
Clifford construction above, set those qudits in fixed
eigenstates, and purify each of the remaining \(q\) maximally
mixed qudits by a Bell pair. Undo the Clifford on \(RAB\).
The resulting pure stabilizer state is a code Choi state:
the reference is maximally mixed, and the subgroup with
trivial \(R\) has rank equal to the number of physical
qudits minus \(m\), since the \(R\)-projection is onto.
Equivalently the isometry obtained from its reference Schmidt
decomposition lands in the code space of that physical subgroup.

Here \(RA\) and \(RB\) are products by Pauli trace orthogonality
and injectivity of the \(B\)- and \(A\)-projections. Also \(RC\)
is a product: tracing out \(AB\), the stabilizers
\(U_v^*\otimes A_v\otimes B_v\) force invariance under
all reference Pauli conjugations, which makes the reference
maximally mixed and independent of \(C\). So all three
erasures are correctable by the argument of Section 2.
There is no \(A\)-only stabilizer, and by construction the
target map is the desired \(b\). This establishes the claimed
effective helper-size optimum within this three-region code
setting, not a claim about uniform share size for every
multi-target access structure.
