# Efficient extraction of the optimal integer number of Bell pairs from unknown pure two-qubit inputs

Author addendum v2, 16 October 2026. Ordinary written proof pending independent read, not Lean or external peer-review certification. The general mixed-state construction is still not asserted to have an efficient ancilla-free implementation. This is a separate pure-promise protocol, not a circuit implementation of the earlier all-state family.

## 1. Statement and resource accounting

Let k>=1. Alice and Bob hold k qubits each, jointly in |psi><psi|^{tensor k}, where the completely unknown normalized vector psi is in C^2 tensor C^2=C^4. Put

    r_j=binom(j+3,3),
    h_k=floor(k-(1/2)log_2 r_k).                           (1.1)

There is one circuit on these original 2k qubits, depending only on k, followed by local discarding, which produces exactly h_k standard Bell pairs for every psi. No qubit is supplied, initialized, measured, reset or discarded before this global circuit. Pure zero registers used during the construction are obtained unitarily from the promised pure iid input inside its original Hilbert space.

The integer h_k is optimal even allowing an arbitrary common global unitary and cPPT postprocessing. It is the optimal number of output qubit Bell pairs; the separate sharp minimax results permit arbitrary integer target dimensions and need not be implemented by this circuit.

The circuit uses CNOT and arbitrary single-qubit gates. It can be synthesized exactly with

    G(k)<=1000 sum_(j=2)^k q_j^2 L_j^2 +100 k^2,
    ell_j=ceil(log_4 r_j),
    q_j=2(ell_(j-1)+1),  L_j=2^(q_j),                      (1.2)

and thus G(k)=O(k^7 (log(k+3))^2). For example the explicit looser bound

    G(k)<=256000 k(k+2)^6(3log_2(k+3)+4)^2+100k^2          (1.3)

is sufficient. No optimization of this conservative bound is claimed.

For a fixed efficiently computable inverse-closed finite universal one-qubit gate set together with CNOT, there is an approximation with operator-norm error at most delta, using O(G(k) log^c(G(k)/delta)) gates for a fixed Solovay--Kitaev exponent c. It gives fidelity at least 1-2delta uniformly over all psi. The gate angles and circuit description can be classically computed to the requisite precision in time polynomial in k and log(1/delta). Exactness is asserted for the continuous gate library; a generic Clifford+T circuit is not claimed to realize these algebraic rotations exactly.

Prior work already gives efficient symmetric-qubit compression and general Schur circuits. The contribution here is a fully resource-compatible construction for C^4 iid inputs, its conversion into the optimal integer Bell-pair extraction target, and its precise separation from the still unresolved general mixed-state implementation.

## 2. Sequential symmetric-space compression without supplied ancillas

The normalized occupation-number basis of Sym^j(C^4) is indexed by nu=(nu_0,...,nu_3), nu_i>=0, sum nu_i=j. Fix a lexicographic enumeration enc_j(nu) in {0,...,r_j-1}. It is computable by elementary binomial counts in time polynomial in log j per label, or by explicit enumeration of the polynomially many labels. With unused high digits zero, it fits in ell_j four-level registers. We have ell_j<=j and ell_j<=ell_(j-1)+1, since r_j/r_(j-1)=(j+3)/j<=4.

Inductively assume the first j-1 copies have been transformed, on their full symmetric subspace, to

    |enc_(j-1)(mu)> on ell_(j-1) four-level registers
       tensor |0> on the remaining processed registers.   (2.1)

The j-th original four-level input register is then coupled to only the active ell_(j-1) registers. The total active dimension is L_j=4^(ell_(j-1)+1), and L_j<=16r_(j-1)=O(j^3). Symmetric branching gives the orthonormal vectors

    v_nu=sum_(i:nu_i>0) sqrt(nu_i/j)
                    |enc_(j-1)(nu-e_i)>|i>.               (2.2)

Different nu have disjoint computational support: the pair (mu,i) determines nu=mu+e_i. Every v_nu has at most four entries, and there are r_j of them. Therefore a unitary on this active register mapping every v_nu to |enc_j(nu)> with all other active digits zero can be constructed explicitly:

1. Within each disjoint support, at most three real Givens rotations map v_nu to one chosen computational basis state. The rotations have sines and cosines equal to square roots of ratios of positive integers at most j; zeros are skipped.
2. A permutation of the L_j computational basis states sends these chosen states to the desired distinct enc_j(nu) states. Match the remaining unused source and target states in their fixed increasing order to complete the permutation.

There is no arbitrary exponentially large unitary completion. The complete active basis list has polynomial size. At most 3r_j+L_j<=4L_j two-level rotations or basis transpositions suffice, since r_j<=L_j. At j=1 use the fixed four-level basis permutation matching the chosen enumeration (or choose that enumeration to make it the identity). Compose these steps on the original registers, with fixed wire permutations as necessary; every processed inactive register is already zero under the promised input and was never externally supplied.

At j=k, this maps the entire symmetric subspace, including every coherent superposition of occupations, into the binary integer labels 0,...,r_k-1. Only q=ceil(log_2 r_k) qubits can be nonzero; all other original qubits are in the pure state |0>. This follows simply from the high zero bits of a nonnegative integer smaller than r_k, even if 2ell_k exceeds q.

## 3. Explicit ancilla-free synthesis of the polynomial active unitaries

For completeness, two-level operations on q qubits have an ancilla-free implementation with at most O(q^2 2^q) CNOT and arbitrary single-qubit gates; a conservative constant 100 is more than sufficient below.

A Gray path between the two affected computational basis strings has at most q adjacent steps. Selective adjacent transpositions, forwards and backwards along the path, reduce a general two-level rotation or transposition to a one-qubit operation controlled on a fixed pattern of all other q-1 qubits. Selective X is H on the target, followed by a phase -1 on one selected full basis string, followed by H.

A phase on one selected basis string has the form exp(i theta P_x), with

    P_x=2^(-q) product_l (I+(-1)^(x_l) Z_l).

Expanding the product gives at most 2^q mutually commuting Pauli-Z strings. Each string exponential is implemented by computing its parity into one existing participating qubit using at most q-1 CNOTs, applying one R_z, and reversing the CNOTs. No workspace qubit is added. The empty-string factor is a global phase and has no effect on the channel. A pattern-controlled R_y is treated the same way by expanding its control projector and conjugating Y on the target to Z. All resulting Pauli strings commute before this conjugation. This costs O(q 2^q), and at most 2q path transpositions plus one controlled rotation cost O(q^2 2^q).

Applying this synthesis separately to the at most 4L_j two-level operations of Section 2 costs at most 1000 q_j^2 L_j^2 gates. Fixed final wire permutations, Bell preparation and discarding require at most 100k^2 further gates. This proves (1.2). Since

    q_j<=3log_2(j+3)+4,
    L_j<=16r_(j-1)<16(j+2)^3,

summing gives (1.3). This elementary bound is intentionally looser than specialized Schur or Dicke compression circuits, but proves a genuine polynomial circuit in the exact resource model.

The elementary angles of the Givens rotations depend on integers <=j. The phase-string expansion divides them by powers of two whose exponents are O(log j). Consequently a precision O(log(G/delta)) beyond their O(log j)-bit descriptions suffices. Standard polynomial-time evaluation of square roots and trigonometric inverses computes them to this precision. A telescope over at most G gates bounds total unitary error by delta when each gate error is at most delta/G. Solovay--Kitaev then gives the stated finite-library overhead without an added ancilla. For normalized inputs, ||U rho U*-V rho V*||_1<=2||U-V||, and subsequent local channels contract the trace norm; the output target fidelity loss is at most 2delta.

## 4. Optimal Bell pairs and final redistribution

The definition of h_k implies

    r_k<=2^(2(k-h_k)),
    ceil(log_2 r_k)<=2(k-h_k).                            (4.1)

After Section 2, redistribute the q possibly nonzero memory qubits into the two local garbage sets of k-h_k qubits each, using fixed global SWAP gates. Fill their unused positions with some of the existing zero qubits. The remaining h_k qubits at each party are all zero. Apply a Hadamard to each remaining Alice qubit and a CNOT from it to its paired Bob qubit. These are still gates within the one allowed global unitary. The resulting state is

    Phi_2^(tensor h_k) tensor omega_garbage(psi).

Local discarding yields exactly the requested Bell pairs. Every gate and placement was selected without psi.

For necessity, the Haar average of |psi><psi|^{tensor k} is Pi_sym/r_k. If one common protocol gives fidelity one for every psi, its effective fidelity operator M is the identity on Sym^k(C^4). The cPPT effect bound yields

    r_k<=Tr M^2<=4^k/4^h.

Thus h<=floor(k-(1/2)log_2 r_k)=h_k. LO attains the cPPT upper bound for the integer Bell-pair objective at every k. In particular the log correction in the main minimax result is not only an abstract dimension count: this pure-input qubit specialization attains its exact integer zero-error target with a polynomial circuit and no externally initialized pre-unitary memory.

## References and limits

Plesch--Buzek, Efficient compression of quantum information, https://arxiv.org/abs/0907.1764v2, and Baertschi--Eidenbenz, Deterministic Preparation of Dicke States, https://arxiv.org/abs/1904.07358, already give efficient symmetric-qubit compression; this prior mechanism is credited. Z. Chen, C. Xiong, K. Khadiev and J. Wu, Efficient quantum compression for identically prepared states with arbitrary dimension, https://arxiv.org/abs/2307.12024v2, directly treats exact compression of arbitrary-dimensional symmetric states; the C^4 compression mechanism is prior work and is not a discovery claim here. The elementary construction above is included to account explicitly for all original registers and gates in the extraction application. Bacon--Chuang--Harrow, https://arxiv.org/abs/quant-ph/0601001, gives the general Schur-transform algorithmic context. Barenco et al., Elementary gates for quantum computation, https://arxiv.org/abs/quant-ph/9503016, and Shende--Bullock--Markov, Synthesis of Quantum Logic Circuits, https://arxiv.org/abs/quant-ph/0406176v5, are prior general exact synthesis results. The elementary Pauli-projector expansion above supplies the ancilla accounting directly, rather than assuming that those constructions preserve our resource budget. Solovay--Kitaev finite-set synthesis is an explicit external algorithmic theorem.

The proof is for the pure-input promise on the original 2k qubits. Mixed inputs do not generate the pure zero memory in (2.1), so this reasoning cannot justify an efficient implementation of the full all-state Schur protocol. Nor does the Bell-pair objective solve the optimal finite-library gate count or arbitrary-integer-target sharp constant.
