# Sources and exact scope

1. Eric Chitambar, Sarah Hagen, David W. Kribs, Zhao Ma, Mike I.
   Nelson, and Andrew Nemec, *Codes for Quantum Secret Sharing
   with a Helper*, [arXiv:2609.00234v1](https://arxiv.org/pdf/2609.00234v1)
   (31 August 2026; v1 only as checked 27 November 2026).
   Definition and Lemma 1 give the stabilizer helper structure;
   Theorem 1 and Corollary 2 give the single-qubit secret,
   single-qubit target positive result, originally using two
   classical bits. Example 3 (printed PDF p. 6) exhibits a
   qutrit contrast for the specific Pauli method. The PDF
   matrix, not the truncated HTML, was used to check the
   fourth-row symbol. The published row is noncommuting as
   printed; the single-entry correction and exact \(1/3\)
   bound for that corrected qutrit target are in Section 5
   of the present note. The more general theorem here
   concerns any prime, any number of logical qudits and an
   equally sized target, and optimizes fidelity and classical
   messages over arbitrary one-way local operations.

2. Eric Chitambar, Sarah Hagen, David W. Kribs, Mike I. Nelson,
   and Andrew Nemec, *Quantum Secret Sharing with a Helper and
   Programmable Access Structures*, [arXiv:2609.00220v1](https://arxiv.org/html/2609.00220v1).
   Definition 1, the monotonicity clarification immediately
   after it, and condition (iii) specify blind helper codes.
   Section V asks which helper codes admit one-way local
   decoding without extra teleportation resources. We answer
   that question in the equal-target-dimension prime
   stabilizer class, not in the unrestricted helper model.

3. Emanuel Knill and Raymond Laflamme, *Theory of quantum
   error-correcting codes*, [arXiv:quant-ph/9604034](https://arxiv.org/abs/quant-ph/9604034).
   The scalar-compression criterion for erased-operator
   algebras is standard. David Fattal et al., *Entanglement in
   the stabilizer formalism*, [arXiv:quant-ph/0406168](https://arxiv.org/abs/quant-ph/0406168),
   provides the standard stabilizer-projector and partial-trace
   setting. The note proves the specific cleaning and
   conditional-algebra facts it needs.

4. Matteo Gregoratti and Reinhard F. Werner, *Quantum Lost
   and Found*, [arXiv:quant-ph/0209025](https://arxiv.org/abs/quant-ph/0209025),
   and Laleh Memarzadeh, Chiara Macchiavello and Stefano
   Mancini, *Recovering quantum information through partial
   access to the environment*, [arXiv:1101.3768](https://arxiv.org/abs/1101.3768),
   study environment-assisted recovery and entanglement
   fidelity. The former allows a full environment measurement;
   the latter specializes to particular noise models. Our
   conditional algebra concerns stabilizer codes with both a
   measured helper and a separate erased region, plus a
   sharp finite classical message constraint.

Bounded search on 27 November 2026: exact titles/identifiers of the
two helper papers, “one-way helper entanglement fidelity”,
“stabilizer helper symplectic defect”, and partial-environment
recovery. No matching equal-dimension fidelity/message theorem
or correction to the specific qutrit generator was located.
We do not claim novelty for stabilizer cleaning, Pauli projector
algebra, Clifford realization of symplectic maps, or the known
single-qubit recovery. No third-party source file is redistributed
or required for the replay; the small stabilizer example is cited
as mathematical data and tested from its Pauli labels.
