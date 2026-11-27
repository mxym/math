# Sources and exact scope

1. Harumichi Nishimura, *Concrete Functions in Private Simultaneous
   Quantum Messages: Quantum Advantages and Structural Limitations*,
   [arXiv:2610.23090v1](https://arxiv.org/html/2610.23090v1)
   (submitted 16 October 2026, v1 only as checked on 27 November 2026).
   Section 2.2 defines the averaged-state privacy and correctness
   model. Section 4.1, Lemma 4.1 gives the three-bit label formula.
   Section 4.4 fixes one GHZ state, arbitrary finite hidden classical
   randomness, local Paulis on the sent qubits and arbitrary referee
   measurement, and states Equations (4.4)–(4.8). Theorem 4.5 already
   constructs all 80 allowed three-bit functions. Remark 4.7 gives
   the other 176 floating-point infeasibility outcomes explicitly
   as observations, naming EXACT1, EXACT2 and the two-edge forms.
   Section 7's second open direction asks for a rigorous or
   analytic converse to turn that census into a theorem. The
   present note supplies it and generalizes the criterion to
   all-essential functions at odd party counts. The original
   three-bit positive family and the GHZ label formula are not
   new results of this note.

2. Kazumasa Shinagawa and Koji Nuida, *Explicit Lower Bounds for
   Communication Complexity of PSM for Concrete Functions*,
   [IACR ePrint 2023/1743](https://eprint.iacr.org/2023/1743).
   This is the classical PSM comparison used by Nishimura for
   three-bit majority and equality; it is not the fixed
   one-GHZ Pauli feasibility classification.

3. Akinori Kawachi and Harumichi Nishimura, *Communication
   Complexity of Private Simultaneous Quantum Messages Protocols*,
   [ITC 2021](https://doi.org/10.4230/LIPIcs.ITC.2021.20).
   The broader PSQM model permits general local encoding
   channels and other shared states. The present converse
   does not apply to that broader resource model. In particular
   it does not settle the unrestricted AND3 cost question in
   Nishimura Section 7, nor claim the broader local-unitary
   impossibility result of his Theorem 5.1.

Bounded prior-art check (27 November 2026): inspected the
original arXiv history and searched the exact arXiv identifier
and title with “GHZ–Pauli”, “EXACT1”, “two-edge”, “classification”,
and “odd party”; also reviewed the concrete PSM/PSQM work above.
No published analytic converse matching Remark 4.7 or the stated
all-essential odd-party theorem was found in this check. This is
not an absolute priority claim. No files from the sources are
required or included for the deterministic replays.
