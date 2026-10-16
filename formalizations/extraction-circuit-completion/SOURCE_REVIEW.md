# Primary-source and library review, 2026-10-16

The review informed independently written proofs. No third-party Lean source
was copied or imported into this package.

- [Barenco et al., Elementary gates for quantum computation](https://arxiv.org/abs/quant-ph/9503016), 1995: primary reference for U(2)+CNOT universality and ancilla-free controlled/two-level synthesis. The actual Gray/Pauli word proofs in this package are internal Lean proofs, not imported universality assumptions.
- [Chen, Xiong, Khadiev and Wu, Efficient quantum compression for identically prepared states with arbitrary dimension, v2](https://arxiv.org/abs/2307.12024v2), revised 2026-08-29: existing exact symmetric-input compression and efficient approximation. This prior compression mechanism is not presented as a new result of this project.
- [Dawson and Nielsen, The Solovay–Kitaev algorithm](https://arxiv.org/abs/quant-ph/0505030), 2005: primary source for efficient finite-library approximate synthesis. The theorem and its complete algorithmic dependencies remain outside the formal scope here.
- [LeanQuantum](https://github.com/inQWIRE/LeanQuantum): reviewed existing gate/matrix infrastructure. Its toolchain and current proof coverage do not directly supply the required pinned complete occupation/SK chain.
- [TNLean](https://github.com/LionSR/TNLean) and its [local-quantum-circuit blueprint](https://sirui-lu.com/TNLean/blueprint/ch-local_quantum_circuits.html): relevant two-level/Givens work, but its published toolchain differs from this package and its README records incomplete/axiomatic parts elsewhere. No claim has been made that every potentially relevant closure is incomplete; a same-pin closure review would be required before reuse.
- [NetRxn/SK_EFT_Hawking generic quantitative SK source](https://github.com/NetRxn/SK_EFT_Hawking/blob/main/lean/SKEFTHawking/FKLW/GenericSolovayKitaevQuantitative.lean): the inspected generic endpoint explicitly receives a calibration bound, with separate example-specific discharge. The inspected file has an all-rights-reserved header. No source was copied or imported, and no repository headline was treated as a verified unconditional SK dependency.

The ordinary argument in the manuscript/addendum was checked for the main
structural points: normalized occupation branching, omitted zero branches,
actual same-register Gray/Pauli synthesis, spectator preservation and phase
invariance. The resulting local identities have now been proved internally.
This is not an independent review certificate for the still-unassembled
all-k algorithm or the classical precision/finite-library complexity claims.
