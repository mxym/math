# Lean kernel audit — binary-code orthogonal sign action

## Replayed compiler and dependency

Source: GaussianCodeCore.lean
Lean version: 4.34.1
Import: Init (Lean core only; no Mathlib needed)
Toolchain: leanprover/lean4:v4.34.1

Compiler invocation:
  lean formal/GaussianCodeCore.lean

All declared theorems compiled successfully. Exact stdout,
including kernel axiom reports, appears in
../results/lean-check.txt.

## Important checked declarations

- dot: recursive Boolean binary dot product on Fin n.
- add: coordinatewise Boolean XOR.
- dot_add: dot(n,u+v,g) = dot(n,u,g) XOR dot(n,v,g).
- sign_xor: character of XOR is product of integer signs.
- sign_dot_add: binary linear character homomorphism.
- add_self / sign_dot_self: binary group involution algebra.
- orbitCoord / orbit_mul: score-orbit sign multiplication.
- sign_square and orbit_unit: every sign-coordinate squared is 1.
- sqEnergy: exact full integer sum of coordinate squares.
- sqEnergy_signTwist: a diagonal +/-1 reflection preserves
  the **entire finite-dimensional squared energy**.
- codeTwist_orbit: the group action sends a codeword
  orbit vector to another orbit vector as expected.
- codeTwist_preserves_energy: every binary-code group
  sign action preserves the full squared energy.

These are actual universally quantified Lean theorems,
not finite enumerations of selected dimensions.

## Axioms and omissions

The #print axioms declarations on three representative
theorems report:

  GaussianCode.sign_dot_add: [propext]
  GaussianCode.orbit_reflection_preserves_square:
      [propext, Quot.sound]
  GaussianCode.codeTwist_preserves_energy:
      [propext, Quot.sound]

These are Lean standard foundational axioms, not
user-declared assumptions. No sorry, admit, unsafe,
custom axiom or opaque external proof witness is
used to establish the above algebraic theorems.
The source is independently replayable with Lean alone.

**CRITICAL SCOPE LIMIT:** The Lean theorems prove
the finite Boolean-character and integer-vector
isometry algebra. They do NOT prove Gaussian
measure preservation, conditional integration,
the spherical-cap probability bound, the
Berry–Esseen theorem, or the complete analytic
variance-rigidity theorem of ../paper.md.
Those claims have separate rigorous
**written analytic proofs**, not Lean proof terms.

The global Gaussian theorems are therefore
not described as fully Lean-formalized.
