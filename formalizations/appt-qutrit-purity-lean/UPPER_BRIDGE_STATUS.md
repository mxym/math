# Uniform-to-ordered-spectrum proof boundary

`lean/APPT/UpperSpectrumBridge.lean` proves the large-`n` upper-bound
**implication** from an explicitly quantified `UniformCertificateBound`
proposition. The module does **not** supply a proof of this proposition and
does **not** assume APPT is equivalent to the two Hildebrand matrices.

Once the 17-block identity and 17-block nonnegativity modules have compiled,
`APPT.Uniform.normalized_bound` can instantiate `UniformCertificateBound`.
That step is an ordinary application of a proved Lean theorem and requires no
new axiom; its precise source must be audited and compiled before being added.

A separate, genuinely quantum theorem that every APPT density state forces
`matA` and `matB` positive semidefinite for its sorted eigenvalue list is
still necessary. The already kernel-checked attainment theorems live in the
sibling `formalizations/appt-qutrit-purity/` directory. Neither existing
result by itself proves the final optimality theorem.
