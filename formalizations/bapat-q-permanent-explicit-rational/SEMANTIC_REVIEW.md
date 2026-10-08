# Root semantic review of the specified rational Bapat witness

This is an internal model-conducted source review by the bridge author. It is
not external human peer review, an independent-model review, a new Lean run,
or a literature-priority determination. The review is tied to the six source
hashes below. The execution record is separate.

The actual main theorem is unconditional for the specified dimension-200
matrix; it has no hypothesis asserting a negative derivative, a Fischer
identity, a certificate result, or perturbation continuity. It provides actual
`Matrix.PosDef`, offdiagonal nonzero entries, q0 strictly between 0 and 1,
and a positive h/8 lower bound on the actual q-permanent reversal at q0 and 1.
The endpoint 1 belongs to the original interval [-1,1]; these two displayed
parameters are not described as both interior.

DefinitionBridge proves that the inversion cardinal, finite inversion sum,
real endpoint polynomial derivative and two separately defined q-permanents
are the same actual objects. It constructs the actual two-column V and proves
VV* equals the same ordered rank-two Gram matrix. No permutation of the row
order or assumed invariance of the q-permanent is used.

N200EndpointGap uses the actual 200-transition state theorem and exact
Gaussian-integer coefficient norms. Integer strict inequality gives a unit
gap; the proved endpoint identity gives real derivative at most -1/2.
N200EntryBounds checks the actual coordinates and derives the norm bound1600.
No rounding, numerical solver or `native_decide` supplies the sign.

ConstantParameters retains factorials and powers symbolically and proves exact
natural/rational/real/complex cast correspondence for Gamma, K, epsilon, h and
q0. In particular, q0=1-1/(8K), not an existentially chosen real parameter.
The universal proved Gram perturbation and derivative-bound theorem then gives
positive definiteness, the derivative estimate and the interval reversal.

N200RationalEntries provides actual entry formulas as rational real and
imaginary parts, based on the same ordered input list. N200Explicit also proves
real-valuedness of the actual all-permutation q-permanent for real q and refutes
the actual original strict-monotonicity conjecture, including its non-diagonal
and positive-definite hypotheses.

Scope boundary: the final B is complex Hermitian and full rank; its underlying
unperturbed Gram matrix has rank at most two. This is not the real-symmetric
finite-existence proof or the separate noncomputational asymptotic route.
The public v1.1 existential counterexample is preserved separately. Formalizing
a specified rational witness does not itself establish historical priority.

The prior original runner's timeout is retained as FAILED. Its completed fresh
22-module source builds and all-owned inventory are eligible only for a
separate successful 928-owned union replay with actual inventory coverage and
false control. No timeout is treated as PASS. The new bridge must itself pass
fresh-source compilation, all30 theorem axiom checks, and full transitive
empty-kernel replay before publication.

## Reviewed mathematical source SHA-256

- `DefinitionBridge.lean`: `1784dc5875e8e8b7b330bc285fd75997baaede578906f86a57f47119ed1e78be`
- `ConstantParameters.lean`: `1a4989e02f78acb4ee445ea9247e6d911669bd0f8a6db95bd7b88e919229fac5`
- `N200EntryBounds.lean`: `c8099eff4bc65088bf700cd042ec97ce5f00fddcc2cc0d8b595fee5e3f8558ae`
- `N200RationalEntries.lean`: `a42974b785b5f361b1ccd146f73c17c1d704b28560794cbe4da8a3827c6b1de5`
- `N200EndpointGap.lean`: `8e4ee39e6f4f196dd15c0916473caa46e991649a40329000e802ba1f53aac9d5`
- `N200Explicit.lean`: `c2de6d4ebd28a4f7c1adc89778f387ee2a6de5f0edbbbf8f0bf9086719169390`
