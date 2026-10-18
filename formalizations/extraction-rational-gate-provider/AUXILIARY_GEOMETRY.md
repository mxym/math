# Auxiliary rational-phase geometry

These nine additional named theorems support the prospective concrete library.
They are not new universality results and are not in any frozen audit.

GaussianAngle.lean sends Gaussian integers to ZMod5 with i mapped to2.
The numerator3+4i maps to1, whereas5 maps to0. Consequently its positive
powers cannot equal5^n. Complex injectivity and clearing denominators prove
q=(3+4i)/5 has norm square1 and q^n is never1 for positive n.

CircleDensity.lean places q on the unit circle, transports it through the
circle/AddCircle1 homeomorphism and proves infinite additive order. Mathlib's
irrational-rotation theorem then proves its integer powers are dense on Circle.
No numerical irrationality assertion or unproved density hypothesis is used.
The mathematical phase/circle denotations are noncomputable; the separate
five-state binary provider has no such real/complex computation in its program.

Density on SU2, the four explicit gates/inverse labels and the numerical
provider interface are separate remaining bridges. Circle density alone is not
a complete universal-gate or full compiler-time theorem. See the author
validation reports for the exact ordinary Lean checks; no independent
empty-kernel replay is claimed for this auxiliary module family.
