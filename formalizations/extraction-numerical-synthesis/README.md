# Numerical synthesis with explicit arithmetic traces

Status: own-module feedback checks passed; fresh serialized aggregate pending. Lean 4.34.1; Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

This independent package extends the frozen b288 `extraction-circuit-recursion`
package. It contains only the 20 later numerical/cost modules and their 160
new theorem roots. Import paths are `CircuitNumerical.*`; declaration names
retain namespace `CircuitRecursion`. The entire old package has been restored
to its b288 bytes. `PORT_PROVENANCE.json` records the pre-port mature commit,
byte-verified D: backup, moved modules and historical verification boundary.

The online algorithm takes finite inverse labels, a fixed finite word table,
integer output precision p, and four-coordinate rational/dyadic entry-packet
oracles for the fixed gate library and target SU(2) matrix. Universality and
inverse closure internally provide the library-dependent offline net. This
does not compute a net bound uniformly from an arbitrary library description.
The manuscript's efficiently computable gate-set assumption is retained when
asking for a classical algorithm with efficient input providers.

`numericalSU2Synthesis_dyadic` proves the actual finite word recursion has
operator error at most `2^-p` and word length `C*(p+1)^5`. Both correction
steps, overlapping stopping decisions, conditioned chart selection and
normalized factor oracles are implemented and proved internally. No final
error, factorization or polynomial-cost certificate is assumed as an input.

The explicit eager-cache implementation returns the same word, with

```
D <= 51200000*(L+1)*(p+1)^9,
gate-packet requests = m*(D+1),
target-packet requests = D+1,
maximum requested input precision <= D.
```

It stores every supplied packet at precisions 0 through D once. Each dyadic
signed numerator uses at most q+3 bits, and the input prefixes use at most
`4*(m+1)*(D+1)*(D+3)` signed-numerator bits. Denominators are specified by their
precision indices. This is an input-data bound, not an intermediate-bit bound.

`cachedArithmeticSU2Synthesis` adds an actual finite expression/trace program
and proves its word equals the numerical algorithm. Its selective execution
cost is bounded by a conservative expression count, including repeated
subexpressions and all chart alternatives:

```
arithmetic expression operations <=
  1001*(n+1)*(L+1)*2^64*(p+1)^64.
```

Here m, n and L are fixed library/table constants. The listed primitives are
rational arithmetic/comparison, binary shift, natural floor, integer square
root and stored-packet access. Packet product nodes evaluate two stored
operands once. Stopping-threshold construction is included in the trace.
The executable backend uses binary shifts for dyadic powers, and `run_correct`
connects it to the expression semantics. This is an explicit arithmetic-model
bound. Intermediate operand bit lengths, primitive/provider Turing costs and
structural allocation/index costs remain open. The original extraction-family
description/encoding binding is a separate sibling extension.

The pre-port 58-module/416-root source passed authorized own-module feedback
checks, including all root type/axiom prints. Reports under
`verification/pre-port-history` describe that historical source and paths.
The renamed 20 modules and all 160 root prints have passed their own feedback checks. A fresh serialized aggregate and
independent replay must use this new package and its own root scope.
