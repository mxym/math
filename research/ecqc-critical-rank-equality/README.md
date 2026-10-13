# Critical-rank equality in the pure-state ECQC bound

**Yongxian Zhang (张永贤)** · School of Computer Science and Engineering,
South China University of Technology · mxymmxym1@gmail.com ·
ORCID 0009-0000-3864-3536.

[Complete mathematical proof](PAPER.md) ·
[Explicit limited Lean coverage and fresh kernel audit](../../formalizations/ecqc-critical-rank-progress/README.md).

For identical canonical prime-dimensional MUBs, this paper classifies all pure
ECQC equality states of Schmidt rank **r=(p+1)/2**, the largest rank permitted
by the previously proved deficient-rank gap:

* If p≡1 mod4, all are the independent Weyl orbit of the even-parity projection
  of the square-root-of-minus-one Bell state.
* At p=3, all are the independent Weyl orbit of the previously known
  even-parity qutrit singlet.
* At p≡3 mod4, p≥7, no equality occurs at this rank.

In either admissible case there are exactly **p⁴ distinct rays**, each with
`I_M=log r`, `Q=2 log r`, `E=p log r`. Thus an equality state at p≡3 mod4,
p≥7, if rank deficient, must have rank at most (p-1)/2. The smaller ranks and
the unrestricted high-dimensional supremum remain unclassified.

The new part is the **necessary classification and congruence obstruction**;
parity/Wigner phase-point operators and Bell projection are classical machinery
and are credited. The paper does not call the qutrit example or existing
full-rank theorem new, nor claim first historical solution based on finite
literature screening. It fixes the original minimum over p of p+1 paired
measurement settings and uses Bob's actual same canonical basis.

## Verification

The mathematical proof uses the published Holevo inequality and its necessary
commuting-state equality condition. All specialized reductions are written out.
The core residue obstruction and a matrix rigidity lemma have fresh, pure-kernel
Lean verification. **The full quantum theorem is not Lean-complete.**

```bash
python3 check_actual_states.py
```

The standalone standard-library checker reconstructs forty-five actual states
at primes 3,5,13,17,29, including both roots where present and independent
Weyl displacements. It checks the actual Schmidt rank by rational elimination,
both partial traces, the flat marginal minimal polynomial, 329,660 actual
Born probabilities by integer cyclotomic arithmetic, and mutual information
by exact rational coefficients of logarithms of primes. It rejects a wrong
root, a Bob-conjugated basis and a composite dimension. These finite records
do not replace the paper's arbitrary-prime proof or its classification direction.

Source hashes are in `SOURCE_HASHES.json`. The immutable earlier ECQC releases
are untouched. This new manuscript has no Release, DOI or external review yet.
AI assisted derivation, coding, literature checking and writing; no external
funding. Copyright 2026 Yongxian Zhang; all rights reserved for original material.
