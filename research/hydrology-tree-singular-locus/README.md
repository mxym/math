# Rooted-tree compartment singularities — theoretical research

**Status: complete written proofs of the stated model-class theorems, with exact finite diagnostics. Not Lean-formalized, not externally peer reviewed, and not a claim to have solved general hydrological model identification.**

This is a purely theoretical continuation of the repository's hydrology work. No laboratory, field data, or numerical calibration is needed for the results.

## Main result

For every finite bidirected tree, a single input and measured state at the same root r, and one unknown leak at any fixed vertex ell, the full physical-parameter coefficient-map Jacobian is

    det DC = ± (product of rates directed toward ell)
               × product_edges (forward × reverse)^(descendant_size - 1)
               × product_sibling_pairs Res(P_child, P_sibling)^2.

Each P_child is the characteristic polynomial of an actual principal submatrix: the original diagonal loss back to the deleted parent MUST be retained.

The full numerator/denominator resultant equals this Jacobian times the product of rates directed away from the leak, up to an ordering sign. At positive rates, differential regularity is therefore equivalent to root input-output minimality. Branch spectral collisions, not simply equal individual rates, describe the interior singularities.

## Precise open problems addressed

Theorem 1 and Corollary 8 of [THEOREMS.md](THEOREMS.md) give written proofs of:

- Gross–Meshkat–Shiu, *Identifiability of linear compartmental models: the singular locus*, **Conjecture 5.5**: the all-size catenary singular-locus polynomial.
- **Conjecture 5.9**, credited in that paper to Hoch–Sweeney–Tung: the exact multiplicities of every directed rate for arbitrary rooted trees.

The second conclusion requires the proof that no edge variable divides a sibling resultant; a visible monomial lower bound alone would not settle it. The general formula also allows the leak and observation roots to differ and supplies the remaining noncoordinate factors.

The 2026 SIAM paper by Ahmed and coauthors still discusses a future resolution of the catenary conjecture. Search did not locate a later resolution of these exact statements. This is not proof of historical priority. See [LITERATURE.md](LITERATURE.md) for close prior work and the narrowly delimited contribution. Generic local identifiability of tree models and global path identifiability were already known.

## Proof and check entry points

- `THEOREMS.md`: definitions, nine numbered theorem/lemma/corollary blocks, complete proofs, model caveats, and an exact positive singular example.
- `PROOF_DEPENDENCIES.md`: proof graph and audit of nontrivial steps.
- `exact.py`: standard-library integer matrix differentiation, Bareiss determinants, and Sylvester resultants. All 200 rooted tree shapes on 1–8 vertices, every leak location, five rate fixtures: 7,230 cases.
- `independent.py`: separately implemented SymPy checks of 11 full symbolic small-model identities; exact five-compartment spectral-collision example and ranks. It does not import `exact.py`.
- `reproduce.py`: new-directory source-isolated runs, normal/optimized-Python comparison, source hashes, logs, and failure-closed receipts.

Finite tests support but do not prove the arbitrary-size identities. Four altered formulas and one incorrect all-distinct-rates claim are rejected. The supplementary code uses no floating-point calculation or empirical data.

## Reproduce

Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0 are the recorded reference environment. The first checker needs only Python's standard library. The second uses exact symbolic arithmetic, not mpmath numerical evaluation.

```sh
python -m pip install -r requirements.txt
python reproduce.py --output-dir /tmp/tree-singular-independent
```

The output directory must not already exist. The workflow separately installs pinned dependencies and executes this command on a clean GitHub-hosted runner. Only a retrieved completed result is reported as a CI pass. The evidence directory is populated with source-bound verification receipts after the run, rather than a promise of validation.

## Scope and provenance

Known, fixed tree topology; constant linear transfers; one free leak; colocated input/measured state. This does not classify arbitrary multiple leaks, multiple inputs/outputs, nonlinear storage laws, unknown topology, noisy inversion, or general catchment systems. For a root leak measured as discharge, the manuscript proves the positive-interior translation from state output to leak flux. No new empirical hydrological law or improved forecast score is asserted.

The material is a distinct theoretical direction, not an experimental extension and not a completed Lean package. No completion Release or DOI is created here.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering, South China University of Technology. mxymmxym1@gmail.com; ORCID 0009-0000-3864-3536. No external funding. AI-assisted research. Preserve applicable repository licenses and third-party notices; separately original material is all rights reserved where no existing license applies.
