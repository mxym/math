# Dated source and concurrency screen

Date: 9 October 2026. This is a bounded search record, not a guarantee of completeness or priority.

## Repository state

Read the current `README.md`, `SOLVED_PROBLEMS.md`, `RESEARCH.md`, recent commits, and the source material relevant to candidate overlaps. The first inspected mxym/math head was `c0a1085`; before the new worktree was created, `origin/main` was refreshed to `7961515`. A new worktree/branch was based on that commit. No `AGENTS.md` was found anywhere in that checked-out tree, excluding dependency build trees. No existing files in another worktree were modified.

The main branch already includes or is actively developing ECQC pure-state counterexamples, ECQC saturation, APPT qutrit purity, Gaussian partition formalization, and related permanent/entropy projects. Those were excluded as duplicate/parallel targets. A full text scan of the 636299-character current OpenAI `CONTENTS.md` did not match `monogamy`, `vertex.minor`, `claw`, `Bell.Skandera`, or `local complement`; GitHub search was also attempted. This only checks the indexed/catalogued scope, not every proof in that repository. The retrieved OpenAI `CONTENTS.md` blob was `2c68c086fff36a5806c936ad1659cf1a8d0b6dd9`; its README blob was `50feb63d396138f30dc1ff1e0af121d0263bf5a3`.

## Candidates considered

1. **Absolute PPT purity.** Current primary/source records include Anh T. Tran, arXiv:2609.18568. The repository has an active APPT formalization checkpoint. Excluded to avoid duplication; no APPT theorem is claimed here.
2. **Bell–Skandera real-rooted integer polynomials.** Read Mu–Welker, arXiv:2503.24076v1, Question 1.1 and the stated partial criteria. The repository's ended scalar-arithmetic stage is explicitly not a real-rooted counterexample. Deferred: the missing discrete coefficient inequalities are not supplied by Newton inequalities or weak norm bounds, and this session did not find a new closed route. No resolution is claimed.
3. **Graph-state MMI forbidden subgraph.** Read Fuentes–Keeler–Munizzi–Pollack, arXiv:2511.19585v1, including Conjecture 1 (printed p.30) and its surrounding induced-star interpretation. The arXiv abstract/history endpoint returned v1, 24 November 2025, with no later version listed. Selected because the exact forbidden-target formulation permits a finite extension certificate plus an unbounded induction.

## Primary references checked

* Fuentes et al., arXiv:2511.19585v1: the specific conjecture. Search results also showed the 2026 TQC poster description; this is not a separate proof.
* Van den Nest–Dehaene–De Moor, Physical Review A 69, 022316 (2004), DOI 10.1103/PhysRevA.69.022316: LC graph transformations.
* Hein–Eisert–Briegel, Physical Review A 69, 062311 (2004), DOI 10.1103/PhysRevA.69.062311: graph states, cut ranks, and small graph-state classifications.
* de Jong et al., Physical Review Research 6, 013330 (2024), DOI 10.1103/PhysRevResearch.6.013330: complete GHZ extraction results for linear cluster states, not arbitrary connected graphs.
* Ji Ho Bae, arXiv:2604.13434v1: a different edgeless vertex-minor Ramsey target. The present proof does not use its computational statements or conflate its parameter with a connected claw threshold.

Queries included combinations of `2511.19585 proof`, `Monogamy of Mutual Information in Graph States conjecture`, `local complementation claw`, `claw vertex-minor-free`, `K4 vertex minor classification`, and `GHZ four seven connected graph`. Two search engines and primary publisher/arXiv pages were used. No exact prior resolution was located in this finite screen. Accordingly the paper states the proved implication and its source but makes no first-in-history claim.

## Independent content versus inherited ingredients

The six small graph-state types, LC operations, and binary cut-rank entropy identity are established objects. The deliverable supplies its own explicit 120-extension certificate, completeness induction, analytic negative-class proof, exact all-partition formula, and separately implemented replay. The entropy identity and lifting lemmas are reproved to expose the semantic bridge from actual quantum states to the finite graph certificate.
