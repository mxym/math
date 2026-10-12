# New weak principal supply and literal main endpoint

These new modules preserve the historical six workloads and their controls.
`ArithmeticSupplyWeakFromDirichlet` constructs the genuine conductor ray field
and finite Galois normal closure, then proves
`Entry002.arithmeticSupply_weakPrincipalSupply_from_Dirichlet` for every quadratic
number field and every positive conductor. All norm, principal-kernel,
conjugation, paired `pO`, and unital residue-map witnesses are retained.

`ArithmeticSupplyWeakMainReduction` records the one-premise reduction through
the prime-specific Dirichlet-to-logarithmic-good-bin bridge.
`ArithmeticSupplyWeakMain` uses the proved bridge and finite sieve to state the
unchanged, unparameterized `Entry002.arithmeticSupply_mainTarget_proved : MainTarget`.

The main owned modules must first be freshly compiled with the pinned round-five
runtime. Then, from this arithmetic-audit directory, run:

```sh
python3 -B round5_weak_compile.py --cft-cache ${PRIVATE_WORKSPACE_PATH} > logs/round5-weak-closed-fresh.log 2>&1
```

The `--cft-cache` argument is an explicit read-only root of the already audited
external compiled objects. An equivalent matching cache can be supplied at a
different location. The compiler checks all 995 CFT and two historical bridge
objects against the included input-object SHA-256 bindings before importing
them. `--lean-binary` and repeated `--main-lean-path` options can
override relocated tool and main/official cache paths. New owned outputs go to
`round5-weak-build/lib/lean`; historical caches are never written.

From the main `lean` directory, validate the final log and its exact stored root
inventory with:

```sh
python3 -B references/upstream/arithmetic-audit/round5_weak_summarize_audit.py references/upstream/arithmetic-audit/logs/round5-weak-closed-fresh.log references/upstream/arithmetic-audit/logs/round5-weak-closed-recursive-summary.json
```

The canonical final summary uses the included log's relative path and exact
SHA-256. The copied three-module evidence is an earlier workload retained
unchanged; `logs/round5-weak-three-module-evidence-relocation.json` maps its
original development paths to the included identical evidence and promoted
sources. Compiled binaries and dependency caches are omitted from the archive;
their hashes identify the actual objects used by the recorded compilations.

The pins remain Lean `4.34.1`, mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, ClassFieldTheory
`2eb22d6485af45f29c5219de6c49f196a61c4f49`, and the previously authenticated
OpenAI/math compatibility revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The existing authenticated 995-module CFT closure is reused as compiled input.
This workload claims fresh compilation of the new owned modules and a new
stored-type/body closure audit; it does not claim a fresh 995-module CFT rebuild.

`ArithmeticSupplyWeakClosedCompilerAudit` selects every stored declaration by
the exact four owned module indices, including generated declarations. It
requires the closed main root to have exactly the unparameterized `MainTarget`
type. For every root it traverses stored types and bodies, checks agreement with
`collectAxioms`, and rejects extra axioms or unsafe, partial, or missing
dependencies. `logs/round5-weak-*` holds the new logs, exact root inventory,
source/object bindings, and historical external input-object hashes.
