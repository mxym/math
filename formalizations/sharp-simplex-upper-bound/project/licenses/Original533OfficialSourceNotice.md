# Official source provenance

The three vendored OAI files originate from
[OpenAI/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/ProjectionVolume):

- `lean/OAI/Geometry/ProjectionVolume/Model.lean`
- `lean/OAI/Geometry/ProjectionVolume/Basic.lean`
- `lean/OAI/Geometry/ProjectionVolume/Brightness.lean`

The official Lean directory's Apache License 2.0 is copied verbatim in
`LICENSE.OpenAI-math.Apache-2.0.txt`. Existing official declarations and notices
are retained. Basic and Brightness are byte-identical to their official
sources. Model has a prominent modification notice and only its umbrella
import is replaced by four checked pinned Mathlib imports. All Model
declarations and proof bodies are unchanged. `ModelImportOnly.patch` is the
complete diff, including the modification notice; `Provenance.json` records
all exact original/adapted hashes, the original commit and package pins.

Keep this notice, the copied license, import-only patch, and provenance record
alongside copies of these vendored files. Do not execute the official Lake
configuration to build this small lane: it contains unrelated dependency
bootstrap and compatibility patch logic.

The new `Entry005/OfficialProjectionDefinitions.lean` is a separate checked
equivalence bridge authored in the continuation workspace. It does not change
the original target definitions or claim any broader official theorem.

Replay command in this workspace:

```text
python ${HISTORICAL_LOCAL_PATH}
```

The script checks source hashes, then compiles the four source targets
sequentially with Lean 4.34.1 and `-DautoImplicit=false`, using only the readonly
pinned dependency path in `formal/LeanPath.txt`. All output .oleans and logs
remain in the isolated checkpoint. It finally runs the complete 40-declaration
axiom audit. No source under the original clone or shared dependency caches is
written. Root integration should copy the three OAI files, the separate
Entry005 bridge, and this provenance bundle into its own project and run its
own compile/audit, with that project's already compiled Entry005.Targets in
the module path.
