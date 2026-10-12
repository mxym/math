# Retained audit evidence

`independent/` contains compact results of the original 125-module independent audit. `checks/` contains its seven Lean checking programs unchanged. `predecessor/` records the earlier 102-module/714-public-proof geometry bridge audit. The public verification runner is a separately derived tool, not a claim that the original audit drivers were portable.

Large original ownership and import inventories are retained once as deterministic gzip files. Their uncompressed JSON has not been edited. No dependency `.olean` cache is bundled. The original submitted project contains its own compact historical build/axiom logs. Additional duplicated independent compiler logs are omitted; the public runner regenerates them outside the package.

Public copies of prose reports and two negative-control logs replace private artifact identifiers and machine-local paths with explanatory placeholders; the original and public SHA-256 values are in `../provenance/PUBLIC_DERIVATIVE_LEDGER.json`. An unqualified `checks/` or `logs/` path in a retained historical report refers to that audit's original layout. In this public copy, result JSON and retained logs are in `independent/`, Lean probes in `checks/`, and compressed inventories end in `.json.gz`. `build.json` and `fresh-output-resolution.json` preserve the original per-module compile and resolution results. Fresh replay output is generated separately.

The retained reports certify their stated mathematical snapshot. The public derivative's packaging controls and final-copy build results are reported separately, so original audit success is never silently treated as an audit of new packaging tools.
