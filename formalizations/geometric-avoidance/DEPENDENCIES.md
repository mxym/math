# Pinned dependencies and retained notices

Maintained in mxym/math; developed with AI assistance.

This inventory records the inputs to the geometric-avoidance Lean proof. It does not grant a new license for the original proof. The repository's existing attribution policy is preserved in [NOTICE.md](NOTICE.md).

## Exact source pins

The authoritative dependency lock is `lake-manifest.json`. Its SHA-256 is `e47bfb25c8cdba035776c5a96f08b553d005d6e8d0d05e2861d60bde895ed7a2`. Mutable `inputRev` labels in that file are descriptive inputs; the exact `rev` values below are the reconstruction pins. Reproduction must retain the lock and verify every materialized checkout against it, rather than run an unrestricted `lake update`.

| Package | Exact revision | Upstream repository | Retained license |
| --- | --- | --- | --- |
| mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` | [mathlib4](https://github.com/leanprover-community/mathlib4) | [Apache-2.0](third_party_licenses/mathlib/LICENSE) |
| plausible | `118aa17ee84656b8bd727fef7c458ee8c833385c` | [plausible](https://github.com/leanprover-community/plausible) | [Apache-2.0](third_party_licenses/plausible/LICENSE) |
| LeanSearchClient | `ddf04cf3949fa556442341e87d47f9f6e6074707` | [LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient) | [Apache-2.0](third_party_licenses/LeanSearchClient/LICENSE) |
| importGraph | `e928b72544873815af278d38681b31c0293588e3` | [import-graph](https://github.com/leanprover-community/import-graph) | [Apache-2.0](third_party_licenses/importGraph/LICENSE), plus [MIT HTML-template notice](third_party_licenses/importGraph/html-template/LICENSE_source) |
| proofwidgets | `106ff4fafc74ef4ac99d81dbf3ab399118f497a5` | [ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4) | [Apache-2.0](third_party_licenses/proofwidgets/LICENSE) |
| aesop | `355695d523e41d0554926416cba2a2b3544fbbc9` | [aesop](https://github.com/leanprover-community/aesop) | [Apache-2.0](third_party_licenses/aesop/LICENSE) |
| Qq | `6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259` | [quote4](https://github.com/leanprover-community/quote4) | [Apache-2.0](third_party_licenses/Qq/LICENSE) |
| batteries | `f2effa3d803fda822b1f97b806c47cf2adfbcbc2` | [batteries](https://github.com/leanprover-community/batteries) | [Apache-2.0](third_party_licenses/batteries/LICENSE) |
| Cli | `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204` | [lean4-cli](https://github.com/leanprover/lean4-cli) | [MIT](third_party_licenses/Cli/LICENSE) |

The package license files were copied from already downloaded upstream Git checkouts. For each file, its bytes were compared with the Git object at the exact manifest commit; each checkout's origin URL and HEAD were also checked. No dependency source was modified. Copyright and authorship information in the retained notices remains intact; source-level attributions remain with the corresponding upstream sources.

## Lean toolchain

- Toolchain declaration: `leanprover/lean4:v4.34.1`
- Reported official source commit: `5045d0056413266e57c625dcd7c365b10e377c52`
- Linux x86_64 bootstrap: [official Lean 4.34.1 archive](https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst)
- Archive SHA-256: `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`
- Retained files: [Lean LICENSE](third_party_licenses/lean4/LICENSE) and the complete [distribution LICENSES](third_party_licenses/lean4/LICENSES)

The binary distribution's component notices cover additional software, including LLVM, the GNU C Library, GNU MP, CaDiCaL, and leantar. Those components must not all be described as Apache-2.0. The full distribution notice is retained without editing. The license files were copied from the installed official-version distribution; this documentation pass did not re-download the toolchain archive. Its archive hash comes from the independently audited reproduction source, and the bootstrap is expected to check it before extraction.

The source release does not vendor the toolchain, dependency source trees, or compiled caches. The online reproduction path retrieves official dependency build caches using the pinned mathlib cache program. Thus the reproduction is an own-source rebuild with upstream dependency-cache trust, not a from-source rebuild of the compiler and all dependencies. System curl >= 7.81 avoids the pinned cache program's fallback download of an additional static-curl helper; leantar is supplied by the hash-pinned Lean distribution.

## Machine-readable verification

[DEPENDENCY_PROVENANCE.json](DEPENDENCY_PROVENANCE.json) records repository URLs, exact revisions, immutable license-source links, license file SHA-256 values, Git blob identifiers where available, and the limits of each verification claim. [third_party_licenses/SHA256SUMS](third_party_licenses/SHA256SUMS) covers all included notice texts plus this provenance record. From this project directory:

```sh
sha256sum -c third_party_licenses/SHA256SUMS
```

This notice inventory is scoped to the pinned Lean source packages, the bundled Lean distribution notices, and the collection's inherited OpenAI/math material. It is not an assertion that arbitrary future vendored binaries or rebuilt web-widget distributions need no additional notices.
