# Reproduction interface and trust boundary

The exact successful commands, working directories, exit codes, source hashes,
object hashes and compiler identity are in the two build ledgers and run records.
The archived scripts preserve the actual execution configuration; they are not
claimed to be a separately tested portable fresh runner. Absolute workspace paths
must be explicitly relocated when replaying elsewhere. Mathematical source bytes
must not be changed during relocation.

## Inputs

1. Verify the original source ZIP SHA recorded in BUNDLE_RECEIPT.json and safely
   extract it as source/. The ZIP is included under inputs/ in this audit bundle.
2. Supply Lean 4.34.1 at compiler commit
   5045d0056413266e57c625dcd7c365b10e377c52, and the clean official package sources
   at every revision in the original lake-manifest.json. The exact Linux binary
   used here is recorded, not asserted to be a cross-platform binary identity.
3. Supply a read-only official cache at those pins, or rebuild it. This audit did
   not rebuild all official modules. The manifests distinguish 113 new main
   official modules, the shared independently compiled 457, and older official
   cache inputs.
4. Use an empty owned output root. Compile all 129 main units from their actual
   import DAG with `lean -DautoImplicit=false -o OUTPUT SOURCE`. Do not put an old
   Entry002 cache on LEAN_PATH. The independent preflight records all sources.
5. Rebuild the exact 995 CFT module graph from the bundled CFT source and compatible
   pins/patches, or explicitly authenticate the independently fresh objects in
   shared_cft_evidence/. This audit did the latter after exact source/compiler
   matching. The original 1456-module ledger also includes 457 official and 4 old
   bridge builds. It is not an author cache certificate.
6. On the new Entry002 objects, compile the five bridge modules in this order:
   ArithmeticSupplyRayBridge, ArithmeticSupplyRayConductor,
   ArithmeticSupplyWeakFromDirichlet, ArithmeticSupplyWeakMainReduction,
   ArithmeticSupplyWeakMain. Actual source locations and flags are in the ledger.

## Checking

The successful mathematical LEAN_PATH was an ordered union of:

- new five-bridge object root
- new Entry002 object root
- sparse read-only official view plus newly compiled official objects
- independently fresh CFT object root
- stock Lean standard library

The audit-tool directory was prepended only for checking tools. Actual resolved
paths were checked, rather than assuming search-path order sufficed.

With that path and the pinned lean binary:

- Compile AuditCore.lean and EmptyKernelReplay.lean from the audit-tool directory.
- Run RunMainAudit.lean and validate_audit.py for its actual output.
- Compile ExternalAuditCore.lean, run RunExternalAudit.lean and
  validate_external_audit.py. These inspect module-index-owned declarations,
  stored values/types and every actual dependency, including private/opaque ones.
- Run ReplayLiteralMain.lean. It insists on the exact no-premise MainTarget type,
  rejects nonstandard axioms or unsafe/partial dependencies, then calls official
  Kernel.Environment.replay on the entire selected closure in mkEmptyEnvironment 0.
- Check standard axiom types against StockStandardAxioms.lean's Lean-only baseline
  using the precompiled StockAxiomSnapshot.lean and CheckLiteralStandardAxioms.lean.
- Run the corrected CheckCombinedOwned.lean for all 134 modules. It inventories
  every declaration but seeds the logical union with nonpartial declarations;
  it still rejects any partial/unsafe dependency in that union.

The successful negative controls and the initial, correctly rejected all-inventory
seed attempt are preserved separately. Do not import these deliberately invalid
controls into a mathematical library, nor mistake their expected failures for
failures of Main.

The original unrelocated scripts were actually run. A later release may provide
path-only adapters, but those must be marked as derived and must not be described
as another completed 995-module rebuild or 125368-constant kernel run unless those
operations really occur. The independent Main proof result is not the author's
historical object-byte validation mode; different fresh objects need their own
source/command/log/object record and real declaration/kernel checks.

## Not claimed

No second kernel implementation; no full Mathlib/Lean rebuild; no effective Main
algorithm; no closed old natural-density/PNT supply target; no endpoint replay of
all 2906 safe roots as one merged kernel job. Partial code-generation auxiliaries
are inventoried but are absent from all certified logical closures.
