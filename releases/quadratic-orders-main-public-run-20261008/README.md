# Completed public-source reproduction: quadratic orders Main

The exact source package with SHA256 `8e16e2191c788738dbe3592578fb8c4a09082215ec373ff8d87201fbe6a15e6f` passed its public verifier end to end, from a new output directory. The public program exited zero and printed its final `QUADRATIC_ORDERS_MAIN_PUBLIC_REPLAY_PASS` marker. The emitted output-manifest hash was then checked by the real read-only checker in both normal and optimized Python.

The run freshly compiled **995 CFT modules, 129 main-library units and five arithmetic bridges**. No previous owned or CFT objects were reused, and no restart/resume occurred. All 7,000 official/toolchain cached modules matched the sealed source/artifact reference; this is not a complete fresh rebuild of Lean or mathlib.

The endpoint is `Entry002.arithmeticSupply_mainTarget_proved : Entry002.MainTarget`, accessed through `import ArithmeticSupplyWeakMain`. Its **125,368-constant** stored closure passed a genuinely empty kernel replay at trust level zero, using only `propext`, `Classical.choice` and `Quot.sound`. The combined inventory and nonpartial closure matched the prior independent certificate; the seven documented partial compiler helpers remain excluded as proof roots.

- Started: 2026-10-08T00:24:59.919522+00:00
- Public verifier finished: 2026-10-08T03:23:40.544773+00:00
- Terminal output checks finished: 2026-10-08T03:24:22.283192+00:00
- Original completed-run output manifest SHA256: `76db4a5a82937d9cb00506acbcb756447eade6426082600cc3f68eb5ee19c761`

See [the receipt](RECEIPT.json), [fresh build ledger](FRESH_BUILD_LEDGER.json.gz), [kernel result](LITERAL_MAIN_EMPTY_KERNEL.json) and [source/reproduction instructions](../../formalizations/quadratic-orders-main/README.md). The two full declaration-name arrays are already in the sealed source package under `audit/independent/`; this run's arrays matched those bytes exactly and are not duplicated here.

## Evidence and remaining scope

These are compact public records of the completed execution, with host paths normalized. `PROVENANCE.json` records original and public digests. Compiled objects and large official caches are intentionally not committed. This folder alone is not an offline binary-output verification bundle: reproduce with the sealed source runner, then check that run's actual output directory and independently retained manifest hash. `RUN_OUTPUT_INTEGRITY_PASS` reports artifact integrity, not a second kernel proof. A lone intermediate `FINAL_VERIFICATION.json` is insufficient; the zero exit, final marker, output seal and successful checks were all required here.

The original natural-density/PNT endpoints, an effective bound algorithm, originality and journal suitability are not conclusions of this run. This local preparation does not itself establish that a GitHub publication happened.
