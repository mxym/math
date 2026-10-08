# Independent evidence and reproduction tools

`independent/FINAL_LOADED_OBJECT_HASHES.json.gz` binds all 8,132 actually resolved modules and their recorded sidecars in the final combined independent audit. This complements the earlier main-phase object snapshot.

`independent/` contains public derivatives of completed audit records. Host-specific paths and private delivery identifiers are normalized; source, compiler and object digests are preserved. `mathematical/` contains source-semantic/traditional mathematical reviews, which are not kernel certificates or claims of external human refereeing. `checks/` contains the Lean programs used by the public fresh-source runner; only output-path portability changes and documented release checks distinguish them from the completed audit harness.

The literal Main empty-kernel replay checks 125,368 reachable constants. The root is exactly `Entry002.arithmeticSupply_mainTarget_proved`, its type is exactly `Entry002.MainTarget`, the destination begins with zero constants, and trust level is zero. A proof-corruption control changes a stored theorem body to an ill-typed term and must fail in the kernel.

Compilation provenance distinguishes 129 round-five main modules, five round-five bridges, 995 CFT modules independently built in the prior audit, the 113 and 457 freshly supplied official modules, and other pinned official cache inputs. Official cache reuse is not a full dependency rebuild. The 995-module CFT ledger's four old PNT bridges do not count as the five new round-five weak-supply bridges.

The complete combined inventory is separate from the accepted safe logical roots and stored-declaration closure. Seven compiler-generated partial `._unsafe_rec` helpers are retained and identified in the full inventory, excluded as proof roots, and rejected if reachable from the accepted roots. A failed all-inventory-as-roots control is retained to show this distinction. No blanket claim of a kernel replay of all 2,952 entries is made.

`FINAL_MATH_RESULT.json` and `ENTRY002_ROUND5_INDEPENDENT_AUDIT.md` state the completed result. Intermediate `MAIN_PHASE_PASS.json` and author-side records retain their historical narrower or pending status. The first attempt to treat every inventory entry as a proof root genuinely failed on the generated partial helpers. That failure is preserved as a boundary control. The final check distinguishes those seven helpers while still rejecting any partial or unsafe dependency reachable from an accepted proof root.

Current release packaging controls are outside the independent mathematical certificate. Read `VERIFICATION.md` and the external final-copy audit before interpreting a package as release-ready.
