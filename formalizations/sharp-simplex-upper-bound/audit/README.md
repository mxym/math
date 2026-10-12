# Audit evidence scopes

`independent/` contains privacy-sanitized copies of the final complete 204-file composition audit, including the exact 123-source inventory, 848 public proofs, 1,833 actual owned declarations and both empty trust-zero replay logs. Large inventories use deterministic gzip. The original report and original evidence-manifest hashes are retained in INPUT_COMPOSITION.json and the derivative ledger. Historical audit manifests are not validators for this repackaged release.

`checks/` contains the actual independent Lean programs, including literal and negative controls and two recursive empty-kernel replayers. These execute again in the recommended production verifier against freshly built public sources. `mathematical/` supplies the independent traditional argument review and exact finite corroboration; it never claimed to replace the kernel audit. `historical/` contains the superseded author replay that defaulted to 20 incremental modules. Do not use it to certify this release.

The lower truncation-sharpness audit is separate. Its completion and the upper Main completion should be stated separately, without treating a historical lower checkpoint's open-Main comment as the overall current result.
