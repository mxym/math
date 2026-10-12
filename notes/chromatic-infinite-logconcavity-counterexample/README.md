# Cycles refute chromatic infinite log-concavity

Research note and reproducibility package, 8 October 2026.

## Result

The cycle C17 gives an exact counterexample to Amdeberhan–Moll Conjecture 21 (and Amdeberhan's earlier Conjecture 13.1 in the 2022 v7 manuscript): the degree-2 entry in the third log-concavity transform is -28272276537344.

The proof extends to every cycle C_n with n >= 17 and gives the full cycle classification under standard zero extension: infinite log-concavity holds exactly for 3 <= n <= 11. C12 fails in the fifth iteration; no smallest-counterexample claim among all graphs is made. Adding isolated vertices supplies counterexamples under an endpoint-deleting convention as well.

## Read and reproduce

- [cycle_counterexample_proof.md](cycle_counterexample_proof.md): complete disproof, infinite family, boundary discussion and classification.
- [status_search_20261008.md](status_search_20261008.md): source definitions and bounded literature checks.
- [verify_cycle_counterexample.py](verify_cycle_counterexample.py), [exact_certificates.json](exact_certificates.json) and [verification_output.txt](verification_output.txt): exact main verifier, certificates and output.
- [audit/audit_report.md](audit/audit_report.md): independent source, arithmetic and mathematical audit.
- [audit/independent_verify.py](audit/independent_verify.py), [audit/independent_exact_results.json](audit/independent_exact_results.json) and [audit/verification_output.txt](audit/verification_output.txt): independent edge-subset inclusion-exclusion, integer iterations and rational-polynomial checks.
- [MANIFEST.json](MANIFEST.json) and [SHA256SUMS](SHA256SUMS): complete file inventory and integrity checks.

Run from this directory with Python 3.10 or later and no third-party dependencies:

```sh
python3 verify_cycle_counterexample.py
python3 audit/independent_verify.py
sha256sum -c SHA256SUMS
```

The scripts regenerate the corresponding JSON certificates beside their source files. The classification's infinite positive direction uses a proved invariant; its infinite negative tail uses an exact symbolic identity.

## Limits

The bounded literature search found no earlier matching disproof. The author's separate updates page could not be read, and the search does not establish worldwide novelty. The journal record's 2022 issue date and the PDF's December 2023 date are recorded separately in the source audit. No human peer review or formal Lean verification is claimed.
