# Exact-source review and editorial changes

The independent sign-off applies to the complete compact-data source with SHA-256 `757d0ba430e52cfcfd98c5e78afe59150970e7897e99516efdb92adc42d1ab21`. It found no required mathematical correction, independently reconstructed that exact source, checked the entire statement and proof, and rebuilt its ten-page PDF. The unchanged certificate is included as [audits/exact-source-signoff.txt](audits/exact-source-signoff.txt). It is a model review, not external peer review or a novelty certification.

This public copy has SHA-256 `a0b8068ff29c76a319e81495f38e11dc0437844723aaa7aa11b26dbb102db695`. Only three review-status locations changed:

1. PDF subject metadata now records the completed compact-source model review.
2. The opening review paragraph records the completed exact-source check.
3. The appendix status sentence records completion and excludes Gaussian-data extensions and matched-layer strengthening.

Replacing these three old/new spans by the same markers makes the entire old and public TeX sources byte-identical. All 12 mathematical theorem, lemma, proposition and proof environments are independently byte-identical. No assumption, equation, proof, constant, norm, endpoint statement, or bibliography entry changed. The normalized source hash is `484fff5fa81a3bbf51d2d193e9f44cf4ff83d093d47c5c9bbba16a4efda96a35`.

The pending Gaussian and matched-layer projects are separate work and are not included in this package. The unsummed unit-amplitude mean correction remains open. Historical review hashes are provenance; the classical mathematical inputs are public and mapped in DEPENDENCIES.md.

For an independent byte check run `python3 verify_review.py`. The three exact substitutions are supplied in editorial-status-changes.json. The verifier reverses them in memory and must recover the certificate's original source hash; it makes no network request and writes no file.
