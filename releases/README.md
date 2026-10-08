# Public research releases

On 8 October 2026 the repository owner reported enabling GitHub release
immutability and authorized future major, fully proved research results
to be published through immutable releases. Ordinary research progress
can continue through reviewed files and commits without creating a release.

For a qualifying release:

1. Finish the complete theorem, proof, stated dependencies and reproducible
   verification materials; distinguish experimental data and partial Lean
   checks from the proved mathematical endpoint.
2. Bind the final files and attachments to a full commit SHA and SHA-256
   manifest. Prepare the release notes and all assets in a draft before
   publication, since an immutable release's attachments cannot be replaced.
3. Publish against that exact commit, then query the resulting release and
   verify `immutable: true`, the tag/commit binding, asset hashes and GitHub's
   generated release attestation. Preserve the public URL and API metadata.
4. Publish later corrections or stronger versions in a new release, with
   explicit links to the earlier version. Do not alter the locked disclosure.

The owner's setting report is not a recorded API verification of a new
release. Enabling the setting does not retroactively make existing releases
immutable. Release metadata and attestations strengthen evidence of what was
publicly disclosed and when; mathematical priority also depends on the
actual proof and earlier literature, so an immutable timestamp alone does
not establish worldwide novelty or priority.

Official description:
https://docs.github.com/en/code-security/concepts/supply-chain-security/immutable-releases
