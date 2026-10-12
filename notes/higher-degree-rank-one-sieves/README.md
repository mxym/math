# Higher-degree arithmetic sieves

A self-contained supplement on rank-one finite-state completion, arbitrary-order
irreducible restoration, and two exact cubic examples in Z[theta], theta^3=2.

## Results and scope

- A complete periodic quotient with closed-walk voltage rank at most one in each
  component can be completed by finitely many norm-prime principal ideals.
  The initial rank-one gate is a hypothesis, not a theorem for arbitrary steps.
- F6 = {+/-1, +/-theta, +/-theta^2}: exact avoiding maximum 6, supplied period
  ideal index 30, three generators.
- F8chain = F6 union {+/-(theta+theta^2)}: exact avoiding maximum 56, supplied
  period ideal index 330, four generators. The quotient has 32 undirected cycles;
  every labelled directed edge nevertheless has exactly zero section voltage.
- Every single additional proper principal ideal fails to complete the fixed
  two-ideal F8chain zigzag gate. Two-prime CRT slabs complete it.
- The stronger associate-class intersection constant is k^2 * 2^{16(r+1)}, with
  r=r_1+r_2-1 for every order. It restores irreducible component cardinality
  bounds of 4,825,576,145,682,469 for F6 and 46,926,635,792,162,881,985 for
  F8chain. The smaller maxima 6 and 56 concern avoiding graphs.

There is no claim for arbitrary bounded steps, the 26-neighbor graph, a universal
higher-degree moat, globally minimal periods, mathematical priority, or formal
proof verification. Component cardinalities are not asserted as moat radii.

## Read first

- [paper.md](paper.md): full proof and exact hypotheses
- [paper.pdf](paper.pdf): typeset reading copy
- [SOURCE_MAP.md](SOURCE_MAP.md): theorem-to-source map, imported results, frozen
  provenance, and exact public-derivative changes
- [AUDIT.md](AUDIT.md): independent mathematical/finite-certificate audit and
  schema-hardening status

The JSON certificates are complete supplementary proof data, including all
states and exact integer lift sections. They are byte-identical to the audited
originals. The author checkers were hardened only in public derivative copies;
[original-verifiers/](original-verifiers/) preserves original checker bytes.

## Reproduce

Python 3.9 or later and its standard library suffice. From this directory:

    python3 tools/reproduce.py

This verifies the exact file whitelist, SHA-256 hashes, preserved certificate
hashes, original-checker hashes, exact derivative diffs, and saved result bytes.
It reruns both public author-derived checkers, the independent checker, and
metadata-regression controls normally and with python -O. Their results must
match in both modes. All validation remains active under optimization.

To make a deterministic archive outside the package directory:

    python3 tools/reproduce.py --archive /tmp/higher-degree-rank-one-sieves.tar.gz

The archive contains exactly the whitelist, under one package-root directory,
with sorted paths, fixed metadata and a zero gzip timestamp. Repeating the
command on unchanged files produces identical archive bytes. Any changed,
missing or unexpected regular file causes verification to fail. The package
contains no generated cache files or external dependencies.

Individual checks can also be run directly:

    python3 -B check_cubic_certificate.py
    python3 -B check_rank_one_f8_certificate.py
    python3 -B independent_check.py
    python3 -B tools/check_metadata_controls.py

The public author derivatives reject 17 built-in negative controls each. The
independent checker rejects 15 targeted controls for each certificate, with a
separate three-case metadata regression per certificate. The historical checker
regression is deliberately run on isolated unchanged copies: it confirms the
schema weakness and then confirms rejection by both strict implementations.

## Manifest convention

MANIFEST.json contains the exact whitelist and hashes of every payload file.
It excludes its own digest and that of SHA256SUMS from its payload hash list
(to avoid self-reference). SHA256SUMS hashes every whitelisted file except
itself, including MANIFEST.json. The reproduction script checks both layers.
These integrity records do not constitute a cryptographic signature.

The PDF is a supplied verified reading copy. Reproducing the mathematical
checks and deterministic archive requires only Python. Regenerating the PDF is
optional and additionally needs ReportLab:

    python3 tools/render_pdf.py

PDF regeneration is not part of the immutable-package check because rendering
software versions can affect PDF bytes. If any published file is edited, the
package's integrity records must be deliberately regenerated after review.
