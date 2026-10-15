# Internal AI written-proof review

This compact review record accompanies *The finite-block cost of universality in entanglement extraction*. It is an internal AI written-proof review, separately tasked from the author construction. It is not external human peer review, end-to-end Lean verification, or a priority certificate.

The reviewed PDF has 21 pages and SHA-256:

`76567b010523b15642cdb59e4c4d189dc1ccc79467650c1362534822d28e748f`

All eight TeX files received a complete mathematical read in the preceding frozen version. The final revision was independently compared against every file: only two headings and a table's alignment changed. PDF pages 1-14 render identically to the previously inspected pages; revised pages 15-21 were individually inspected. No unresolved mathematical, reference, or layout blocker was identified within this review's scope.

The directory contains the review, exact manuscript bindings, a read ledger, a formatting-only patch and validation records. It contains no external full papers, personal workspace paths or third-party datasets. Mathematical sources and the two independently scoped Lean packages are supplied separately in the manuscript's reproduction bundle.

From this directory, check this review subset with:

```sh
python3 verify_bindings.py
```

To check the actual manuscript bytes as well, supply its directory:

```sh
python3 verify_bindings.py --manuscript PATH_TO_MANUSCRIPT
```

The checker uses only the Python standard library. It checks hashes; it does not prove the mathematics, reproduce visual judgment or run Lean. The manifest is an integrity record, not a digital signature.
