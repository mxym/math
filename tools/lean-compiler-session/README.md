# Lean development compiler session

This is an editor-like diagnostic facility for the authorized tree formalization
when the desktop compiler host is unavailable. It is NOT the independent proof
verification workflow and a successful session job is NOT a proof certificate.

A validated JSON request on the dedicated input branch supplies Lean sources
and a module build order. Every request starts with zero owned object files;
external dependencies remain pinned. A compiler error is recorded explicitly
in the corresponding receipt. No arbitrary shell command is accepted as input.
Authentication is used only by the driver, not passed in the compiler environment.

The driver publishes source hashes, exact compiler exit codes, and literal
errors to a dedicated results branch. It stops on an explicit stop request or
a 55-minute session limit. Source compilation is still only development evidence:
the separate hydrology-tree-lean.yml workflow must perform the final clean Lake
build, full axiom audit, trust-zero replay, and negative controls.
