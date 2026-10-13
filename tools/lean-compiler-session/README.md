# Lean development compiler session

This is an editor-like diagnostic facility for the authorized tree formalization
when the desktop compiler host is unavailable. It is NOT the independent proof
verification workflow and a successful session job is NOT a proof certificate.

A validated JSON request on the dedicated input branch supplies Lean sources
and a module build order. Every request uses a separate work directory. Successful owned objects may be
reused only under exact source and recursive owned-dependency keys; object bytes
are rehashed before reuse. This incremental mode is development diagnostics only;
external dependencies remain pinned. A compiler error is recorded explicitly
in the corresponding receipt. No arbitrary shell command is accepted as input.
Authentication is used only by the driver, not passed in the compiler environment.

The driver publishes source hashes, exact compiler exit codes, and literal
errors to a dedicated results branch. It stops on an explicit stop request or
a 55-minute session limit. Source compilation is still only development evidence:
the separate hydrology-tree-lean.yml workflow must perform the final clean Lake
build, full axiom audit, trust-zero replay, and negative controls.

Development cache keys include the pinned toolchain/dependency manifest, module
name, source bytes and every direct owned dependency key (recursively binding
the full owned import closure). Changed source invalidates all dependent keys.
Failed compilations are never cached. The separate formal-verification workflow
is unchanged: fresh Lake tree, fresh module compilation, axiom audit, trust-zero
kernel replay and deliberate false-source controls. Development cache hits are
explicitly recorded and never described as independent proof certificates.
