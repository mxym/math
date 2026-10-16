# Actual matrix projector from a known complex subspace

This independent Lean 4.34.1 / pinned Mathlib package has no quantum-protocol or
symmetric-support dependency. `MatrixSubspace.exists_subspace_projection S`
internally constructs an actual Hermitian idempotent P with range S, matrix rank
exactly finrank S, and P*v=v for every v in S. The proof uses a finite basis and
its Gram matrix; invertibility and every matrix identity are proved internally.
It makes no performance, rank or orthonormality assumption about the caller.
This is a separately compiled new scope; final audit bindings are being prepared.
Earlier fixed quantum and APPT audits remain unchanged.
