# Reproduce the frozen APPT scalar certificate package

The two exact replayers use Python 3.10 or later and only the standard library.
They do not require Lean, Lake, Mathlib, mpmath or SymPy. Copy files with
copyfile into fresh private scratch directories so output files are writable;
leave all frozen originals and their UTC-bound certificate bytes untouched.

Verify SOURCE_INPUTS.json and the per-scope manifests before running. The
claimed mathematical review scope includes the manuscripts and analytic tail
arguments, not just successful program execution.

## Critical uniqueness, 73 exact leaves

Copy these files to one fresh scratch directory:

    critical_exact_intervals.py
    CRITICAL_EXACT_INTERVAL_CERTIFICATE.json
    CRITICAL_UNIQUENESS_CERTIFICATE.md
    replay_critical_certificate.py

From that scratch directory run:

    python replay_critical_certificate.py

Expected: AUTHOR_REPLAY_SUCCESS, 73 leaves, source/certificate/paper hashes
matching the manifest. It verifies four full rational partitions, all stored
integer bounds, constants, the lower mixed witness and core derivatives.
The successful replay writes CRITICAL_CERTIFICATE_AUTHOR_REPLAY.json only
inside the scratch copy. Its new UTC is not expected to match the frozen
author-run log; its bound inputs and all mathematical results must match.

## Global mixed classification, 74 exact leaves including K=0 charts

Copy these files to another fresh scratch directory:

    critical_exact_intervals.py
    global_mixed_turn_certificate.py
    GLOBAL_MIXED_TURN_CERTIFICATE.json
    GLOBAL_MIXED_PHASE.md
    replay_global_turn_certificate.py

Run:

    python replay_global_turn_certificate.py

Expected: AUTHOR_GLOBAL_TURN_REPLAY_SUCCESS, 74 leaves in six covers with
counts 35,1,28,5,1,4. The middle cover has 21 negative leaves and seven
explicit leaves outside the cap K<=13/25. The replay recomputes all exact
integer sign bounds and verifies each entire two-dimensional partition by
an exact rational axis sweep; its final one-dimensional partition uses
exact adjacency. K=0 is included, with the removable E_p functions and
their controlled Taylor tails. It writes GLOBAL_MIXED_AUTHOR_REPLAY.json
only in scratch.

## Mathematical and code reading required

The complete reading order is LAST_MIXED_BOUNDARY.md, NO_ISLANDS.md,
CRITICAL_UNIQUENESS_CERTIFICATE.md and GLOBAL_MIXED_PHASE.md. Read the
bound L/S scientific inputs for their original density/APPT quantifiers,
first-nonzero nearoptimality and all three losses. Read both exact engines,
both replayers and both certificates, including all closed-domain tails,
removable K=0 charts, constrained h boundary and cap intersections.

The producer files contain main routines that create certificates with a
fresh UTC. A reviewer may regenerate them in a separate disposable scratch
copy and compare the full mathematical leaves and source hashes, but must
not regenerate an original frozen certificate in place. The certificates'
stored source hashes bind the exact original producer bytes.

The optional no_islands_author_controls.py and global_mixed_turn_algebra.py
use SymPy; floating discovery scripts use mpmath. They are author auxiliary
controls and are not needed for the standard-library certificate replay.
No assumption of installed versions of those optional libraries is part of
the proof. A successful optional control does not replace reading the analytic
proof or certify priority.

## Review boundary

A replay can detect a wrong bound, incomplete partition, source mismatch or
certificate alteration. It does not by itself prove that the analytic reduction
describes the original APPT problem. Ordinary independent review must check
those mathematical bridges and bind the exact manuscripts and metadata.
All new claims remain author-only until that separate review passes. There
are no new Lean roots or existing-audit changes in this package.
