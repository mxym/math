# Additive bibliographic correction publication

This directory is a separate attribution correction for the immutable
quantitative symmetric projection-cone stability release. Its mathematical
statements, proof text, exact arithmetic checks and dependency pins are retained.
The new background credits Weil bodies, exact matroid block structure,
lift-zonoid determinant calculus and the standard nested-body cap argument.
The Boroeczky-De comparison is deliberately qualitative. The original positive
power is 1/(6d), the obstruction excludes powers above 1/d, and the gap is open
within this corrected release. Later exponent-improvement research is separate.

## Public package boundary

RELEASE_WHITELIST.txt lists every permitted path relative to this directory.
SOURCE_MANIFEST.json hashes the source payload; MANIFEST.json additionally
hashes the source manifest and article PDF. A manifest does not hash itself.
The packaging program uses an exact source list; it does not collect arbitrary
files found in code, corrections, results or build directories. Archive entries
are rooted at notes/quantitative-symmetric-projection-stability-bibliographic-correction.

The package contains no private filesystem locator, private Library identifier,
receipt download URL, external checkout, unpublished research or third-party
full paper. The v4 before/after review copies are the author's own authorized
numbered manuscript; cited external works are linked and summarized only.

## Integration

Add exactly this directory and its whitelisted files as a new note. Preserve
all earlier releases and their identifiers. Do not overwrite the earlier note,
change dependency pins or copy build intermediates. The v4 attribution patch
is review material in corrections; applying it to the numbered v4 manuscript
is a separate change and is not part of this additive package.

After any catalogue update that has been authorized separately, link this note
from the existing upper-end stability entry and describe it as an attribution
correction with unchanged mathematics. Keep it distinct from later stronger
stability supplements. Recheck the whitelist and hashes immediately before
upload or commit. This preparation itself makes no upload, commit or push.

## Reproduction

Run python3 code/check_editorial.py and python3 code/verify.py with output below
build or in a separate directory. Run sh build.sh for the article. Run
python3 code/package_release.py to recreate deterministic source and complete
archives in dist. The archive payload remains fixed despite generated build
or dist files. The recorded toolchain is in BUILD.md.
