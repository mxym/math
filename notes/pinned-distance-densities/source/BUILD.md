# Build and inspect

## Standard TeX installation

From this directory run:

    ./build.sh

The script runs pdfLaTeX three times with shell escape disabled, stops on errors, unresolved references/citations, missing characters, or overfull boxes, and copies the final PDF to `main.pdf`. It does not install software, download packages, or access a repository.

Dependencies: pdfLaTeX, article, geometry, fontenc, Latin Modern, amsmath, amssymb, amsthm, mathtools, microtype, xurl, hyperref, enumitem, and booktabs. A normally configured TeX Live installation supplies them.

The build fixes SOURCE_DATE_EPOCH, UTC, and the locale. Auxiliary files and all three compile transcripts are in `build/`. The final source and PDF hashes are in `SHA256SUMS`.

## This workspace's existing TeX fallback

The build script was reused from the nearby Hadamard manuscript package, with the same article/AMS-math stack used in the vertex-excess manuscript. If the standard TeX search configuration cannot locate article.cls or pdflatex.fmt, the script uses the already present system TeX trees and the existing cache at:

    ../kinetic13_manuscript_independent_audit_20261007/tex-cache

No cache is generated or downloaded. An alternative existing cache can be selected:

    TEX_CACHE_DIR=/absolute/path/to/existing/cache ./build.sh

That cache must contain `pdflatex.fmt` and `pdftex.map`. A configured standard installation does not need this workspace-specific fallback. The fallback may need adjustment on a machine with different TeX installation paths.

## Visual inspection

To regenerate one image per page with Poppler:

    mkdir -p qa
    pdftoppm -r 100 -png main.pdf qa/page

Every page must be visually inspected, not merely text-extracted. `qa/QA_REPORT.md` records the performed inspection. QA images are inspection intermediates, not separate publication deliverables.

For text and structure checks:

    pdfinfo main.pdf
    pdftotext -layout main.pdf build/main.txt
    sha256sum -c SHA256SUMS

No mathematical computation, Lean build, bibliography network request, or external publishing operation is required to compile this manuscript.
