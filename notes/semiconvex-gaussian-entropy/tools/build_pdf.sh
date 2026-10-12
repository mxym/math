#!/usr/bin/env bash
# Build outside the immutable package; requires pdfTeX and Poppler.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUTPUT="${1:-$(mktemp -d -t semiconvex-entropy-build.XXXXXX)}"
mkdir -p "$OUTPUT"
OUTPUT="$(cd "$OUTPUT" && pwd)"
if [[ "$OUTPUT" == "$ROOT" || "$OUTPUT" == "$ROOT/"* ]]; then
  echo 'Use an output directory outside this package.' >&2
  exit 2
fi
cp "$ROOT/entropy.tex" "$OUTPUT/entropy.tex"
cd "$OUTPUT"
export SOURCE_DATE_EPOCH=1791331200
export FORCE_SOURCE_DATE=1
export TZ=UTC
PDFLATEX=(pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -jobname=entropy)
if ! "${PDFLATEX[@]}" '\def\DoNotLoadEpstopdf{}\input{entropy.tex}' > build-pass1.txt 2>&1; then
  # A minimal TeX distribution may lack a precompiled format or font map.
  # Rebuild them only in OUTPUT, without changing the installed TeX tree.
  DIST=/usr/share/texlive/texmf-dist
  EXTRA=/usr/share/texmf
  [[ -f "$DIST/tex/latex/tex-ini-files/pdflatex.ini" ]]
  export TEXINPUTS="$DIST/tex//:$EXTRA/tex//:"
  export TFMFONTS="$DIST/fonts/tfm//:$EXTRA/fonts/tfm//:"
  export VFFONTS="$DIST/fonts/vf//:$EXTRA/fonts/vf//:"
  export T1FONTS="$DIST/fonts/type1//:$EXTRA/fonts/type1//:"
  export ENCFONTS="$DIST/fonts/enc//:$EXTRA/fonts/enc//:"
  export TEXFONTMAPS="$OUTPUT:$DIST/fonts/map//:$EXTRA/fonts/map//:"
  cat "$EXTRA/fonts/map/dvips/lm/lm.map" "$DIST"/fonts/map/dvips/amsfonts/*.map > pdftex.map
  pdftex -ini -etex -no-shell-escape -interaction=nonstopmode -halt-on-error \
    -jobname=pdflatex "$DIST/tex/latex/tex-ini-files/pdflatex.ini" > format-build.txt 2>&1
  PDFLATEX=(pdflatex -fmt="$OUTPUT/pdflatex.fmt" -no-shell-escape -interaction=nonstopmode -halt-on-error -jobname=entropy)
  "${PDFLATEX[@]}" '\def\DoNotLoadEpstopdf{}\input{entropy.tex}' > build-pass1.txt 2>&1
fi
for pass in 2 3; do
  "${PDFLATEX[@]}" '\def\DoNotLoadEpstopdf{}\input{entropy.tex}' > "build-pass${pass}.txt" 2>&1
done
if grep -Eq 'Warning|Overfull|Underfull|undefined|Fatal' build-pass3.txt; then
  grep -E 'Warning|Overfull|Underfull|undefined|Fatal' build-pass3.txt >&2
  exit 1
fi
[[ "$(pdfinfo entropy.pdf | awk '/^Pages:/ {print $2}')" == 9 ]]
pdftotext -layout entropy.pdf entropy.txt
printf 'PASS: nine-page PDF, no final-pass warnings; shell escape disabled.\nOutput: %s/entropy.pdf\n' "$OUTPUT"
