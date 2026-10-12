#!/usr/bin/env bash
# Rebuild the revised source in an isolated temporary directory.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [[ $# -ne 1 ]]; then echo "Usage: bash verification/build_pdf.sh OUTPUT_DIRECTORY" >&2; exit 2; fi
mkdir -p "$1"
OUT="$(cd "$1" && pwd)"
BUILD="$(mktemp -d)"
trap 'rm -rf "$BUILD"' EXIT
cp "$ROOT/synthesis.tex" "$BUILD/synthesis.tex"
cd "$BUILD"
# A fixed epoch removes time-dependent PDF metadata. Shell escape is disabled.
export SOURCE_DATE_EPOCH=1791331200 FORCE_SOURCE_DATE=1 TZ=UTC
export TEXMFVAR="$BUILD/texmf-var" TEXMFCONFIG="$BUILD/texmf-config"
# Normal TeX installations use the standard filename database and format.
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  # Fallback for an installed Debian TeX tree without generated databases.
  test -f /usr/share/texlive/texmf-dist/tex/latex/tex-ini-files/pdflatex.ini
  export TEXMF='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
  pdftex -ini -etex -no-shell-escape -jobname=pdflatex '\input pdflatex.ini' >format-build.stdout 2>&1
  cat /usr/share/texmf/fonts/map/dvips/lm/lm.map /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/*.map >pdftex.map
  export TEXFORMATS="$BUILD:" TEXFONTMAPS="$BUILD:/usr/share/texmf/fonts/map//:/usr/share/texlive/texmf-dist/fonts/map//:"
fi
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape synthesis.tex >pass1.stdout 2>&1
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape synthesis.tex >pass2.stdout 2>&1
if grep -Eq '(^!|Undefined control sequence|LaTeX Warning:.*undefined|Overfull \\[hv]box)' synthesis.log; then
  cat synthesis.log >&2; exit 1
fi
pdftotext -layout synthesis.pdf synthesis.txt
pdfinfo synthesis.pdf >pdfinfo.txt
cp synthesis.pdf synthesis.txt pdfinfo.txt "$OUT/"
# Logs can expose installation paths; they remain local rebuild diagnostics only.
cp synthesis.log pass1.stdout pass2.stdout "$OUT/"
echo 'PASS: revised TeX rebuilt in isolation with shell escape disabled.'
