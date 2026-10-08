#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# A normal TeX installation needs only pdflatex. To reuse an already
# prepared custom format/font-map directory, set LOCAL_TEX_DIR explicitly.
local_tex=${LOCAL_TEX_DIR:-}
if [[ -n "$local_tex" ]]; then
  if [[ ! -f "$local_tex/pdflatex.fmt" ]]; then
    echo 'LOCAL_TEX_DIR must contain an existing pdflatex.fmt.' >&2
    exit 2
  fi
  export TEXMF=${TEXMF:-/usr/share/texlive/texmf-dist}
  export TEXFONTMAPS="$local_tex//:${TEXFONTMAPS:-}"
  tex=(pdflatex "-fmt=$local_tex/pdflatex.fmt")
else
  tex=(pdflatex)
fi
for pass in 1 2; do
  "${tex[@]}" -interaction=nonstopmode -halt-on-error paper.tex > "build-pass${pass}.log" 2>&1
done
if grep -Eq 'undefined references|undefined citations|Overfull|^!' build-pass2.log; then
  echo 'Inspect build-pass2.log before publication.' >&2
  exit 1
fi
mkdir -p qa
pdftoppm -scale-to 1600 -png paper.pdf qa/page
pdftotext -layout paper.pdf qa/paper.txt
pdfinfo paper.pdf > qa/pdfinfo.txt
printf 'Built paper.pdf and rendered all pages in qa/.\n'
