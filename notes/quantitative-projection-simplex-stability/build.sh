#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build
export SOURCE_DATE_EPOCH=1791324000
if ! kpsewhich article.cls >/dev/null 2>&1 || ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  BASE=/usr/share/texlive/texmf-dist
  EXTRA=/usr/share/texmf
  test -f "$BASE/tex/latex/tex-ini-files/pdflatex.ini"
  CACHE="$PWD/build/tex-cache"
  mkdir -p "$CACHE/config" "$CACHE/var"
  export TEXMF="{$BASE,$EXTRA}"
  export TEXINPUTS=".:$BASE/tex//:$EXTRA/tex//:"
  export TFMFONTS="$BASE/fonts/tfm//:$EXTRA/fonts/tfm//:"
  export VFFONTS="$BASE/fonts/vf//:$EXTRA/fonts/vf//:"
  export T1FONTS="$BASE/fonts/type1//:$EXTRA/fonts/type1//:"
  export ENCFONTS="$BASE/fonts/enc//:$EXTRA/fonts/enc//:"
  export TEXFORMATS="$CACHE:"
  export TEXFONTMAPS="$CACHE:$BASE/fonts/map//:$EXTRA/fonts/map//:"
  export TEXMFVAR="$CACHE/var"
  export TEXMFCONFIG="$CACHE/config"
  if [ ! -f "$CACHE/pdflatex.fmt" ]; then
    (cd "$CACHE" && pdftex -ini -etex -interaction=nonstopmode -halt-on-error \
      -jobname=pdflatex "$BASE/tex/latex/tex-ini-files/pdflatex.ini" >format-build.txt 2>&1)
  fi
  cat "$EXTRA/fonts/map/dvips/lm/lm.map" \
      "$BASE/fonts/map/dvips/amsfonts/cm.map" \
      "$BASE/fonts/map/dvips/amsfonts/symbols.map" >"$CACHE/pdftex.map"
fi
pandoc paper.md --standalone --from=markdown+tex_math_dollars --to=latex \
  --include-in-header=header.tex --lua-filter=layout.lua --variable=fontsize:11pt \
  --variable=geometry:margin=0.85in --variable=linestretch:1.04 \
  --output=paper.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build paper.tex >build/pass1.txt
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build paper.tex >build/pass2.txt
cp build/paper.pdf paper.pdf
printf '%s\n' 'Built paper.pdf from paper.md; inspect rendered pages before release.'
