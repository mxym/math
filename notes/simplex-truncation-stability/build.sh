#!/bin/sh
# Rebuild in place; no network, package installation, or source edits.
set -eu
cd "$(dirname "$0")"
mkdir -p build
export TZ=UTC
export SOURCE_DATE_EPOCH=1791331200
export FORCE_SOURCE_DATE=1
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
      "$BASE/fonts/map/dvips/amsfonts/symbols.map" \
      "$BASE/fonts/map/dvips/amsfonts/euler.map" >"$CACHE/pdftex.map"
fi
pdflatex -interaction=nonstopmode -halt-on-error -jobname=proof -output-directory=build \
  '\pdftrailerid{}\input{proof.tex}' >build/pass1.txt 2>&1
pdflatex -interaction=nonstopmode -halt-on-error -jobname=proof -output-directory=build \
  '\pdftrailerid{}\input{proof.tex}' >build/pass2.txt 2>&1
cp build/proof.pdf proof.pdf
pdftotext -layout proof.pdf proof.txt
printf '%s\n' 'Built proof.pdf and proof.txt from proof.tex. Inspect all rendered pages after edits.'
