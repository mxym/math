#!/bin/sh
set -eu
cd "$(dirname "$0")"
if ! kpsewhich article.cls >/dev/null 2>&1 || ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  BASE=/usr/share/texlive/texmf-dist
  EXTRA=/usr/share/texmf
  test -f "$BASE/tex/latex/tex-ini-files/pdflatex.ini"
  CACHE_ROOT=$(printenv TMPDIR || true)
  test -n "$CACHE_ROOT" || CACHE_ROOT=/tmp
  CACHE="$CACHE_ROOT/math-kinetic-tex-$(id -u)"
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
       -jobname=pdflatex "$BASE/tex/latex/tex-ini-files/pdflatex.ini" \
       > format-build.stdout 2>&1)
  fi
  cat "$EXTRA/fonts/map/dvips/lm/lm.map" \
      "$BASE/fonts/map/dvips/amsfonts/cm.map" \
      "$BASE/fonts/map/dvips/amsfonts/symbols.map" > "$CACHE/pdftex.map"
fi
latexmk -g -pdf -interaction=nonstopmode -halt-on-error manuscript.tex
