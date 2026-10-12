#!/bin/sh
set -eu
BASE=/usr/share/texlive/texmf-dist
EXTRA=/usr/share/texmf
CACHE="$PWD/tex-cache"
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
(cd "$CACHE" && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex "$BASE/tex/latex/tex-ini-files/pdflatex.ini" >format-build.txt 2>&1)
cat "$EXTRA/fonts/map/dvips/lm/lm.map" "$BASE/fonts/map/dvips/amsfonts/cm.map" "$BASE/fonts/map/dvips/amsfonts/symbols.map" "$BASE/fonts/map/dvips/amsfonts/euler.map" >"$CACHE/pdftex.map"
exec "$@"
