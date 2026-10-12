#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build/typeset
export SOURCE_DATE_EPOCH=1791331200
export FORCE_SOURCE_DATE=1
export TZ=UTC
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
      "$BASE/fonts/map/dvips/amsfonts/euler.map" \
      "$BASE/fonts/map/dvips/rsfs/rsfs.map" >"$CACHE/pdftex.map"
fi
pandoc paper.md --from=markdown+tex_math_single_backslash --to=latex --standalone --variable=documentclass:article --variable=fontsize:11pt --variable=geometry:margin=24mm --variable=lang:en --variable=colorlinks:true --include-in-header=header.tex --output=build/typeset/paper.tex
python3 typeset_prepare.py build/typeset/paper.tex > build/typeset/format-fixes.txt
cp build/typeset/paper.tex paper.tex
(cd build/typeset
 pdflatex -interaction=nonstopmode -file-line-error -halt-on-error paper.tex > pass1.log
 pdflatex -interaction=nonstopmode -file-line-error -halt-on-error paper.tex > pass2.log
)
cp build/typeset/paper.pdf paper.pdf
pdftotext -layout paper.pdf paper.txt
printf 'Built complete proof PDF and text.\n'
