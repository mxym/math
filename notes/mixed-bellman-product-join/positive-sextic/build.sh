#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# Reproducible PDF metadata; no shell escape or network access is needed.
export SOURCE_DATE_EPOCH=1791331200
export FORCE_SOURCE_DATE=1
out="${1:-build}"
mkdir -p "$out"
# Respect a normal TeX installation. This fallback supports the minimal Debian
# installation used to prepare the note, where the default TEXMF tree is empty.
if ! kpsewhich article.cls >/dev/null 2>&1; then
  base=/usr/share/texlive/texmf-dist; extra=/usr/share/texmf
  cache="$PWD/$out/tex-cache"
  mkdir -p "$cache/config" "$cache/var"
  export TEXMF="{$base,$extra}"
  export TEXINPUTS=".:$base/tex//:$extra/tex//:"
  export TFMFONTS="$base/fonts/tfm//:$extra/fonts/tfm//:"
  export VFFONTS="$base/fonts/vf//:$extra/fonts/vf//:"
  export T1FONTS="$base/fonts/type1//:$extra/fonts/type1//:"
  export ENCFONTS="$base/fonts/enc//:$extra/fonts/enc//:"
  export TEXFORMATS="$cache:"
  export TEXFONTMAPS="$cache:$base/fonts/map//:$extra/fonts/map//:"
  export TEXMFVAR="$cache/var" TEXMFCONFIG="$cache/config"
  (cd "$cache"; pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex "$base/tex/latex/tex-ini-files/pdflatex.ini" >format-build.log 2>&1)
  cat "$extra/fonts/map/dvips/lm/lm.map" "$base/fonts/map/dvips/amsfonts/cm.map" "$base/fonts/map/dvips/amsfonts/symbols.map" "$base/fonts/map/dvips/amsfonts/euler.map" >"$cache/pdftex.map"
fi
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -output-directory="$out" paper.tex >"$out/first-pass.log" 2>&1
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -output-directory="$out" paper.tex >"$out/second-pass.log" 2>&1
cp "$out/paper.pdf" paper.pdf
printf 'Built paper.pdf from paper.tex.\n'
