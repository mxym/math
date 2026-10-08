#!/usr/bin/env bash
# Existing system TeX only; no downloads and no vendored dependency tree.
set -euo pipefail
cd -- "$(dirname -- "$0")"
ROOT=$PWD
export SOURCE_DATE_EPOCH=1791417600 FORCE_SOURCE_DATE=1 TZ=UTC LC_ALL=C
if ! kpsewhich article.cls >/dev/null 2>&1 || ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  BASE=/usr/share/texlive/texmf-dist
  EXTRA=/usr/share/texmf
  CACHE=${TEX_CACHE_DIR:-${TMPDIR:-/tmp}/mxym-math-tex-cache}
  mkdir -p "$CACHE/config" "$CACHE/var"
  export TEXMF="{$BASE,$EXTRA}"
  export TEXINPUTS=".:$BASE/tex//:$EXTRA/tex//:"
  export TFMFONTS="$BASE/fonts/tfm//:$EXTRA/fonts/tfm//:"
  export VFFONTS="$BASE/fonts/vf//:$EXTRA/fonts/vf//:"
  export T1FONTS="$BASE/fonts/type1//:$EXTRA/fonts/type1//:"
  export ENCFONTS="$BASE/fonts/enc//:$EXTRA/fonts/enc//:"
  export TEXFORMATS="$CACHE:"
  export TEXFONTMAPS="$CACHE:$BASE/fonts/map//:$EXTRA/fonts/map//:"
  export TEXMFVAR="$CACHE/var" TEXMFCONFIG="$CACHE/config"
  if [ ! -f "$CACHE/pdflatex.fmt" ]; then
    (cd "$CACHE" && pdftex -ini -etex -interaction=nonstopmode -halt-on-error \
      -jobname=pdflatex "$BASE/tex/latex/tex-ini-files/pdflatex.ini" > format-build.stdout 2>&1)
  fi
  if [ ! -f "$CACHE/pdftex.map" ]; then
    cat "$EXTRA/fonts/map/dvips/lm/lm.map" \
      "$BASE/fonts/map/dvips/amsfonts/cm.map" \
      "$BASE/fonts/map/dvips/amsfonts/symbols.map" > "$CACHE/pdftex.map"
  fi
fi
for paper in "${@:-top-n binary-mass general-moment}"; do
  for item in $paper; do
    cd "$ROOT/$item"
    mkdir -p build
    for pass in 1 2 3; do
      pdflatex -no-shell-escape -halt-on-error -interaction=nonstopmode \
        -file-line-error -recorder -output-directory=build main.tex > "build/pass-$pass.txt"
    done
    cp build/main.pdf main.pdf
    if grep -Eq '(^!|LaTeX Warning: (Reference|Citation).*undefined|There were undefined references|Overfull \\hbox|Overfull \\vbox|Missing character:)' build/main.log; then
      grep -En '(^!|undefined|Overfull|Missing character:)' build/main.log >&2
      exit 1
    fi
    sha256sum main.pdf
  done
done
