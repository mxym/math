#!/usr/bin/env bash
# Compile this manuscript only. Never installs packages or downloads TeX.
set -euo pipefail
cd -- "$(dirname -- "$0")"
export SOURCE_DATE_EPOCH=1791417600 FORCE_SOURCE_DATE=1 TZ=UTC LC_ALL=C
if ! kpsewhich article.cls >/dev/null 2>&1 || ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  BASE=/usr/share/texlive/texmf-dist
  EXTRA=/usr/share/texmf
  CACHE=${TEX_CACHE_DIR:-../kinetic13_manuscript_independent_audit_20261007/tex-cache}
  CACHE=$(cd "$CACHE" && pwd)
  if [ ! -f "$CACHE/pdflatex.fmt" ] || [ ! -f "$CACHE/pdftex.map" ]; then
    echo 'Provide TEX_CACHE_DIR containing an existing pdflatex.fmt and pdftex.map, or use a configured TeX installation.' >&2
    exit 2
  fi
  export TEXMF="{$BASE,$EXTRA}"
  export TEXINPUTS=".:$BASE/tex//:$EXTRA/tex//:"
  export TFMFONTS="$BASE/fonts/tfm//:$EXTRA/fonts/tfm//:"
  export VFFONTS="$BASE/fonts/vf//:$EXTRA/fonts/vf//:"
  export T1FONTS="$BASE/fonts/type1//:$EXTRA/fonts/type1//:"
  export ENCFONTS="$BASE/fonts/enc//:$EXTRA/fonts/enc//:"
  export TEXFORMATS="$CACHE:"
  export TEXFONTMAPS="$CACHE:$BASE/fonts/map//:$EXTRA/fonts/map//:"
  export TEXMFVAR="$PWD/build/tex-var" TEXMFCONFIG="$PWD/build/tex-config"
fi
mkdir -p build
for pass in 1 2 3; do
  pdflatex -no-shell-escape -halt-on-error -interaction=nonstopmode \
    -file-line-error -recorder -output-directory=build main.tex > "build/pass-$pass.txt"
done
if grep -Eq '(^!|LaTeX Warning: (Reference|Citation).*undefined|There were undefined references|Overfull \\hbox|Overfull \\vbox|Missing character:)' build/main.log; then
  grep -En '(^!|undefined|Overfull|Missing character:)' build/main.log >&2
  exit 1
fi
cp build/main.pdf main.pdf
sha256sum main.pdf
