#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd -- "$(dirname -- "$0")" && pwd)
export SOURCE_DATE_EPOCH=1791331200 FORCE_SOURCE_DATE=1 TZ=UTC LC_ALL=C
WORK=$(mktemp -d "${TMPDIR:-/tmp}/avoidance-covering-build.XXXXXX")
trap 'rm -rf "$WORK"' EXIT
# The fallback uses installed, standard TeX Live files without altering the
# system installation. It is useful for installations with missing databases.
if ! kpsewhich article.cls >/dev/null 2>&1 || ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  BASE=/usr/share/texlive/texmf-dist
  EXTRA=/usr/share/texmf
  test -f "$BASE/tex/latex/tex-ini-files/pdflatex.ini"
  CACHE="$WORK/tex-cache"
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
  (cd "$CACHE" && pdftex -ini -etex -interaction=nonstopmode -halt-on-error \
      -jobname=pdflatex "$BASE/tex/latex/tex-ini-files/pdflatex.ini" > format.stdout 2>&1)
  cat "$EXTRA/fonts/map/dvips/lm/lm.map" \
      "$BASE/fonts/map/dvips/amsfonts/cm.map" \
      "$BASE/fonts/map/dvips/amsfonts/symbols.map" > "$CACHE/pdftex.map"
fi
for NAME in bounded-cluster-avoidance critical-covering-gauge; do
  if [ "${1:-all}" != all ] && [ "${1:-all}" != "$NAME" ]; then continue; fi
  DIR="$HERE/../$NAME"
  mkdir -p "$WORK/$NAME"
  for PASS in 1 2 3; do
    (cd "$DIR" && pdflatex -no-shell-escape -halt-on-error -interaction=nonstopmode \
      -file-line-error -output-directory="$WORK/$NAME" paper.tex \
      > "$WORK/$NAME/pass-$PASS.txt") || {
        cat "$WORK/$NAME/pass-$PASS.txt" >&2; exit 1;
      }
  done
  if grep -Eq '(^!|LaTeX Warning: (Reference|Citation).*undefined|There were undefined references|Overfull \\hbox|Overfull \\vbox)' "$WORK/$NAME/paper.log"; then
    grep -En '(^!|undefined|Overfull)' "$WORK/$NAME/paper.log" >&2; exit 1
  fi
  cp "$WORK/$NAME/paper.pdf" "$DIR/paper.pdf"
  sha256sum "$DIR/paper.pdf"
done
