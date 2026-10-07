#!/bin/sh
# TeX Live build. No source writes, downloads, or copied format caches.
# Programs: pdflatex and kpsewhich; pdftex for the fresh-format fallback.
# LaTeX packages: fontenc, inputenc, lmodern, geometry, amsmath, amssymb,
# amsthm, mathtools, microtype, xurl, hyperref (and their dependencies).
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
export SOURCE_DATE_EPOCH=1791331200
export FORCE_SOURCE_DATE=1
export TZ=UTC
export LC_ALL=C
for program in pdflatex kpsewhich; do
    command -v "$program" >/dev/null 2>&1 || {
        printf '%s\n' "$program is required (TeX Live; see the full package list at the top of build.sh)." >&2
        exit 1
    }
done
mkdir -p build
# A read-only TeX installation may have missing filename databases or formats.
# Discover its trees through kpathsea and build a fresh, local format if needed.
if ! kpsewhich article.cls >/dev/null 2>&1 || ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
    BASE=$(kpsewhich -var-value=TEXMFDIST)
    EXTRA=$(kpsewhich -var-value=TEXMFDEBIAN)
    [ -d "$EXTRA" ] || EXTRA=$BASE
    [ -f "$BASE/tex/latex/tex-ini-files/pdflatex.ini" ] || {
        printf '%s\n' 'TeX Live sources are missing; install or repair the LaTeX distribution.' >&2
        exit 1
    }
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
        (cd "$CACHE" && pdftex -ini -etex -no-shell-escape -interaction=nonstopmode -halt-on-error \
          -jobname=pdflatex "$BASE/tex/latex/tex-ini-files/pdflatex.ini" >format-build.stdout.log 2>&1)
    fi
    LM_MAP=$(kpsewhich lm.map)
    CM_MAP=$(kpsewhich cm.map)
    SYMBOL_MAP=$(kpsewhich symbols.map)
    cat "$LM_MAP" "$CM_MAP" "$SYMBOL_MAP" > "$CACHE/pdftex.map"
fi
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -no-shell-escape \
      -output-directory=build proof.tex >"build/pass${pass}.stdout.log"
done
if grep -Eq '(^!|Missing character:|There were undefined references|LaTeX Warning: (Reference|Citation).*undefined|Overfull \\hbox|Overfull \\vbox)' build/proof.log; then
    grep -En '(^!|Missing character:|undefined|Overfull)' build/proof.log >&2
    exit 1
fi
cp build/proof.pdf proof.pdf
printf '%s\n' 'Built proof.pdf; compiler diagnostics are in build/proof.log.'
