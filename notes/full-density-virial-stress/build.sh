#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
export SOURCE_DATE_EPOCH=1791331200
export FORCE_SOURCE_DATE=1
export TZ=UTC
export LC_ALL=C
mkdir -p build
# Use system TeX normally. The fallback repairs missing filename databases or
# format caches in a read-only installation without changing any system file.
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
      -jobname=pdflatex "$BASE/tex/latex/tex-ini-files/pdflatex.ini" \
      > format-build.stdout 2>&1)
  fi
  cat "$EXTRA/fonts/map/dvips/lm/lm.map" \
      "$BASE/fonts/map/dvips/amsfonts/cm.map" \
      "$BASE/fonts/map/dvips/amsfonts/symbols.map" > "$CACHE/pdftex.map"
fi
for pass in 1 2 3; do
  pdflatex -no-shell-escape -halt-on-error -interaction=nonstopmode -file-line-error -recorder -output-directory=build manuscript.tex > "build/pass-${pass}.txt"
done
cp build/manuscript.pdf manuscript.pdf
{
  printf 'SOURCE_DATE_EPOCH=%s\nTZ=%s\nLC_ALL=%s\n' "$SOURCE_DATE_EPOCH" "$TZ" "$LC_ALL"
  pdflatex --version
  printf '\nOS and locale\n'
  uname -srm
  locale
} > build/toolchain.txt
python3 - <<'PY'
import hashlib,json,pathlib
files={}
for line in pathlib.Path('build/manuscript.fls').read_text().splitlines():
    if line.startswith('INPUT '):
        p=pathlib.Path(line[6:])
        if p.is_file() and p.resolve() != pathlib.Path('manuscript.tex').resolve() and not str(p.resolve()).startswith(str(pathlib.Path('build').resolve())+'/'):
            files[str(p.resolve())]=hashlib.sha256(p.read_bytes()).hexdigest()
pathlib.Path('build/tex-inputs.sha256.json').write_text(json.dumps(files,indent=2,sort_keys=True)+'\n')
PY
if grep -Eq '(^!|LaTeX Warning: (Reference|Citation).*undefined|There were undefined references|Overfull \\hbox|Overfull \\vbox)' build/manuscript.log; then
  grep -En '(^!|undefined|Overfull)' build/manuscript.log >&2
  exit 1
fi
sha256sum manuscript.pdf
