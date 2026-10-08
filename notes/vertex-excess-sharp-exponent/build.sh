#!/bin/sh
set -eu
cd "$(dirname "$0")"
if [ "${VERTEX_TEX_CONFIGURED:-0}" != 1 ] && ! kpsewhich article.cls >/dev/null 2>&1; then
  export VERTEX_TEX_CONFIGURED=1
  exec ./configure_tex.sh ./build.sh
fi
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=build main.tex >build/pass1.stdout.log 2>&1
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=build main.tex >build/pass2.stdout.log 2>&1
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=build main.tex >build/pass3.stdout.log 2>&1
cp build/main.pdf vertex_excess_sharp_exponent.pdf
pdfinfo vertex_excess_sharp_exponent.pdf >build/pdfinfo.txt
pdftotext -layout vertex_excess_sharp_exponent.pdf build/pdf_text.txt
printf 'Built vertex_excess_sharp_exponent.pdf\n'
