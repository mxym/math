#!/bin/sh
set -eu
cd "$(dirname "$0")"
if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex
else
  pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
  bibtex manuscript
  pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
  pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
fi
