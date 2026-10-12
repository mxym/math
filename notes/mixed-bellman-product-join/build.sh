#!/usr/bin/env bash
set -euo pipefail

task_publication_dir="$(cd "$(dirname "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
  echo "pdflatex is required; see README.md for the TeX packages." >&2
  exit 1
fi
mkdir -p "$task_publication_dir/build"
cd "$task_publication_dir"
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build paper.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build paper.tex
cp build/paper.pdf paper.pdf
echo "Built paper.pdf from paper.tex."
