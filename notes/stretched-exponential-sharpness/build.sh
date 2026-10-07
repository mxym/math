#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build stretched_exponential_sharpness.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build stretched_exponential_sharpness.tex
cp build/stretched_exponential_sharpness.pdf stretched_exponential_sharpness.pdf
