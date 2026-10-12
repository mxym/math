#!/bin/sh
# Regenerate the standalone LaTeX source and PDF without touching check reports.
set -eu
package_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
typeset_dir=${1:-"$package_dir/build/typeset"}
case "$typeset_dir" in
    /*) ;;
    *) typeset_dir="$package_dir/$typeset_dir" ;;
esac
mkdir -p "$typeset_dir"
export SOURCE_DATE_EPOCH=1791331200
export FORCE_SOURCE_DATE=1
pandoc "$package_dir/paper.md" \
    --from=markdown+tex_math_single_backslash \
    --to=latex --standalone \
    --variable=documentclass:article \
    --variable=fontsize:11pt \
    --variable=geometry:margin=25mm \
    --variable=lang:en \
    --variable=colorlinks:true \
    --variable=linkcolor:blue!35!black \
    --variable=urlcolor:blue!40!black \
    --include-in-header="$package_dir/header.tex" \
    --output="$typeset_dir/paper.tex"
(
    cd "$typeset_dir"
    pdflatex -interaction=nonstopmode -file-line-error -halt-on-error paper.tex > pass1.log
    pdflatex -interaction=nonstopmode -file-line-error -halt-on-error paper.tex > pass2.log
)
cp "$typeset_dir/paper.tex" "$package_dir/paper.tex"
cp "$typeset_dir/paper.pdf" "$package_dir/paper.pdf"
printf 'Built paper.tex and paper.pdf\n'
