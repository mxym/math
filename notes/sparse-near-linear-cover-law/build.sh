#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
task_output="${1:-/tmp/sparse-cover-law-paper}"
task_manuscript="${2:-paper.md}"
task_title='An asymptotic cover law for sparse nearly linear intersecting hypergraphs'
mkdir -p "$task_output"
task_output="$(cd "$task_output" && pwd)"
python3 - "$task_manuscript" "$task_output/body.md" <<'PY'
from pathlib import Path
import sys
lines = Path(sys.argv[1]).read_text().splitlines(keepends=True)
if not lines or not lines[0].startswith('# '):
    raise RuntimeError('expected manuscript title heading')
Path(sys.argv[2]).write_text(''.join(lines[1:]))
PY
pandoc "$task_output/body.md" -f markdown+tex_math_single_backslash -s \
  -o "$task_output/paper.tex" \
  --metadata title="$task_title" \
  -V geometry:margin=24mm -V fontsize=11pt
pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory="$task_output" "$task_output/paper.tex" > "$task_output/pass1.txt"
pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory="$task_output" "$task_output/paper.tex" > "$task_output/pass2.txt"
if rg 'Overfull|LaTeX Warning: (Reference .* undefined|There were undefined references)' "$task_output/paper.log"; then
  exit 1
fi
printf 'PDF: %s/paper.pdf\n' "$task_output"
