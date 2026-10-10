#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export MATHLIB_NO_CACHE_ON_UPDATE=1
mapfile -t modules < <(python3 - <<'PY'
import json
from pathlib import Path
modules = json.loads(Path('MODULES.json').read_text())
imports = set()
for path in modules.values():
    for line in Path(path).read_text().splitlines():
        if line.startswith('import Mathlib.'):
            imports.add(line.split()[1])
print('\n'.join(sorted(imports)))
PY
)
lake exe cache get "${modules[@]}"
