#!/bin/sh
set -eu
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
cd "$here"
t=$(mktemp -d)
trap 'rm -rf -- "$t"' EXIT
export PYTHONDONTWRITEBYTECODE=1
python3 -O scope4.py
"${CXX:-c++}" -std=c++20 -O3 -Wall -Wextra -Werror phase4.cpp -o "$t/phase"
"$t/phase" > "$t/a"
cmp phase4.survivors "$t/a"
python3 -O cover4.py "$t/a"
"${CXX:-c++}" -std=c++20 -O3 -Wall -Wextra -Werror independent_phase.cpp -o "$t/phase2"
"$t/phase2" > "$t/b"
python3 - "$t/a" "$t/b" <<'PY'
from pathlib import Path
import sys
def read(p):
    return [tuple(map(int,l.split())) for l in Path(p).read_text().splitlines()]
a,b=map(read,sys.argv[1:])
if not (len(a)==len(b)==len(set(a))==225 and set(a)==set(b)):
    raise RuntimeError("survivor lists disagree")
print("All 225 individual survivor tuples agree.")
PY
python3 -O independent_cover.py "$t/b"
