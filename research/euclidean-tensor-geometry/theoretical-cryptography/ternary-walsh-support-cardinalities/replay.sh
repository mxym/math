#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
t="$(mktemp -d)"
trap 'rm -rf -- "$t"' EXIT
c++ -std=c++20 -O3 geometry.cpp -o "$t/geometry"
c++ -std=c++20 -O3 exhaustive3.cpp -o "$t/exhaustive3"
python3 -B verify.py
"$t/geometry"
"$t/exhaustive3"
