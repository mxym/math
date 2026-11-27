#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
d="$(mktemp -d)"
trap 'rm -rf -- "$d"' EXIT
c++ -O3 -Wall -Wextra -std=c++20 verify.cpp -o "$d/verify"
"$d/verify"
