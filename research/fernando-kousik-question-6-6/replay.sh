#!/bin/sh
set -eu
cd "$(dirname "$0")"
bin=$(mktemp)
trap 'rm -f "$bin"' EXIT HUP INT TERM
"${CXX:-c++}" -std=c++17 -O2 verify.cpp -o "$bin"
"$bin"
