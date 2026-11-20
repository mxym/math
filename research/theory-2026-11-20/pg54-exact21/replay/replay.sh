#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
CXX="${CXX:-g++}"
for prog in generate census planes secants; do "$CXX" -O3 -std=c++17 "$prog.cpp" -o "$prog"; done
./generate
./census
for h in 9 10 11; do for n in 21 22; do
  ./planes "$h" "$n" <"pg4_$h.txt" >"plane_${h}_${n}.log"
  ./secants "$h" "$n" <"pg4_$h.txt" >"sec_${h}_${n}.log"
done; done
python3 verify.py
