#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
node proof/verify-fuglede-f17-size34-decic-witness-nonlift.js
node proof/verify-fuglede-f17-size34-final-incidence.js
"${CXX:-g++}" -O3 -std=c++17 proof/verify-fuglede-f17-size34-cap-four-profiles.cpp -o "$tmp/cap"
"$tmp/cap"
if [[ "${1:-}" == quick ]]; then exit; fi
"${CXX:-g++}" -O3 -std=c++17 proof/verify-fuglede-f17-size34-six-directions-decic.cpp -o "$tmp/decic"
: > "$tmp/ranges"
for ((lo=0; lo<833; lo+=105)); do
  hi=$((lo+105))
  if ((hi>833)); then hi=833; fi
  "$tmp/decic" 1 "$lo" "$hi" > "$tmp/$lo"
  grep ' unexcluded 0$' "$tmp/$lo" | sed 's/ unexcluded 0$//' >> "$tmp/ranges"
done
grep '^scale 1 range ' proof/verify-fuglede-f17-size34-six-directions-decic-transcript.txt | head -n 8 > "$tmp/expected"
diff -u "$tmp/expected" "$tmp/ranges"
printf '%s\n' 'Degree-ten census matched all 833 prefixes, with zero spatial candidates.'
