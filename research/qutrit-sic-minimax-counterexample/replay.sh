#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
python3 -B verify_triples.py
python3 -B verify_effects.py
