#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
python3 -B verify_moments.py
python3 -B verify_maps.py
