#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
python3 -B verify_coefficients.py
python3 -B verify_construction.py
