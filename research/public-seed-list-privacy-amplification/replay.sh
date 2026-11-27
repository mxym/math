#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
python3 -B verify_classical.py
python3 -B verify_quantum.py
