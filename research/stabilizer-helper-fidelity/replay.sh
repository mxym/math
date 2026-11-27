#!/bin/sh
set -eu
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
python3 verify_exact.py
python3 verify_independent.py
