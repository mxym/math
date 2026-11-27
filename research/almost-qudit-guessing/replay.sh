#!/bin/sh
set -eu
OPENBLAS_NUM_THREADS=1 python3 verify_exact.py
OPENBLAS_NUM_THREADS=1 python3 verify_independent.py
