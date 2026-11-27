#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 verify_constructive.py
python3 verify_independent.py
