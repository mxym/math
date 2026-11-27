#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
python3 verify_small.py
python3 verify_definition.py
