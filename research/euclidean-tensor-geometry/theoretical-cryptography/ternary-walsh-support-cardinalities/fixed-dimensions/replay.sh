#!/bin/sh
set -eu
cd "$(dirname "$0")"
node generate.js 2>&1
python3 verify_fixed.py
