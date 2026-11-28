#!/bin/sh
set -eu
python3 verify.py
sha256sum -c SHA256SUMS
