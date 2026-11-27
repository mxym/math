#!/bin/sh
set -eu
if [ "$#" -gt 0 ]; then
    case "$1" in
        /*) catalog="$1";;
        *) catalog="$PWD/$1";;
    esac
    cd "$(dirname "$0")"
    exec python3 verify_phi.py --catalog7 "$catalog"
fi
cd "$(dirname "$0")"
exec python3 verify_phi.py
