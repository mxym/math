#!/usr/bin/env python3
"""Verify the frozen package without executing Lean or downloading dependencies."""
from pathlib import Path
import argparse
import sys
sys.dont_write_bytecode = True
from release_integrity import ReleaseIntegrityError, validate_release


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    try:
        files = validate_release(Path(__file__).resolve().parents[1])
    except ReleaseIntegrityError as error:
        print(str(error), file=sys.stderr)
        return 1
    print('RELEASE_INTEGRITY_PASS ' + str(len(files)) + ' frozen files')
    return 0


if __name__ == '__main__':
    sys.exit(main())
