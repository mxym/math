#!/usr/bin/env python3
"""Explicit maintainer initialization, never a repair or implicit resealing step.

Both seal records must be absent, and the final derivative ledger must already
be bound in release_integrity.py. Archive creation never calls this command.
"""
from pathlib import Path
import argparse
import sys
sys.dont_write_bytecode = True
from release_integrity import (ReleaseIntegrityError, checksum_bytes, manifest_bytes,
                               read_payload, require, sha256, validate_frozen_payload, validate_release)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--initialize', action='store_true', required=True,
                        help='Acknowledge one-time maintainer initialization of this versioned source tree')
    parser.parse_args()
    created = []
    try:
        root = Path(__file__).resolve().parents[1]
        for name in ('SOURCE_MANIFEST.json', 'SHA256SUMS'):
            require(not (root / name).exists() and not (root / name).is_symlink(),
                    'refusing to reseal an existing release: ' + name)
        snapshot = read_payload(root, sealed=False)
        validate_frozen_payload(snapshot)
        manifest = manifest_bytes(snapshot)
        hashes = {name: sha256(data) for name, data in snapshot.items()}
        hashes['SOURCE_MANIFEST.json'] = sha256(manifest)
        for name, data in [('SOURCE_MANIFEST.json', manifest), ('SHA256SUMS', checksum_bytes(hashes))]:
            with (root / name).open('xb') as stream:
                created.append(root / name)
                stream.write(data)
        validate_release(root)
        print('RELEASE_SEAL_INITIALIZED')
        return 0
    except (ReleaseIntegrityError, OSError) as error:
        # Roll back only files this invocation created, never an existing seal.
        for path in created:
            path.unlink(missing_ok=True)
        print(str(error) if isinstance(error, ReleaseIntegrityError) else 'RELEASE_INTEGRITY: seal failed: ' + str(error),
              file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
