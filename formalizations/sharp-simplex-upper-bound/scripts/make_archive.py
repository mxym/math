#!/usr/bin/env python3
"""Create a deterministic tar.gz from an already sealed, validated source tree.

Never creates or repairs a manifest. Output must be outside the source root.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import io
import os
import sys
import tarfile
import tempfile
sys.dont_write_bytecode = True
from release_integrity import ARCHIVE_PREFIX, ReleaseIntegrityError, require, validated_snapshot


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    temporary = None
    try:
        root = Path(__file__).resolve().parents[1]
        snapshot = validated_snapshot(root)
        require(not args.output.is_symlink(), 'archive output must not be a symlink')
        output = args.output.resolve()
        require(not output.is_relative_to(root), 'write archive outside the source tree')
        require(output.parent.is_dir(), 'archive output parent does not exist')
        require(not output.exists() or output.is_file(), 'archive output must be a regular file')
        with tempfile.NamedTemporaryFile(prefix='.' + output.name + '.', suffix='.tmp', dir=output.parent,
                                         delete=False) as stream:
            temporary = Path(stream.name)
            with gzip.GzipFile(filename='', mode='wb', fileobj=stream, mtime=0, compresslevel=9) as compressed:
                with tarfile.open(fileobj=compressed, mode='w|', format=tarfile.PAX_FORMAT) as archive:
                    for name, data in sorted(snapshot.items()):
                        info = tarfile.TarInfo(ARCHIVE_PREFIX + '/' + name)
                        info.size = len(data)
                        info.mode = 0o644
                        info.mtime = 0
                        info.uid = info.gid = 0
                        info.uname = info.gname = ''
                        archive.addfile(info, io.BytesIO(data))
            stream.flush()
            os.fsync(stream.fileno())
        digest = hashlib.sha256(temporary.read_bytes()).hexdigest()
        os.replace(temporary, output)
        temporary = None
        print(digest + '  ' + output.name)
        return 0
    except (ReleaseIntegrityError, OSError) as error:
        print(str(error) if isinstance(error, ReleaseIntegrityError) else 'RELEASE_INTEGRITY: archive failed: ' + str(error),
              file=sys.stderr)
        return 1
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


if __name__ == '__main__':
    sys.exit(main())
