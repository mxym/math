"""Read SHA-pinned historical inputs, even after parallel ancestors evolve."""
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

ROOT=Path(__file__).resolve().parents[1]


class HistoricalInputs:
    def __init__(self):
        self.pins=json.loads((ROOT/'manuscripts/SOURCE_PINS.json').read_text())
        self.commit=self.pins['commit']
        if not re.fullmatch(r'[0-9a-f]{40}',self.commit):
            raise RuntimeError('Historical snapshot must be a full commit hash')
        self.restored={}

    def read_bytes(self,path):
        digest=self.pins['files'][path]
        if path in self.restored:return self.restored[path]
        relative=PurePosixPath(path)
        if relative.is_absolute() or '..' in relative.parts:
            raise RuntimeError('Unsafe historical source path')
        local=ROOT/path
        data=local.read_bytes() if local.is_file() and not local.is_symlink() else None
        if data is not None and sha256(data).hexdigest()==digest:return data
        # This is a read of the exact disclosed commit, never a reseal or an
        # acceptance of changed current files. A zip without Git must contain
        # the original inputs or the reader must obtain the pinned checkout.
        p=subprocess.run(['git','show',self.commit+':'+path],cwd=ROOT,capture_output=True)
        if p.returncode or sha256(p.stdout).hexdigest()!=digest:
            raise RuntimeError('Cannot obtain SHA-pinned source '+path+
                               '; use the recorded integration checkout')
        self.restored[path]=p.stdout
        return p.stdout

    def verify_all(self):
        for path in self.pins['files']:self.read_bytes(path)
