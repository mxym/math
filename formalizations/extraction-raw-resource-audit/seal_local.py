#!/usr/bin/env python3
"""Archive a complete independently verified local run; never modifies frozen inputs."""
from pathlib import Path
import argparse,json,tarfile
import reproduce as a
from verify_local import verify


def main():
    ap=argparse.ArgumentParser();ap.add_argument('directory');args=ap.parse_args();out=Path(args.directory).resolve();result=verify(out)
    destination=out.parent/(out.name+'-full-evidence.tar.gz')
    if destination.exists():raise RuntimeError('Archive already exists; preserve it')
    files={path.relative_to(out).as_posix():a.sha(path)for path in sorted(out.rglob('*'))if path.is_file()}
    if any(path.is_symlink()for path in out.rglob('*')):raise RuntimeError('Symlinked local evidence')
    a.dump(out/'EVIDENCE_HASHES.json',files)
    with tarfile.open(destination,'x:gz')as archive:
        for path in sorted(out.rglob('*')):
            if path.is_file():archive.add(path,arcname=path.relative_to(out).as_posix(),recursive=False)
    with tarfile.open(destination,'r:gz')as archive:
        members=archive.getmembers();expected=files|{'EVIDENCE_HASHES.json':a.sha(out/'EVIDENCE_HASHES.json')}
        if len(members)!=len(expected)or {m.name for m in members}!=set(expected)or any(not m.isfile()for m in members):raise RuntimeError('Wrong archive membership')
        import hashlib
        for m in members:
            if hashlib.sha256(archive.extractfile(m).read()).hexdigest()!=expected[m.name]:raise RuntimeError('Archive readback byte mismatch')
    record=dict(result,archive=destination.name,archive_sha256=a.sha(destination),archive_bytes=destination.stat().st_size,archive_files=len(files)+1,evidence_manifest_sha256=a.sha(out/'EVIDENCE_HASHES.json'))
    a.dump(out.parent/(out.name+'-SEALED.json'),record);print(json.dumps(record,indent=2))

if __name__=='__main__':main()
