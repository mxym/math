#!/usr/bin/env python3
"""Package the declared supplement sources deterministically; never alter dependency pins."""
import gzip,hashlib,io,pathlib,tarfile
p=pathlib.Path(__file__).resolve().parent
names=['manuscript.tex','build.sh','README.md','DEPENDENCIES.md','dependency-inventory.json','verify_dependencies.py','MATHEMATICAL_AUDIT.md','AUDIT_PROVENANCE.json','EDITORIAL_CHANGES.md','BUILD_ENVIRONMENT.md','ARTIFACT_QA.md','package_source.py']
for n in names:
    if not(p/n).is_file():raise SystemExit('Missing source artifact: '+n)
(p/'SOURCE_SHA256SUMS').write_text(''.join(hashlib.sha256((p/n).read_bytes()).hexdigest()+'  '+n+'\n' for n in sorted(names)))
with(p/'source.tar.gz').open('wb')as raw:
    with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=1791331200,compresslevel=9)as out:
        with tarfile.open(fileobj=out,mode='w',format=tarfile.USTAR_FORMAT)as tar:
            for n in sorted(names+['SOURCE_SHA256SUMS']):
                d=(p/n).read_bytes();i=tarfile.TarInfo('full-density-virial-stress/'+n)
                i.size=len(d);i.mtime=1791331200;i.uid=i.gid=0;i.uname=i.gname='';i.mode=0o755 if n.endswith(('.sh','.py'))else 0o644
                tar.addfile(i,io.BytesIO(d))
print(hashlib.sha256((p/'source.tar.gz').read_bytes()).hexdigest()+'  source.tar.gz')
