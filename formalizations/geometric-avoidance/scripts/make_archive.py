#!/usr/bin/env python3
"""Make a deterministic source-only tar.gz from a verified frozen project."""
from pathlib import Path
import argparse,gzip,hashlib,io,json,tarfile,sys
sys.dont_write_bytecode = True
from release_integrity import validate_release
R=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser(description=__doc__);p.add_argument('output',type=Path);a=p.parse_args()
files=validate_release(R)
if a.output.resolve().is_relative_to(R):raise RuntimeError('write archive outside source project')
with a.output.open('wb') as f,gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0,compresslevel=9) as z,tarfile.open(fileobj=z,mode='w|',format=tarfile.PAX_FORMAT) as t:
 for n in files:
  data=(R/n).read_bytes();info=tarfile.TarInfo('geometric-avoidance/'+n);info.size=len(data);info.mode=0o644;info.mtime=0;info.uid=info.gid=0;info.uname=info.gname='';t.addfile(info,io.BytesIO(data))
print(hashlib.sha256(a.output.read_bytes()).hexdigest()+'  '+a.output.name)
