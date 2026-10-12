#!/usr/bin/env python3
"""Replay release archive/patch in clean directories, normal and -O, with exact PDF rebuild."""
from __future__ import annotations
import argparse,hashlib,json,subprocess,sys,tarfile,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
PREFIX='notes/conserved-quadratic-fluctuations'

def require(ok,message):
    if not ok: raise RuntimeError(message)

def execute(command,cwd):
    r=subprocess.run(command,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    require(r.returncode==0,'Replay failed: '+' '.join(command)+'\n'+r.stdout+'\n'+r.stderr)
    return r.stdout

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--archive',type=Path,required=True);p.add_argument('--patch',type=Path,required=True);p.add_argument('--output',type=Path);a=p.parse_args();expected=hashlib.sha256((ROOT/'manuscript.pdf').read_bytes()).hexdigest();allowed=set(json.loads((ROOT/'PUBLIC_FILES.json').read_text())['files'])|{'package-manifest.json'};checks=[]
    with tempfile.TemporaryDirectory(prefix='quadratic-replay-') as directory:
        base=Path(directory);arc=base/'archive';arc.mkdir()
        with tarfile.open(a.archive,'r:gz') as archive:
            members=archive.getmembers();names=[m.name for m in members]
            require(len(names)==len(set(names)),'Duplicate archive entry.')
            require(set(names)=={PREFIX+'/'+name for name in allowed},'Archive differs from fixed publication whitelist.')
            for m in members:
                require(m.isfile() and not m.issym() and not m.islnk(),'Nonregular archive entry.')
                require(not Path(m.name).is_absolute() and '..' not in Path(m.name).parts,'Unsafe archive entry.')
                require(m.mtime==1791331200 and m.mode==0o644 and m.uid==0 and m.gid==0 and m.uname=='' and m.gname=='','Noncanonical archive metadata.')
                target=arc/m.name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(archive.extractfile(m).read())
        patchdir=base/'patch';patchdir.mkdir();patch=a.patch.resolve();headers=[line[6:] for line in patch.read_text().splitlines() if line.startswith('+++ b/')]
        text_allowed={PREFIX+'/'+name for name in allowed if name!='manuscript.pdf'}
        require(len(headers)==len(set(headers)) and set(headers)==text_allowed,'Patch differs from complete public text whitelist.')
        execute(['git','apply','--whitespace=nowarn',str(patch)],patchdir)
        for route,where in [('archive',arc/PREFIX),('patch',patchdir/PREFIX)]:
            # Patch contains no binary PDF; reconstruct it before exact-inventory verification.
            if route=='patch': execute([sys.executable,'build.py','--verify-repeat'],where)
            for optimized in [False,True]:
                mode=['-O'] if optimized else []
                for checker in ['checks/verify_package.py','checks/strict_check.py']:
                    execute([sys.executable,*mode,checker],where);checks.append({'route':route,'checker':checker,'optimized':optimized,'passed':True})
            execute([sys.executable,'build.py','--verify-repeat'],where)
            digest=hashlib.sha256((where/'manuscript.pdf').read_bytes()).hexdigest();require(digest==expected,'PDF rebuilt with different bytes.')
            execute([sys.executable,'checks/verify_package.py'],where)
            checks.append({'route':route,'fresh_double_build':True,'pdf_sha256':digest,'all_packaged_generated_bytes_unchanged':True})
        for name in allowed:
            if name=='manuscript.pdf': continue
            require((arc/PREFIX/name).read_bytes()==(patchdir/PREFIX/name).read_bytes(),'Archive/patch text mismatch: '+name)
    result={'archive_sha256':hashlib.sha256(a.archive.read_bytes()).hexdigest(),'patch_sha256':hashlib.sha256(a.patch.read_bytes()).hexdigest(),'pdf_sha256':expected,'complete_text_replay_identical':True,'checks':checks}
    if a.output: a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__': main()
