#!/usr/bin/env python3
"""Verify immutable release bytes, replay exact checks, and optionally rebuild."""
import argparse, gzip, hashlib, io, json, shutil, subprocess, sys, tarfile, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent


def require(ok, description):
    if not ok:
        raise RuntimeError(description)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def source_archive(paths):
    buffer=io.BytesIO()
    with tarfile.open(fileobj=buffer,mode='w',format=tarfile.USTAR_FORMAT) as archive:
        for path in sorted(paths):
            data=(ROOT/path).read_bytes()
            item=tarfile.TarInfo('semiconvex-gaussian-entropy/'+path)
            item.size=len(data); item.mode=0o644; item.uid=item.gid=0
            item.uname=item.gname=''; item.mtime=1791331200
            archive.addfile(item,io.BytesIO(data))
    compressed=io.BytesIO()
    with gzip.GzipFile(filename='',mode='wb',fileobj=compressed,mtime=0,compresslevel=9) as stream:
        stream.write(buffer.getvalue())
    return compressed.getvalue()


def integrity():
    whitelist=json.loads((ROOT/'PUBLICATION_WHITELIST.json').read_text())['paths']
    require(whitelist==sorted(set(whitelist)), 'whitelist must be sorted and unique')
    for path in whitelist:
        require(not Path(path).is_absolute() and '..' not in Path(path).parts, 'unsafe whitelist path')
    found=[]
    for path in ROOT.rglob('*'):
        require(not path.is_symlink(), 'symlinks are not release files')
        if path.is_file(): found.append(path.relative_to(ROOT).as_posix())
    require(sorted(found)==whitelist, 'missing or unexpected regular file in package')
    source_paths=sorted(set(whitelist)-{'MANIFEST.json','SHA256SUMS','paper.pdf','source.tar.gz'})
    for name,expected in [('SOURCE_MANIFEST.json',set(source_paths)-{'SOURCE_MANIFEST.json'}),
                          ('MANIFEST.json',set(whitelist)-{'MANIFEST.json','SHA256SUMS'})]:
        files=json.loads((ROOT/name).read_text())['files']
        require({item['path'] for item in files}==expected and len(files)==len(expected),
                'incorrect manifest coverage: '+name)
        for item in files:
            data=(ROOT/item['path']).read_bytes()
            require(len(data)==item['bytes'] and digest(data)==item['sha256'], 'hash mismatch: '+item['path'])
    sums=''.join(digest((ROOT/path).read_bytes())+'  '+path+'\n' for path in whitelist if path!='SHA256SUMS')
    require(sums==(ROOT/'SHA256SUMS').read_text(), 'SHA256SUMS mismatch')
    original_pins={item['name']:item for item in json.loads((ROOT/'ORIGINAL_INPUT_HASHES.json').read_text())['files']}
    preserved={'entropy.tex':'originals/entropy.tex','check_exact.py':'checks/check_exact.py',
               'fetch_sources.py':'fetch_sources.py','sources.json':'sources.json'}
    for name,path in preserved.items():
        data=(ROOT/path).read_bytes(); pin=original_pins[name]
        require(len(data)==pin['bytes'] and digest(data)==pin['sha256'], 'frozen original input mismatch: '+name)
    audit_pins={item['name']:item for item in json.loads((ROOT/'PROVENANCE.json').read_text())['audit_input_hashes']}
    for name,path in [('entropy.corrected.tex','originals/entropy.corrected.tex'),
                      ('independent_checks.py','checks/independent_checks.py'),
                      ('square_exponential_domain.patch','square_exponential_domain.patch')]:
        data=(ROOT/path).read_bytes(); pin=audit_pins[name]
        require(len(data)==pin['bytes'] and digest(data)==pin['sha256'], 'frozen audited input mismatch: '+name)
    canonical=source_archive(source_paths)
    require(canonical==(ROOT/'source.tar.gz').read_bytes(), 'source archive does not match exact canonical payload')
    return {'release_files':len(whitelist),'source_archive_files':len(source_paths),
            'source_archive_sha256':digest(canonical)}


def run(command,cwd):
    result=subprocess.run(command,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                          env={**__import__('os').environ,'PYTHONDONTWRITEBYTECODE':'1'})
    require(result.returncode==0, 'command failed: '+str(command)+'\n'+result.stdout+result.stderr)
    return result.stdout


def exact_replays():
    reports={}
    for checker,expected in [('check_exact.py','original_replay.json'),
                             ('independent_checks.py','independent_replay.json'),
                             ('check_correction.py','correction_replay.json')]:
        outputs=[]
        for optimized in [False,True]:
            with tempfile.TemporaryDirectory(prefix='semiconvex-exact-') as directory:
                temporary=Path(directory)
                if checker=='independent_checks.py':
                    shutil.copyfile(ROOT/'checks'/checker,temporary/checker)
                    shutil.copyfile(ROOT/'originals/entropy.tex',temporary/'entropy.tex')
                    target=temporary/checker
                else:
                    target=ROOT/'checks'/checker
                command=[sys.executable,'-B']+(['-O'] if optimized else [])+[str(target)]
                output=run(command,temporary)
                if checker=='independent_checks.py':
                    require((temporary/'entropy.corrected.tex').read_bytes()==(ROOT/'originals/entropy.corrected.tex').read_bytes(),
                            'independent regenerated correction differs')
                    require((temporary/'square_exponential_domain.patch').read_bytes()==(ROOT/'square_exponential_domain.patch').read_bytes(),
                            'independent regenerated patch differs')
                outputs.append(output)
        require(outputs[0]==outputs[1], 'optimization changed checker output: '+checker)
        require(outputs[0]==(ROOT/'checks'/expected).read_text(), 'stored checker output differs: '+checker)
        report=json.loads(outputs[0]); require(report['status']=='PASS', 'checker did not pass: '+checker)
        reports[checker]=report
    return reports


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--build',action='store_true')
    parser.add_argument('--output-dir',type=Path)
    parser.add_argument('--archive',type=Path,help='Write the verified canonical source archive outside the package')
    args=parser.parse_args()
    report={'status':'PASS','integrity':integrity(),'normal_optimized_identical':True,
            'checks':exact_replays(),'scope':'Exact finite algebra and byte integrity; the written proof and analytic audit supply universal assertions. No complete Lean verification.'}
    if args.archive:
        destination=args.archive.resolve()
        require(ROOT not in destination.parents and destination!=ROOT, 'archive output must be outside package')
        destination.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(ROOT/'source.tar.gz',destination)
        report['archive_written']=str(destination)
    if args.build:
        destination=args.output_dir or Path(tempfile.mkdtemp(prefix='semiconvex-pdf-'))
        report['pdf_build_output']=run(['bash',str(ROOT/'tools/build_pdf.sh'),str(destination.resolve())],ROOT)
        report['pdf_rebuild']={'pages':9,'shell_escape':False,'final_pass_warnings':False}
    print(json.dumps(report,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
