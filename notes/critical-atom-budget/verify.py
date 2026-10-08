#!/usr/bin/env python3
"""Frozen-artifact and optional PDF-build checks; not a mathematical proof verifier."""
from pathlib import Path,PurePosixPath
import argparse,difflib,hashlib,json,os,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
def require(v,s):
    if not v: raise RuntimeError(s)
def sha(b): return hashlib.sha256(b).hexdigest()
def command(argv,**kwargs):
    r=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,**kwargs)
    require(r.returncode==0,'Command failed: '+str(argv[0])+'\n'+r.stdout.decode(errors='replace')[-2000:])
    return r.stdout
def unique(pairs):
    out={}
    for k,v in pairs:
        require(k not in out,'Duplicate JSON key');out[k]=v
    return out
ANCHORS={'PROOF.md': '88d9971c062414b1637806b0b61248585f1132c6082783df227266fe7122996e', 'paper.tex': '208d9643aec88d143c26028fb616144c7cc5cd2e0c3822265b413ddee0c4d030', 'paper.pdf': 'd117df45635753ce0ad88d82dbff2854803f2c558adaaf82e06bdf7cfb28dbfc', 'review/PARENT_INDEPENDENT_REVIEW.md': 'f0a135768a3efd6d86772dd689636f7fa264fda8168b1239b99538dd5e959d1c', 'review/FINAL_COPY_REVIEW.json': 'a94c88cd8a1d97c1717eabd6edb8fe355bd564fd9c5d9a889cb6a91b72e0cd5a', 'history/paper-v1.tex': 'fb526952185098b61c90f89bc4f5b4e47a0f4300ae9008949fdabfafeeb9395b', 'history/paper-v1-to-final.diff': 'aab833916f148174989c9c29588b539990614a809e49cb8d76fb1f5114008321'}
def integrity():
    doc=json.loads((ROOT/'MANIFEST.json').read_text(),object_pairs_hook=unique)
    require(doc['format']=='critical-atom-budget-manifest-v1','Manifest format')
    expected=doc['files'];actual={}
    for p in ROOT.rglob('*'):
        require(not p.is_symlink(),'Symlink in package')
        if p.is_file() and p.relative_to(ROOT).as_posix() not in ('MANIFEST.json','SHA256SUMS'):
            actual[p.relative_to(ROOT).as_posix()]={'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}
    require(actual==expected,'Payload inventory or hash mismatch')
    for name,digest in ANCHORS.items():require(sha((ROOT/name).read_bytes())==digest,'Frozen reviewed input differs: '+name)
    hashes={n:r['sha256'] for n,r in actual.items()};hashes['MANIFEST.json']=sha((ROOT/'MANIFEST.json').read_bytes())
    want=''.join(hashes[n]+'  '+n+'\n' for n in sorted(hashes))
    require((ROOT/'SHA256SUMS').read_text()==want,'Checksum index differs')
    a=(ROOT/'history/paper-v1.tex').read_text();b=(ROOT/'paper.tex').read_text()
    diff=''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='paper-v1.tex',tofile='paper.tex'))
    require(diff==(ROOT/'history/paper-v1-to-final.diff').read_text(),'Exact TeX correction differs')
    require('\\author{}' in b,'Blank author field changed')
    return {'status':'PASS','payload_files':len(actual)+2,'reviewed_inputs_byte_identical':len(ANCHORS),'exact_typographic_diff':True,'blank_author_preserved':True}
def check_pdf_build(output):
    if output:
        output = output.resolve()
        require(output != ROOT and ROOT not in output.parents, 'Build output must be outside frozen package')
        require(not output.exists(), 'Build output already exists; choose a new directory')
    with tempfile.TemporaryDirectory(prefix='manuscript-pdf-') as temp:
        build = Path(temp)
        for name in ['paper.tex']:
            shutil.copyfile(ROOT/name, build/name)
        environment = os.environ.copy()
        environment.update(TEXMFVAR=str(build/'tex-cache'), TEXMFCONFIG=str(build/'tex-config'),
                           VARTEXFONTS=str(build/'tex-fonts'))
        environment['TEXFORMATS'] = str(build) + os.pathsep + environment.get('TEXFORMATS', '')
        require(shutil.which('kpsewhich') is not None, 'TeX kpsewhich is missing')
        def located(name):
            probe = subprocess.run(['kpsewhich', name], env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            return probe.returncode == 0 and bool(probe.stdout.strip())
        format_bootstrap = not all(located(name) for name in ['pdflatex.fmt', 'article.cls', 'pdftex.map'])
        if format_bootstrap:
            # Some minimal Debian TeX installations have the standard package
            # files but neither a format nor an ls-R index. Read those installed
            # files directly; never download packages or write system caches.
            base, extra = Path('/usr/share/texlive/texmf-dist'), Path('/usr/share/texmf')
            ini = base/'tex/latex/tex-ini-files/pdflatex.ini'
            require(ini.is_file(), 'A usable standard pdfLaTeX installation is required')
            cache = build/'tex-cache'
            cache.mkdir()
            (cache/'language.dat').write_text('english hyphen.tex\n')
            environment.update(TEXMF='{'+str(base)+','+str(extra)+'}',
                TEXINPUTS='.'+os.pathsep+str(cache)+os.pathsep+str(base)+'/tex//'+os.pathsep+str(extra)+'/tex//'+os.pathsep,
                TEXFORMATS=str(cache)+os.pathsep, TEXFONTMAPS=str(cache)+os.pathsep+str(base)+'/fonts/map//'+os.pathsep+str(extra)+'/fonts/map//'+os.pathsep)
            for variable, directory in [('TFMFONTS','tfm'),('VFFONTS','vf'),('T1FONTS','type1'),('ENCFONTS','enc')]:
                environment[variable] = str(base)+'/fonts/'+directory+'//'+os.pathsep+str(extra)+'/fonts/'+directory+'//'+os.pathsep
            maps = [extra/'fonts/map/dvips/lm/lm.map', base/'fonts/map/dvips/amsfonts/cm.map',
                    base/'fonts/map/dvips/amsfonts/symbols.map', base/'fonts/map/dvips/amsfonts/euler.map']
            require(all(path.is_file() for path in maps), 'Standard TeX font maps are missing')
            (cache/'pdftex.map').write_bytes(b'\n'.join(path.read_bytes() for path in maps))
            format_log = command(['pdftex', '-ini', '-etex', '-no-shell-escape', '-interaction=nonstopmode',
                                  '-halt-on-error', '-jobname=pdflatex', str(ini)], cwd=cache, env=environment)
            (cache/'format-bootstrap.txt').write_bytes(format_log)
            require((cache/'pdflatex.fmt').is_file(), 'Isolated TeX format generation failed')
        for turn in range(1, 4):
            log = command(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error',
                           'paper.tex'], cwd=build, env=environment)
            (build/f'pass-{turn}.txt').write_bytes(log)
        log = (build/'paper.log').read_text()
        for marker in ['undefined references', 'undefined on input', 'multiply defined', 'Overfull', 'Missing character']:
            require(marker not in log, 'Final TeX problem: ' + marker)
        supplied_text = command(['pdftotext', '-layout', str(ROOT/'paper.pdf'), '-'])
        rebuilt_text = command(['pdftotext', '-layout', str(build/'paper.pdf'), '-'])
        require(supplied_text == rebuilt_text, 'Rebuilt PDF text differs from frozen PDF:\n' + ''.join(difflib.unified_diff(supplied_text.decode().splitlines(keepends=True), rebuilt_text.decode().splitlines(keepends=True), fromfile='frozen-pdf', tofile='rebuilt-pdf'))[:4000])
        require(rebuilt_text.count(b'\f') == 7 and b'??' not in rebuilt_text, 'PDF page/reference check failed')
        result = {'status': 'PASS', 'pages': 7, 'text_equal_to_frozen_pdf': True,
                  'text_sha256': sha(rebuilt_text), 'shell_escape': False,
                  'isolated_format_bootstrap': format_bootstrap,
                  'fallback_hyphenation': 'english hyphen.tex' if format_bootstrap else None,
                  'pdf_byte_identity_required': False,
                  'reason': 'PDF timestamps/engine metadata may differ; frozen delivery PDF stays unchanged.'}
        if output:
            shutil.copytree(build, output)
    return result


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--build-output',type=Path);a=ap.parse_args()
    result={'status':'PASS','python_optimized':not __debug__,'integrity':integrity(),'mathematical_proof_reaudited':False,'lean_verified':False}
    if a.build_output:result['pdf_reproduction']=check_pdf_build(a.build_output)
    else:result['pdf_reproduction']={'status':'NOT_RUN'}
    integrity()
    print(json.dumps(result,indent=2))
if __name__=='__main__':
    try:main()
    except (RuntimeError,OSError,ValueError,KeyError) as e:
        print(json.dumps({'status':'FAIL','error':str(e)},indent=2),file=sys.stderr);sys.exit(1)
