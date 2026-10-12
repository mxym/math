#!/usr/bin/env python3
"""Rebuild revised article editions in new directories; no Lean replay."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,zipfile

HERE=Path(__file__).resolve().parent

def build(source,inputs):
    env=os.environ.copy()
    env.update(SOURCE_DATE_EPOCH='1791460800',FORCE_SOURCE_DATE='1')
    with tempfile.TemporaryDirectory(prefix='mxym-article-revision-') as temp:
        work=Path(temp)
        for name in inputs:
            (work/name).parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(source/name,work/name)
        for n in range(3):
            run=subprocess.run(['pdflatex','-no-shell-escape','-interaction=nonstopmode',
                                '-halt-on-error','-file-line-error','paper.tex'],
                               cwd=work,env=env,capture_output=True,text=True,timeout=180)
            if run.returncode:raise RuntimeError(source.name+'\n'+run.stdout[-4000:])
        log=(work/'paper.log').read_text(errors='replace')
        bad=[s for s in log.splitlines() if any(v in s for v in
             ['Overfull','undefined','Missing character','LaTeX Warning','multiply defined'])]
        if bad:raise RuntimeError(source.name+'\n'+'\n'.join(bad))
        fonts=subprocess.check_output(['pdffonts',str(work/'paper.pdf')],text=True)
        if 'Type 3' in fonts:raise RuntimeError('Bitmap font: '+source.name)
        for line in fonts.splitlines()[2:]:
            if line.split()[-5]!='yes':raise RuntimeError('Unembedded font: '+source.name)
        pdf=(work/'paper.pdf').read_bytes()
        info=subprocess.check_output(['pdfinfo',str(work/'paper.pdf')],text=True)
        pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1])
        audit=source/'audit';audit.mkdir(exist_ok=True)
        (source/'paper.pdf').write_bytes(pdf)
        (audit/'build.log').write_text(log)
        (audit/'pdffonts.txt').write_text(fonts)
        (audit/'paper.txt').write_text(subprocess.check_output(['pdftotext','-layout',str(work/'paper.pdf'),'-'],text=True))
    archive=source/'paper-source.zip'
    with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for name in inputs:
            item=zipfile.ZipInfo(name,(2026,10,8,0,0,0))
            item.compress_type=zipfile.ZIP_DEFLATED;item.external_attr=0o644<<16
            z.writestr(item,(source/name).read_bytes())
    result={'status':'PASS','pages':pages,'passes':3,'fresh_directory':True,
            'shell_escape':False,'warnings':bad,'fonts_embedded':True,
            'pdf_sha256':hashlib.sha256(pdf).hexdigest(),
            'source_zip_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),
            'inputs':{name:hashlib.sha256((source/name).read_bytes()).hexdigest() for name in inputs},
            'scope':'Extracted TeX compilation, final diagnostics and fonts; not mathematical or Lean verification.'}
    (audit/'BUILD_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
    print('ARTICLE_BUILD_PASS',source.name,pages,'pages',flush=True)
    return result

def main():
    specs=json.loads((HERE/'CATALOG.json').read_text())['papers']
    for spec in specs:build(HERE/spec['slug'],spec['inputs'])
    build(HERE.parent/'all-graph-chollet-2026-10',['paper.tex'])

if __name__=='__main__':main()
