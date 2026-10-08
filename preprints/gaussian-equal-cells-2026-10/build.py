#!/usr/bin/env python3
"""Build standalone PDF and TeX ZIP in a fresh directory; typesetting only."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,zipfile
HERE=Path(__file__).resolve().parent

def main():
    env=os.environ.copy();env.update(SOURCE_DATE_EPOCH='1791417600',FORCE_SOURCE_DATE='1')
    audit=HERE/'audit';audit.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='gaussian-paper-') as t:
        w=Path(t);shutil.copyfile(HERE/'paper.tex',w/'paper.tex')
        for n in range(3):
            r=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','paper.tex'],cwd=w,env=env,text=True,capture_output=True)
            if r.returncode:raise RuntimeError(r.stdout[-4000:])
        log=(w/'paper.log').read_text(errors='replace')
        bad=[s for s in log.splitlines() if any(v in s for v in ['Overfull','undefined','Missing character','LaTeX Warning'])]
        if bad:raise RuntimeError('\n'.join(bad))
        fonts=subprocess.check_output(['pdffonts',str(w/'paper.pdf')],text=True)
        if re.search(r'\bno\s+(?:yes|no)\s+(?:yes|no)\s+\d+\s+\d+\s*$',fonts,re.M):raise RuntimeError('Unembedded font')
        pdf=(w/'paper.pdf').read_bytes();(HERE/'paper.pdf').write_bytes(pdf)
        (audit/'build.log').write_text(log);(audit/'pdffonts.txt').write_text(fonts)
        info=subprocess.check_output(['pdfinfo',str(w/'paper.pdf')],text=True)
        pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1])
        subprocess.run(['pdftotext','-layout',str(HERE/'paper.pdf'),str(audit/'paper.txt')],check=True)
    with zipfile.ZipFile(HERE/'paper-source.zip','w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        i=zipfile.ZipInfo('paper.tex',(2026,10,8,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o644<<16;z.writestr(i,(HERE/'paper.tex').read_bytes())
    report={'status':'PASS','passes':3,'fresh_directory':True,'pages':pages,'warnings':bad,'fonts_embedded':True,'pdf_sha256':hashlib.sha256(pdf).hexdigest(),'tex_sha256':hashlib.sha256((HERE/'paper.tex').read_bytes()).hexdigest(),'source_zip_sha256':hashlib.sha256((HERE/'paper-source.zip').read_bytes()).hexdigest(),'scope':'Typesetting and font checks; not mathematical or Lean certification.'}
    (audit/'BUILD_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
