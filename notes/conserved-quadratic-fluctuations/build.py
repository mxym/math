#!/usr/bin/env python3
"""Rebuild three-pass PDF twice, with fixed metadata and no shell escape."""
from __future__ import annotations
import argparse,hashlib,json,os,re,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
EPOCH=1791331200

def run(command,work,env):
    result=subprocess.run(command,cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if result.returncode: raise RuntimeError('TeX command failed:\n'+result.stdout[-12000:])
    return result.stdout

def located(name,env):
    p=subprocess.run(['kpsewhich',name],env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    return p.returncode==0 and bool(p.stdout.strip())

def build_once():
    env=os.environ.copy(); env.update(SOURCE_DATE_EPOCH=str(EPOCH),FORCE_SOURCE_DATE='1',TZ='UTC',LC_ALL='C',openout_any='p')
    with tempfile.TemporaryDirectory(prefix='quadratic-tex-') as temporary:
        work=Path(temporary); shutil.copyfile(ROOT/'manuscript.tex',work/'manuscript.tex'); shutil.copytree(ROOT/'sections',work/'sections')
        fallback=not all(located(name,env) for name in ['article.cls','pdflatex.fmt','pdftex.map'])
        if fallback:
            base=Path('/usr/share/texlive/texmf-dist'); extra=Path('/usr/share/texmf'); cache=work/'tex-cache'; cache.mkdir()
            ini=base/'tex/latex/tex-ini-files/pdflatex.ini'
            if not ini.is_file(): raise RuntimeError('Missing usable system TeX format; install a standard pdfLaTeX distribution.')
            env.update(TEXMF='{'+str(base)+','+str(extra)+'}',TEXINPUTS='.:{}'.format(cache)+':'+str(base)+'/tex//:'+str(extra)+'/tex//:',TFMFONTS=str(base)+'/fonts/tfm//:'+str(extra)+'/fonts/tfm//:',VFFONTS=str(base)+'/fonts/vf//:'+str(extra)+'/fonts/vf//:',T1FONTS=str(base)+'/fonts/type1//:'+str(extra)+'/fonts/type1//:',ENCFONTS=str(base)+'/fonts/enc//:'+str(extra)+'/fonts/enc//:',TEXFORMATS=str(cache)+':',TEXFONTMAPS=str(cache)+':'+str(base)+'/fonts/map//:'+str(extra)+'/fonts/map//:',TEXMFVAR=str(cache/'var'),TEXMFCONFIG=str(cache/'config'))
            (cache/'language.dat').write_text('english hyphen.tex\n')
            maps=[extra/'fonts/map/dvips/lm/lm.map',base/'fonts/map/dvips/amsfonts/cm.map',base/'fonts/map/dvips/amsfonts/symbols.map',base/'fonts/map/dvips/amsfonts/euler.map']
            (cache/'pdftex.map').write_bytes(b'\n'.join(p.read_bytes() for p in maps))
            run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex',str(ini)],cache,env)
        for _ in range(3):
            run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error','-recorder','manuscript.tex'],work,env)
        pdf=(work/'manuscript.pdf').read_bytes(); log=(work/'manuscript.log').read_text()
        problems=[l for l in log.splitlines() if 'Overfull ' in l or 'undefined' in l or 'multiply defined' in l]
        if problems: raise RuntimeError('Layout/reference problems:\n'+'\n'.join(problems))
        log=log.replace(str(work),'<build-directory>').replace('/usr/share/texlive/texmf-dist','<texlive>').replace('/usr/share/texmf','<texmf>')
        # Keep content/toolchain pins without filesystem or temporary-directory metadata.
        inputs={}
        for line in (work/'manuscript.fls').read_text().splitlines():
            if not line.startswith('INPUT '): continue
            p=Path(line[6:]); p=p if p.is_absolute() else work/p
            if not p.is_file(): continue
            name=str(p.resolve())
            if name.startswith(str(work)): continue
            name=name.replace('/usr/share/texlive/texmf-dist/','texlive/').replace('/usr/share/texmf/','texmf/')
            if name.startswith('/'): name='toolchain/'+p.name
            inputs[name]={'bytes':len(p.read_bytes()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
        return pdf,log,{'fallback_format':fallback,'hyphenation':'english hyphen.tex' if fallback else 'system format','layout_or_reference_problems':[], 'toolchain_inputs':inputs}

def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('--verify-repeat',action='store_true'); parser.add_argument('--output',type=Path,default=ROOT/'manuscript.pdf'); args=parser.parse_args()
    data,log,details=build_once(); digest=hashlib.sha256(data).hexdigest()
    report={'source_date_epoch':EPOCH,'passes_per_build':3,'shell_escape':False,'pdf_bytes':len(data),'first_sha256':digest,'engine':subprocess.check_output(['pdflatex','--version'],text=True).splitlines()[0], 'python':subprocess.check_output(['python3','--version'],text=True).strip(), **details}
    if args.verify_repeat:
        second,_,_=build_once(); report.update(second_sha256=hashlib.sha256(second).hexdigest(),independent_fresh_builds_identical=data==second)
        if data!=second: raise RuntimeError('Fresh builds differ.')
    (ROOT/'build').mkdir(exist_ok=True); (ROOT/'build/manuscript.log').write_text(log); (ROOT/'build/determinism.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n'); args.output.parent.mkdir(parents=True,exist_ok=True); args.output.write_bytes(data)
    print(json.dumps({k:v for k,v in report.items() if k!='toolchain_inputs'},indent=2))
if __name__=='__main__': main()
