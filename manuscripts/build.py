#!/usr/bin/env python3
"""Build all five manuscripts in isolation, without TeX shell escape."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
PAPERS = ('sharp-simplex-stability', 'continuum-power-avoidance',
          'fractional-cover-spectrum', 'complex-permanent-pencil',
          'orbital-atom-stability')


def command(args, cwd, env):
    p = subprocess.run(args, cwd=cwd, env=env, capture_output=True)
    if p.returncode:
        raise RuntimeError(' '.join(map(str,args))+'\n'+
                           (p.stdout+p.stderr).decode(errors='replace')[-6500:])
    return p.stdout


def environment(build):
    env = os.environ.copy()
    cache = build/'tex-cache'
    cache.mkdir()
    env.update(TEXMFVAR=str(cache), TEXMFCONFIG=str(build/'tex-config'),
               VARTEXFONTS=str(build/'tex-fonts'))
    probes=[subprocess.run(['kpsewhich',p],cwd=build,env=env,capture_output=True)
            for p in ('article.cls','pdftex.map','pdflatex.fmt')]
    if all(p.returncode==0 and p.stdout.strip() for p in probes):
        return env
    base = Path('/usr/share/texlive/texmf-dist')
    extra = Path('/usr/share/texmf')
    if not base.is_dir():
        raise RuntimeError('Install a working TeX Live distribution.')
    (cache/'language.dat').write_text('english hyphen.tex\n')
    env.update(TEXMF='{'+str(base)+','+str(extra)+'}',
        TEXINPUTS='.:{0}:{1}/tex//:{2}/tex//:'.format(cache,base,extra),
        TEXFORMATS=str(cache)+':',
        TEXFONTMAPS='{0}:{1}/fonts/map//:{2}/fonts/map//:'.format(cache,base,extra))
    for variable, directory in [('TFMFONTS','tfm'),('VFFONTS','vf'),
                               ('T1FONTS','type1'),('ENCFONTS','enc')]:
        env[variable]=f'{base}/fonts/{directory}//:{extra}/fonts/{directory}//:'
    maps = [extra/'fonts/map/dvips/lm/lm.map']+[
        base/f'fonts/map/dvips/amsfonts/{name}.map' for name in ('cm','symbols','euler')]
    (cache/'pdftex.map').write_bytes(b'\n'.join(p.read_bytes() for p in maps))
    command(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode',
             '-halt-on-error','-jobname=pdflatex',
             str(base/'tex/latex/tex-ini-files/pdflatex.ini')],cache,env)
    return env


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True,
                        help='A new external directory for PDFs, sources and logs')
    args=parser.parse_args()
    output=args.output.resolve()
    output.mkdir(parents=True,exist_ok=False)
    report=[]
    with tempfile.TemporaryDirectory(prefix='math-five-papers-') as temp:
        build=Path(temp)
        env=environment(build)
        for name in PAPERS:
            source=HERE/name
            work=build/name
            work.mkdir()
            for file in source.glob('*.tex'):
                shutil.copyfile(file,work/file.name)
            if (source/'paper.md').exists():
                header=work/'header.tex'
                header.write_text('\\usepackage{amsmath,amssymb,mathtools,xurl}\n'
                                  '\\emergencystretch=3em\n')
                command(['pandoc',str(source/'paper.md'),
                    '--from=markdown+tex_math_single_backslash','--standalone',
                    '--include-in-header='+str(header),'-V','geometry:margin=25mm',
                    '-V','fontsize:11pt','-o',str(work/'paper.tex')],work,env)
                # Some inherited prose uses mathematical Unicode outside math
                # fences. Supply its exact TeX counterpart for pdfLaTeX.
                text=(work/'paper.tex').read_text()
                equivalents={'≥':r'\ge','≤':r'\le','∈':r'\in','∩':r'\cap',
                    '∪':r'\cup','≠':r'\ne','→':r'\to','∞':r'\infty',
                    'Θ':r'\Theta','τ':r'\tau','ν':r'\nu','Ψ':r'\Psi',
                    'δ':r'\delta','σ':r'\sigma','λ':r'\lambda','ℓ':r'\ell',
                    '√':r'\surd','⊂':r'\subset','⊆':r'\subseteq',
                    'ℝ':r'\mathbb R','ℕ':r'\mathbb N','ℤ':r'\mathbb Z',
                    '×':r'\times','±':r'\pm','−':'-','₂':'2','₃':'3'}
                for char,replacement in equivalents.items():
                    if char in text:
                        text=text.replace(char,r'\ensuremath{'+replacement+'}')
                (work/'paper.tex').write_text(text)
            for _ in range(3):
                command(['pdflatex','-no-shell-escape','-interaction=nonstopmode',
                         '-halt-on-error','paper.tex'],work,env)
            log=(work/'paper.log').read_text(errors='replace')
            if re.search(r'undefined references|undefined on input|multiply defined|Missing character',log):
                raise RuntimeError('Unresolved reference/character in '+name)
            destination=output/name
            destination.mkdir()
            for file in work.iterdir():
                if file.suffix in ('.tex','.pdf','.log'):
                    shutil.copyfile(file,destination/file.name)
            text=command(['pdftotext','-layout','paper.pdf','-'],work,env)
            if len(text)<1000:
                raise RuntimeError('PDF text missing in '+name)
            (destination/'paper.txt').write_bytes(text)
            info=command(['pdfinfo','paper.pdf'],work,env).decode()
            overfull=re.findall(r'Overfull \\hbox \(([^)]+)\)',log)
            report.append({'paper':name,'status':'PASS',
                'pdf_sha256':sha256((work/'paper.pdf').read_bytes()).hexdigest(),
                'pages':int(re.search(r'Pages:\s+(\d+)',info)[1]),
                'overfull_hboxes':overfull,
                'source':str((source/('paper.md' if (source/'paper.md').exists() else 'paper.tex')).relative_to(HERE))})
            print('PASS PDF '+name,flush=True)
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':
    main()
