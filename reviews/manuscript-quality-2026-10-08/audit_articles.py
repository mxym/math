"""Fresh source-ZIP typesetting audit of the 17 current article entries."""
from pathlib import Path
import concurrent.futures,hashlib,json,os,re,subprocess,tempfile,zipfile
import argparse
if not __debug__: raise SystemExit('Run without -O or -OO')
ROOT=Path(__file__).resolve().parents[2]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,required=True)
parser.add_argument('--reuse-unchanged',action='store_true')
args=parser.parse_args()
OUT=args.output.resolve();OUT.mkdir(parents=True,exist_ok=True)
specs=[('bapat','submissions/arxiv-2026-10/bapat-q-permanent-counterexamples','main.tex','bapat-arxiv-source.zip'),
       ('gaussian-equal','preprints/gaussian-equal-cells-2026-10','paper.tex','paper-source.zip'),
       ('all-graph-chollet','preprints/all-graph-chollet-2026-10','paper.tex','paper-source.zip')]
cat=json.loads((ROOT/'preprints/lean-certified-2026-10/CATALOG.json').read_text())
specs.extend((x['slug'],'preprints/lean-certified-2026-10/'+x['slug'],'paper.tex','paper-source.zip') for x in cat['papers'])
specs.extend((x['slug'],'preprints/article-revisions-2026-10/'+x['slug'],'paper.tex','paper-source.zip')
             for x in json.loads((ROOT/'preprints/article-revisions-2026-10/CATALOG.json').read_text())['papers'])
assert len(specs)==17

def sha(b):return hashlib.sha256(b).hexdigest()
def run(args,work,env=None):return subprocess.check_output(args,cwd=work,env=env,text=True,stderr=subprocess.STDOUT,timeout=180)
def check(spec):
    name,folder,entry,archive=spec;source=ROOT/folder
    env=os.environ.copy();env.update(SOURCE_DATE_EPOCH='1791460800',FORCE_SOURCE_DATE='1')
    out=OUT/name;out.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='article-audit-') as temp:
        work=Path(temp);files={}
        zip_path=source/archive if archive else None
        if zip_path:
            with zipfile.ZipFile(zip_path) as z:
                assert len(z.namelist())==len(set(z.namelist()))
                for item in z.infolist():
                    assert not item.is_dir() and not item.filename.startswith('/') and '..' not in Path(item.filename).parts
                    data=z.read(item)
                    assert data==(source/item.filename).read_bytes(),(name,'source mismatch',item.filename)
                    p=work/item.filename;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
                    files[item.filename]=sha(data)
        else:
            for p in source.glob('*.tex'):
                data=p.read_bytes();(work/p.name).write_bytes(data);files[p.name]=sha(data)
        def active_tex(path,stack=()):
            assert path not in stack,(name,'recursive TeX input')
            content=path.read_text()
            for target in re.findall(r'\\(?:input|include)\{([^}]+)\}',content):
                child=path.parent/(target if Path(target).suffix else target+'.tex')
                content+='\n'+active_tex(child,stack+(path,))
            return content
        tex=active_tex(work/entry)
        labels=re.findall(r'\\label\{([^}]+)\}',tex)
        refs=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',tex)
        cites=[k.strip() for g in re.findall(r'\\cite(?:\[[^]]*\])*\{([^}]+)\}',tex) for k in g.split(',')]
        bib=re.findall(r'\\bibitem(?:\[[^]]*\])?\{([^}]+)\}',tex)
        assert len(labels)==len(set(labels)),(name,'duplicate labels')
        assert not (set(refs)-set(labels)),(name,'undefined source references')
        assert not (set(cites)-set(bib)),(name,'undefined source citations')
        engine='pdflatex'
        for n in range(3):run([engine,'-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error',entry],work,env)
        stem=Path(entry).stem
        log=(work/(stem+'.log')).read_text(errors='replace')
        bad=[l for l in log.splitlines() if any(s in l for s in ['Overfull','undefined','Missing character','LaTeX Warning','multiply defined'])]
        assert not bad,(name,bad)
        pdf=work/(stem+'.pdf');fonts=run(['pdffonts',str(pdf)],work)
        assert 'Type 3' not in fonts,(name,'bitmap fonts')
        for line in fonts.splitlines()[2:]:assert line.split()[-5]=='yes',(name,'unembedded font')
        info=run(['pdfinfo',str(pdf)],work);text=run(['pdftotext','-layout',str(pdf),'-'],work)
        assert 'Yongxian Zhang' in text,(name,'author absent from paper')
        assert re.search(r'0009.?0000.?3864.?3536',text),(name,'ORCID absent')
        (out/'paper.pdf').write_bytes(pdf.read_bytes());(out/'build.log').write_text(log)
        (out/'pdffonts.txt').write_text(fonts);(out/'paper.txt').write_text(text)
        (out/'bbox.html').write_text(run(['pdftotext','-bbox',str(pdf),'-'],work))
        result={'key':name,'source_root':folder,'status':'PASS',
                'pages':int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1]),
                'passes':3,'engine':engine,'source_sha256':files,'compiled_pdf_sha256':sha(pdf.read_bytes()),
                'fresh_extracted_zip':bool(zip_path),'source_zip_sha256':sha(zip_path.read_bytes()) if zip_path else None,
                'all_fonts_embedded':True,'bitmap_fonts':False,'author_and_orcid_present':True,
                'undefined_references':[],'undefined_citations':[],'overfull_boxes':[],
                'latex_warnings':[],'bibliography_keys':bib,
                'scope':'Typesetting and source-ZIP correspondence, not external peer review, new proof audit or Lean replay.'}
        (out/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
        print('ARTICLE_AUDIT_PASS',name,result['pages'],flush=True)
        return result

def main():
    def current(spec):
        name,folder,entry,archive=spec
        p=OUT/name/'AUDIT.json'
        if args.reuse_unchanged and p.exists():
            result=json.loads(p.read_text());source=ROOT/folder
            expected_engine='pdflatex'
            valid=result.get('engine')==expected_engine and all((source/n).exists() and sha((source/n).read_bytes())==h for n,h in result['source_sha256'].items())
            if archive:valid=valid and sha((source/archive).read_bytes())==result['source_zip_sha256']
            if valid:
                print('ARTICLE_AUDIT_RETAINED',name,result['pages'],flush=True)
                return result
        return check(spec)
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
        results=list(pool.map(current,specs))
    for item in results:
        pdf=ROOT/item['source_root']/'paper.pdf'
        item['distributed_pdf_sha256']=sha(pdf.read_bytes())
        fonts=run(['pdffonts',str(pdf)],ROOT)
        assert 'Type 3' not in fonts
        assert all(l.split()[-5]=='yes' for l in fonts.splitlines()[2:])
        info=run(['pdfinfo',str(pdf)],ROOT)
        assert int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1])==item['pages']
        item['distributed_pdf_fonts_embedded']=True
    (OUT/'BUILD_AND_SOURCE_AUDIT.json').write_text(json.dumps({'status':'PASS','date':'2026-10-08',
        'reviewer':'Primary AI assistant, working without subagents',
        'scope':'All 17 article source/ZIP identities, fresh 3-pass TeX compilation and bibliography-key resolution; no new Lean replay or external human peer review.',
        'papers':results},indent=2)+'\n')
    print('ALL_ARTICLES_AUDITED',len(results),sum(x['pages'] for x in results),'pages')
if __name__=='__main__':main()
