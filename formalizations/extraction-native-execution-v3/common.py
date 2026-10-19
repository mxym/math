"""Shared, versioned native-execution binding helpers; no Lean on import."""
from pathlib import Path, PurePosixPath
import hashlib, json, re, subprocess
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parent.parent
PREFIX='formalizations/extraction-native-execution-v3'
PIN='d13f23b723b8a846827a245b89c10fc7d3f11612'
ALLOW={'propext','Classical.choice','Quot.sound'}

def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(data): return hashlib.sha256(data).hexdigest()
def unique_object(pairs):
    obj={}
    for k,v in pairs:
        if k in obj: raise ValueError('Duplicate JSON key: '+k)
        obj[k]=v
    return obj
def readj(path): return json.loads(Path(path).read_text(encoding='utf-8'),object_pairs_hook=unique_object)
def dump(path,obj): Path(path).write_text(json.dumps(obj,sort_keys=True,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
def git(*args): return subprocess.check_output(['git','-C',str(REPO),*args])
def safe_relative(name):
    if type(name)is not str or not name or '\\'in name: raise ValueError('Invalid relative path')
    p=PurePosixPath(name)
    if p.is_absolute()or '..'in p.parts or str(p)!=name or ':'in name: raise ValueError('Unsafe path: '+name)
    return name
def path_at(base,name):
    safe_relative(name); p=Path(base)/name
    if p.is_symlink()or not p.resolve().is_relative_to(Path(base).resolve()): raise ValueError('Symlink/outside path')
    return p
def stripped(s):
    out=[];i=0;depth=0
    while i<len(s):
        if s[i:i+2]=='/-': depth+=1;i+=2
        elif depth and s[i:i+2]=='-/':depth-=1;i+=2
        elif depth:
            if s[i]=='\n':out.append('\n')
            i+=1
        elif s[i:i+2]=='--':
            j=s.find('\n',i);i=len(s)if j<0 else j
        else:out.append(s[i]);i+=1
    if depth: raise ValueError('Unclosed comment')
    return ''.join(out)
def scope():
    s=readj(ROOT/'SCOPE.json')
    if s['schema']!=1: raise ValueError('Wrong scope schema')
    for key in ['theorems','models','controls']:
        ls=s[key]
        if not isinstance(ls,list)or len(ls)!=len(set(ls))or any(type(x)is not str for x in ls): raise ValueError('Invalid root class '+key)
    if set(s['theorems'])&set(s['models'])or s['controls']!=s['theorems']: raise ValueError('Every selected theorem requires a same-type control')
    for name,key in [('ROOTS.txt','theorems'),('MODELS.txt','models'),('CONTROLS.txt','controls')]:
        if (ROOT/name).read_text().splitlines()!=s[key]:raise ValueError('Scope/list drift')
    raw=(ROOT/'Driver.lean').read_text()
    for label,key in [('theoremNames','theorems'),('modelNames','models')]:
        expected='def '+label+' : List Name := [\n'+',\n'.join('  `'+n for n in s[key])+'\n]\n'
        if raw.count(expected)!=1:raise ValueError('Native compiled name list differs from scope')
    if '#[{ module := `ConcreteNativeExtraction.AssembledProgram }]'not in raw:raise ValueError('Wrong dynamic mathematical entry')
    return s
def package_roots():
    roots=[ROOT]
    for item in readj(ROOT/'lake-manifest.json')['packages']:
        if item['type']=='path':
            p=(ROOT/item['dir']).resolve()
            if not p.is_relative_to(REPO.resolve()):raise ValueError('External local package')
            roots.append(p)
    if len(roots)!=len(set(roots)):raise ValueError('Duplicate package root')
    return roots
def root_metadata_file(p):
    return Path(p)in {ROOT/n for n in ['SOURCE_HASHES.json','BINDING.json','PREPARATION_RESULT.json']}
def inventory():
    roots=package_roots();s=scope();seen=set();external=set();todo=[ROOT/'MathEntry.lean',ROOT/'Driver.lean']
    while todo:
        p=todo.pop()
        if p in seen:continue
        seen.add(p);raw=stripped(p.read_text())
        if not p.is_relative_to(ROOT)and re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',raw):raise ValueError('Forbidden math proof token '+str(p))
        for line in re.findall(r'^\s*(?:public\s+|private\s+)?import\s+([^\n]+)',raw,re.M):
            for mod in line.split():
                if mod.split('.')[0]in {'Mathlib','Lean','Std','Batteries','Aesop','Qq'}:external.add(mod);continue
                hits=[q/(mod.replace('.','/')+'.lean')for q in roots if (q/(mod.replace('.','/')+'.lean')).is_file()]
                if len(hits)!=1:raise ValueError('Missing/ambiguous module '+mod)
                todo.append(hits[0])
    forbidden=['TM2','OuterList','outerlist']
    if any(any(x in str(p)for x in forbidden)for p in seen):raise ValueError('Unused successor entered closure')
    selected=set(seen)
    for p in ROOT.rglob('*'):
        rel=p.relative_to(ROOT)
        if p.is_file()and not any(x in {'.lake','verification','__pycache__'}for x in rel.parts)and not root_metadata_file(p):selected.add(p)
    for q in roots:
        for n in ['lakefile.toml','lakefile.lean','lake-manifest.json','lean-toolchain']:
            if (q/n).is_file():selected.add(q/n)
    selected.add(REPO/'.github/workflows/extraction-native-execution-v3.yml')
    result={}
    for p in sorted(selected):
        rel=p.relative_to(REPO).as_posix();path_at(REPO,rel)
        if not p.is_relative_to(ROOT)and not rel.startswith('.github/'):
            original=git('show',s['source_commit']+':'+rel)
            if p.read_bytes()!=original:raise ValueError('Source differs from exact mathematical Git object '+rel)
        result[rel]=sha(p)
    return result,{p.relative_to(REPO).as_posix():sha(p)for p in sorted(seen)if not p.is_relative_to(ROOT)},sorted(external)
def protected_inputs():
    p=readj(ROOT/'PROTECTED_OLD_INPUTS.json')
    expected={'older4378':4378,'core605':605,'algorithm340':340,'raw372':372,'native531':531,'r2_failed13':13}
    if p['group_counts']!=expected:raise ValueError('Old protection scope mismatch')
    for name,want in p['files'].items():
        if sha(path_at(REPO,name))!=want:raise ValueError('Protected old source/evidence changed '+name)
    return p
def binding():
    s=scope()
    if s['state']!='READY'or s['pending_required']or not re.fullmatch('[a-f0-9]{40}',s['source_commit']or''):raise ValueError('Final scope not ready')
    b=readj(ROOT/'BINDING.json')
    if b['schema']!=1 or b['source_commit']!=s['source_commit']:raise ValueError('Wrong binding')
    actual,closure,external=inventory()
    if actual!=readj(ROOT/'SOURCE_HASHES.json')or sha(ROOT/'SOURCE_HASHES.json')!=b['source_manifest_sha256']:raise ValueError('Bound source/config drift')
    if closure!=readj(ROOT/'IMPORT_CLOSURE_HASHES.json'):raise ValueError('Import closure drift')
    if sha(ROOT/'PROTECTED_OLD_INPUTS.json')!=b['protected_manifest_sha256']:raise ValueError('Protected manifest drift')
    protected_inputs()
    if sha(REPO/'.github/workflows/extraction-native-execution-v3.yml')!=sha(ROOT/'extraction-native-execution-v3.workflow.yml'):raise ValueError('Actual/template workflow drift')
    return s,b
def parse_axioms(text,names):
    text=re.sub(r'^info:.*?:[0-9]+:[0-9]+: ','',text,flags=re.M)
    rows=[]
    for name,raw in re.findall(r"^'([^']+)' depends on axioms: \[([^]]*)\]$",text,re.M):rows.append((name,[x.strip()for x in raw.split(',')if x.strip()]))
    rows += [(n,[])for n in re.findall(r"^'([^']+)' does not depend on any axioms$",text,re.M)]
    if len(rows)!=len(names)or {n for n,_ in rows}!=set(names):raise ValueError('Missing/duplicate selected axiom output')
    if any(set(a)-ALLOW for _,a in rows):raise ValueError('Unexpected axiom')
    return dict(rows)
def file_manifest(out):
    out=Path(out);result={}
    for p in sorted(out.rglob('*')):
        if p.is_symlink():raise ValueError('Symlinked artifact')
        if p.is_file()and p!=out/'EVIDENCE_HASHES.json':result[p.relative_to(out).as_posix()]=sha(p)
    return result
def expected_owned_outputs():
    inputs=list(readj(ROOT/'IMPORT_CLOSURE_HASHES.json'))
    packages=sorted(package_roots(),key=lambda p:len(p.parts),reverse=True);outputs=set()
    for n in inputs:
        source=REPO/n;pkg=next(p for p in packages if source.is_relative_to(p))
        outputs.add((pkg/'.lake/build/lib/lean'/source.relative_to(pkg).with_suffix('.olean')).relative_to(REPO).as_posix())
    return outputs
