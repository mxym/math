#!/usr/bin/env python3
"""Strict source-only import closure for the quadratic-orders Main package.
No compiler object can substitute for a missing source. Dependencies are read-only.
"""
from pathlib import Path
import hashlib,re
BRIDGES=('ArithmeticSupplyRayBridge','ArithmeticSupplyRayConductor','ArithmeticSupplyWeakFromDirichlet','ArithmeticSupplyWeakMainReduction','ArithmeticSupplyWeakMain')

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def source_code(text):
    out=[]; i=0; block=0; string=False
    while i<len(text):
        c=text[i];two=text[i:i+2]
        if block:
            if two=='/-':block+=1;out.extend('  ');i+=2;continue
            if two=='-/':block-=1;out.extend('  ');i+=2;continue
            out.append('\n' if c=='\n' else ' ');i+=1;continue
        if string:
            if c=='\\' and i+1<len(text):out.extend('  ');i+=2;continue
            if c=='"':string=False
            out.append('\n' if c=='\n' else ' ');i+=1;continue
        if two=='/-':block=1;out.extend('  ');i+=2;continue
        if two=='--':
            j=text.find('\n',i)
            if j<0:out.extend(' '*(len(text)-i));break
            out.extend(' '*(j-i));i=j;continue
        if c=="'":
            char=re.match(r"'(?:\\[^\n]|[^\\'\n])'",text[i:])
            if char:out.extend(' '*len(char[0]));i+=len(char[0]);continue
        if c=='"':string=True;out.append(' ');i+=1;continue
        out.append(c);i+=1
    if block or string:raise RuntimeError('Unclosed comment or string')
    return ''.join(out)

def import_record(path):
    code=source_code(path.read_text());names=[]
    for line in code.splitlines():
        match=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.*)$',line)
        if not match:continue
        tokens=match[1].split()
        if tokens and tokens[0]=='all':tokens=tokens[1:]
        for token in tokens:
            if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*',token):raise RuntimeError('Unparsed import token '+token+' in '+str(path))
            names.append(token)
    implicit=not bool(re.search(r'^\s*prelude\s*$',code,re.M))
    return {'declared_imports':list(dict.fromkeys(names)),'implicit_Init':implicit,'imports':list(dict.fromkeys((['Init'] if implicit else [])+names))}

def topo(graph):
    result=[];done=set();active=set()
    def walk(n):
        if n in done:return
        if n in active:raise RuntimeError('Import cycle: '+n)
        active.add(n)
        for d in graph[n]['imports']:
            if d in graph:walk(d)
        active.remove(n);done.add(n);result.append(n)
    for n in sorted(graph):walk(n)
    return result

def owned_sources(project):
    f=project/'lean';result={'Entry002':f/'Entry002.lean'}
    result.update({'.'.join(p.relative_to(f).with_suffix('').parts):p for p in (f/'Entry002').glob('*.lean')})
    result.update({n:f/'references/upstream/arithmetic-audit'/(n+'.lean') for n in BRIDGES})
    return result

def providers(project,packages,lean_sources,pins):
    f=project/'lean'
    return [('main',f),('bridges',f/'references/upstream/arithmetic-audit'),('cft',f/'references/upstream/ClassFieldTheory/Lean4')]+[(n,packages/n) for n in pins]+[('lean',lean_sources),('lean',lean_sources/'lake')]

def closure(project,packages,lean_sources,pins,external_modules):
    places=providers(project,packages,lean_sources,pins);result={}
    def visit(n):
        if n in result:return
        rel=Path(n.replace('.','/')).with_suffix('.lean')
        choices=[(kind,base/rel) for kind,base in places if (base/rel).is_file()]
        if len(choices)!=1:raise RuntimeError('Expected one source provider for '+n+', got '+str(choices))
        kind,path=choices[0];r=import_record(path);r.update({'package':kind,'relative_source':(path.relative_to(lean_sources).as_posix() if kind=='lean' else rel.as_posix()),'sha256':digest(path)})
        result[n]=r
        for dep in r['imports']:visit(dep)
    for n in sorted(set(owned_sources(project))|set(external_modules)|{'Lean','Lean.Replay','Init.Data.Nat.Lemmas'}):visit(n)
    topo(result)
    return dict(sorted(result.items()))
