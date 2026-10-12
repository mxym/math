#!/usr/bin/env python3
"""Exact source inventory and transitive Lean imports; no dependency writes."""
from pathlib import Path
import hashlib, re

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def source_code(text):
    # Retain line structure; erase nested comments and double-quoted literals.
    out=[]; i=0; block=0; string=False
    while i < len(text):
        c=text[i]; two=text[i:i+2]
        if block:
            if two=='/-': block+=1; out.extend('  '); i+=2; continue
            if two=='-/': block-=1; out.extend('  '); i+=2; continue
            out.append('\n' if c=='\n' else ' '); i+=1; continue
        if string:
            if c=='\\' and i+1<len(text):
                out.extend('  '); i+=2; continue
            if c=='"': string=False
            out.append('\n' if c=='\n' else ' '); i+=1; continue
        if two=='/-': block=1; out.extend('  '); i+=2; continue
        if two=='--':
            j=text.find('\n',i)
            if j<0: out.extend(' '*(len(text)-i)); break
            out.extend(' '*(j-i)); i=j; continue
        if c=="'":
            char=re.match(r"'(?:\\[^\n]|[^\\'\n])'",text[i:])
            if char:
                out.extend(' '*len(char[0])); i+=len(char[0]); continue
        if c=='"': string=True; out.append(' '); i+=1; continue
        out.append(c); i+=1
    if block or string: raise RuntimeError('Unclosed source comment or string')
    return ''.join(out)

def import_record(path):
    code=source_code(path.read_text())
    names=[]
    for line in code.splitlines():
        match=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.*)$',line)
        if not match: continue
        tokens=match[1].split()
        if tokens and tokens[0]=='all': tokens=tokens[1:]
        for token in tokens:
            if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*',token):
                raise RuntimeError('Unparsed import token: '+token+' in '+str(path))
            names.append(token)
    implicit=not bool(re.search(r'^\s*prelude\s*$',code,re.M))
    all_names=list(dict.fromkeys((['Init'] if implicit else [])+names))
    return {'declared_imports':list(dict.fromkeys(names)),
            'implicit_Init':implicit,'imports':all_names}

def topo(graph):
    order=[]; done=set(); visiting=set()
    def visit(name):
        if name in done:return
        if name in visiting:raise RuntimeError('Import cycle: '+name)
        visiting.add(name)
        for dep in graph[name]['imports']:
            if dep in graph:visit(dep)
        visiting.remove(name); done.add(name); order.append(name)
    for name in sorted(graph):visit(name)
    return order

def root_sources(formal):
    files={}
    for namespace in ['Entry005','Mxym','OAI']:
        for path in (formal/namespace).rglob('*.lean'):
            files['.'.join(path.relative_to(formal).with_suffix('').parts)]=path
    for name in ['Entry005','Audit','MainTargetAudit','Upstream']:
        path=formal/(name+'.lean')
        if path.exists(): files[name]=path
    return files

def closure(formal, packages, lean_sources, pins):
    owned=root_sources(formal)
    # Exact source providers. Ambiguity is an error; no guessed resolution.
    providers=[('owned',formal)]+[(name,packages/name) for name in pins]+[('lean',lean_sources)]
    result={}
    def visit(name):
        if name in result:return
        relative=Path(name.replace('.','/')).with_suffix('.lean')
        candidates=[(package,base/relative) for package,base in providers if (base/relative).is_file()]
        if len(candidates)!=1:
            raise RuntimeError('Expected one source for '+name+', found '+str(candidates))
        package,path=candidates[0]
        try: record=import_record(path)
        except RuntimeError as error: raise RuntimeError(str(path)+': '+str(error)) from error
        record.update({'package':package,'relative_source':relative.as_posix(),
                       'sha256':digest(path)})
        result[name]=record
        for dependency in record['imports']:visit(dependency)
    for name in sorted(owned):visit(name)
    topo(result)
    return dict(sorted(result.items()))

def public_proof_inventory(sources):
    proofs=[]
    for module,path in sorted(sources.items()):
        if module in ['Entry005','Audit','MainTargetAudit','Upstream']:continue
        stack=[]
        for line in source_code(path.read_text()).splitlines():
            stripped=line.strip()
            match=re.match(r'^namespace\s+(\S+)\s*$',stripped)
            if match:stack.append(('namespace',match[1]));continue
            match=re.match(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$',stripped)
            if match:stack.append(('section',match[1]));continue
            match=re.match(r'^end(?:\s+(\S+))?\s*$',stripped)
            if match:
                name=match[1]
                if not stack:raise RuntimeError('Unbalanced end in '+module)
                if name and stack[-1][1]!=name:raise RuntimeError('Section mismatch in '+module+' '+str(stack)+' '+name)
                stack.pop();continue
            match=re.match(r'^(?:@\[[^\]]*\]\s*)*(?:protected\s+)?(?:theorem|lemma)\s+(\S+)',stripped)
            if match:
                ns='.'.join(name for kind,name in stack if kind=='namespace')
                proofs.append((ns+'.' if ns else '')+match[1])
    if len(proofs)!=len(set(proofs)):raise RuntimeError('Repeated public proof name')
    return sorted(proofs)
