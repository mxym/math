#!/usr/bin/env python3
"""Introduce proof-carrying literal barriers in generated nested coefficient merges.

No theorem type changes, no additional mathematical premises. Each primitive
operation receives a kernel-checked equality; congruence/transitivity composes
these equalities instead of repeatedly normalizing a large nested expression.
"""
from __future__ import annotations
import argparse
import ast
import re
from pathlib import Path

MARKER = '-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.\n'
ARITY = {p + '.' + op: arity for p, ops in {
    'CoefficientMerge': {'trim':1, 'scale':2, 'fastMerge':2},
    'SparsePolynomial': {'trim':1, 'scale':2, 'merge':2},
}.items() for op, arity in ops.items()}
DEFINITION = re.compile(r'^def (\w+) : (CoefficientMerge|SparsePolynomial)\.Poly := (\[.*\])$', re.M)
EQUALITY = re.compile(r'^theorem (\w+_data) : (\w+) = (.+) := by decide \+kernel$', re.M)


def parse(text: str):
    tokens = re.findall(r'-?\d+|[A-Za-z_][A-Za-z_0-9.]*|[():]', text)
    pos = 0
    def term():
        nonlocal pos
        if pos == len(tokens):
            raise ValueError('Unexpected end of coefficient expression')
        t=tokens[pos];pos+=1
        if t == '(':
            value=term()
            if tokens[pos] == ':':
                pos+=1
                if tokens[pos] != 'Int':raise ValueError('Unexpected scalar type')
                pos+=1
            if tokens[pos] != ')':raise ValueError('Expected closing parenthesis')
            pos+=1
            return value
        if t in ARITY:return (t, *[term() for _ in range(ARITY[t])])
        if re.fullmatch(r'-?\d+',t):return int(t)
        if t in '():':raise ValueError('Unexpected punctuation')
        return t
    result=term()
    if pos != len(tokens):raise ValueError('Unparsed coefficient expression suffix')
    return result


def render(node):
    if isinstance(node,int):return f'({node} : Int)'
    if isinstance(node,str):return node
    return '('+node[0]+' '+' '.join(render(t) for t in node[1:])+')'


def merge(left, right):
    i=j=0;out=[]
    while i<len(left) and j<len(right):
        k,c=left[i];l,d=right[j]
        if k<l:out.append((k,c));i+=1
        elif l<k:out.append((l,d));j+=1
        else:out.append((k,c+d));i+=1;j+=1
    return out+left[i:]+right[j:]


def transform_dimension(root: Path, dimension: int, selected: set[str] | None = None):
    directory=root/f'APPT/Finite{dimension}Sparse'
    symbols={}
    for path in sorted(directory.glob('*.lean')):
        for name,typ,literal in DEFINITION.findall(path.read_text()):
            value=(typ,ast.literal_eval(literal))
            if name in symbols and symbols[name] != value:raise ValueError('Conflicting literal '+name)
            symbols[name]=value
    reports=[]
    for path in sorted(directory.glob('*.lean')):
        if selected is not None and path.stem not in selected:continue
        text=path.read_text()
        if text.startswith(MARKER):continue
        changed=[]
        def replace(match):
            theorem,lhs,expression=match.groups()
            count=expression.count('CoefficientMerge.fastMerge')+expression.count('SparsePolynomial.merge')
            if count<2:return match[0]
            tree=parse(expression)
            typ= symbols[lhs][0]
            lines=[];serial=0
            def normalize(node):
                nonlocal serial
                if isinstance(node,int):return node,None,None
                if isinstance(node,str):
                    if node not in symbols:raise ValueError('Unknown literal '+node)
                    if symbols[node][0] != typ:raise ValueError('Mixed coefficient types')
                    return node,symbols[node][1],None
                op=node[0]
                if not op.startswith(typ+'.'):raise ValueError('Mixed arithmetic types')
                children=[normalize(c) for c in node[1:]]
                if op.endswith('.trim'):out=[(k,c) for k,c in children[0][1] if c != 0]
                elif op.endswith('.scale'):out=[(k,children[0][0]*c) for k,c in children[1][1]]
                else:out=merge(children[0][1],children[1][1])
                name=f'{theorem}_flat{serial:03d}';serial+=1
                symbols[name]=(typ,out)
                rhs='('+op+' '+' '.join(render(c[0]) for c in children)+')'
                lines.append(f'def {name} : {typ}.Poly := {out!r}')
                lines.append(f'theorem {name}_step : {name} = {rhs} := by decide +kernel')
                rewrites=[name+'_step']+[c[2] for c in children if c[2] is not None]
                lines.append(f'theorem {name}_original : {name} = {render(node)} := by\n  rw ['+', '.join(rewrites)+']')
                return name,out,name+'_original'
            name,out,proof=normalize(tree)
            if symbols[lhs][1] != out:raise ValueError('Exact output mismatch: '+theorem)
            lines.append(f'theorem {theorem} : {lhs} = {expression} := by\n  have h : {lhs} = {name} := by decide +kernel\n  exact h.trans {proof}')
            changed.append({'theorem':theorem,'primitive_checks':serial,'coefficients':len(out)})
            return '\n'.join(lines)
        result=EQUALITY.sub(replace,text)
        if changed:
            path.write_text(MARKER+result)
            reports.append({'path':str(path.relative_to(root)),'theorems':changed})
    return reports


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--dimensions',type=int,nargs='+',default=[9,12,15,18,21,24])
    p.add_argument('--files',nargs='+')
    args=p.parse_args()
    import json
    reports=[]
    for d in args.dimensions:
        reports.extend(transform_dimension(args.root,d,set(args.files) if args.files else None))
    print(json.dumps(reports,indent=2))

if __name__=='__main__':main()
