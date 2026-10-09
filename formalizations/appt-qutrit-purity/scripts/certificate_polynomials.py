#!/usr/bin/env python3
"""Generate bounded, kernel-checkable integer certificate blocks.
The generator is not trusted: every identity and sign is proved in Lean.
Only Python integer/Fraction arithmetic is used; no optimizer is imported.
"""
from __future__ import annotations
import argparse, ast, hashlib, json, math, re
from fractions import Fraction
from pathlib import Path


def balanced(xs: list[str]) -> str:
    if not xs: return '(0 : ℝ)'
    if len(xs) == 1: return xs[0]
    k = len(xs) // 2
    return '(' + balanced(xs[:k]) + ' + ' + balanced(xs[k:]) + ')'


def prod(xs: list[str]) -> str:
    return '(' + ' * '.join(xs) + ')' if xs else '(1 : ℝ)'


class Algebra:
    def __init__(self, n: int):
        self.n = n
        self.zero = (0,) * n
    def c(self, x: int) -> dict:
        return {self.zero: x} if x else {}
    def v(self, i: int) -> dict:
        e = [0] * self.n; e[i] = 1
        return {tuple(e): 1}
    def add(self, *ps: dict) -> dict:
        out = {}
        for p in ps:
            for e,c in p.items(): out[e] = out.get(e, 0) + c
        return {e:c for e,c in out.items() if c}
    def scale(self, c: int, p: dict) -> dict:
        return {e:c*x for e,x in p.items() if c*x}
    def sub(self, p: dict, q: dict) -> dict:
        return self.add(p, self.scale(-1,q))
    def mul(self, *ps: dict) -> dict:
        out = self.c(1)
        for p in ps:
            tmp = {}
            for a,c in out.items():
                for b,d in p.items():
                    e = tuple(x+y for x,y in zip(a,b))
                    tmp[e] = tmp.get(e,0) + c*d
            out = {e:c for e,c in tmp.items() if c}
        return out
    def sq(self, p: dict) -> dict:
        return self.mul(p,p)


def base_expr(name: str) -> str:
    if name.startswith('gprod'):
        return prod([f'(g {i})' for i in ast.literal_eval(name[5:])])
    if name in ('Adet','Bdet'): return f'(det{name[0]} (outer g))'
    if (m := re.fullmatch(r'ratio\*g(\d+)g(\d+)',name)):
        return prod(['(ratio (outer g))', f'(g {int(m[1])-1})', f'(g {int(m[2])-1})'])
    if (m := re.fullmatch(r'([AB])minor(\d)(\d)\*g(\d+)',name)):
        c,i,j,k=m.groups()
        return f'(minor{c} (outer g) {i} {j} * g {int(k)-1})'
    m = re.fullmatch(r'([AB])quad(\([^)]*\))\*g(\d+)g(\d+)',name)
    if not m: raise ValueError(name)
    v=ast.literal_eval(m[2]); i,j=int(m[3])-1,int(m[4])-1
    return f'(quad{m[1]} (outer g) ![{",".join(map(str,v))}] * g {i} * g {j})'


def expression(name: str) -> str:
    if name.startswith('plain:'):
        exps=list(map(int,name[6:].split(',')))
        return prod([f'({f"g {i}" if i<9 else ("t" if i==9 else "z")}) ^ {k}'
                     for i,k in enumerate(exps) if k])
    if '*param' in name:
        b,p=name.rsplit('*param',1)
        return prod([base_expr(b), *[['t','z','(t+z-18)'][i] for i in ast.literal_eval(p)]])
    if (m := re.fullmatch(r'mixedSquare\*g(\d+)\*(1|t|z|w)',name)):
        return f'((mix g t z)^2 * g {int(m[1])-1} * '+{'1':'1','t':'t','z':'z','w':'(t+z-18)'}[m[2]]+')'
    if (m := re.fullmatch(r'scoreSquare(-?\d+),(-?\d+)\*g(\d+)\*(1|t|z|w)',name)):
        return f'((({m[1]} : ℝ)*score g t z + ({m[2]} : ℝ)*mix g t z)^2 * g {int(m[3])-1} * '+{'1':'1','t':'t','z':'z','w':'(t+z-18)'}[m[4]]+')'
    return base_expr(name)


def certificate_context(root: Path, inputs: Path, dimension: int, uniform: bool, block_size: int) -> dict:
    D=dimension; name='Uniform' if uniform else f'Finite{D}'
    filename = 'qutrit_uniform_parameter_search.json' if uniform else ('qutrit_cubic_certificate_search.json' if D==9 else f'qutrit_D{D}_cubic_certificate.json' if D==12 else f'qutrit_D{D}_fast_certificate.json')
    source=inputs/filename
    data=json.loads(source.read_text())
    if not data['exact_certificate']: raise ValueError('Uncertified input marker')
    terms=data['terms']; fractions=[Fraction(e['coefficient']) for e in terms]
    if not all(c>0 for c in fractions): raise ValueError('Nonpositive coefficient')
    Q=math.lcm(*(c.denominator for c in fractions))
    weights=[c.numerator*(Q//c.denominator) for c in fractions]
    a=Algebra(11 if uniform else D); g=[a.v(i) for i in range(D)]
    y=[a.add(*g[i:]) for i in range(D)]; idx=list(range(3))+list(range(D-6,D)); o=[y[i] for i in idx]
    A=[[a.scale(2,o[8]),a.sub(o[7],o[0]),a.sub(o[5],o[1])],
       [a.sub(o[7],o[0]),a.scale(2,o[6]),a.sub(o[4],o[2])],
       [a.sub(o[5],o[1]),a.sub(o[4],o[2]),a.scale(2,o[3])]]
    B=[[a.scale(2,o[8]),a.sub(o[7],o[0]),a.sub(o[6],o[1])],
       [a.sub(o[7],o[0]),a.scale(2,o[5]),a.sub(o[4],o[2])],
       [a.sub(o[6],o[1]),a.sub(o[4],o[2]),a.scale(2,o[3])]]
    T=a.add(*y); S=a.add(*(a.sq(v) for v in y))
    if uniform:
        t,z=a.v(9),a.v(10);w=a.add(t,z,a.c(-18))
        T=a.add(T,a.mul(t,o[2]),a.mul(z,o[3]))
        S=a.add(S,a.mul(t,a.sq(o[2])),a.mul(z,a.sq(o[3])))
        dim=a.add(a.c(9),t,z)
        mix=a.sub(a.mul(t,o[2]),a.mul(z,o[3]))
        score=a.sub(a.scale(9,T),a.scale(4,a.mul(dim,a.add(o[2],o[3]))))
        target=a.mul(a.sub(a.scale(9,a.sq(T)),a.scale(8,a.mul(dim,S))),T)
    else:
        target=a.mul(a.sub(a.scale(D+8,a.sq(T)),a.scale((D+2)**2,S)),T)
    cache={}
    def base(name):
        if name in cache:return cache[name]
        if name.startswith('gprod'):
            p=a.mul(*(g[i] for i in ast.literal_eval(name[5:])))
        elif (m:=re.fullmatch(r'ratio\*g(\d+)g(\d+)',name)):
            p=a.mul(a.sub(a.scale(2,o[3]),o[2]),g[int(m[1])-1],g[int(m[2])-1])
        else:
            M={'A':A,'B':B}[name[0]];tail=name[1:]
            if tail=='det':
                p=a.add(a.mul(M[0][0],M[1][1],M[2][2]),a.mul(M[0][1],M[1][2],M[2][0]),a.mul(M[0][2],M[1][0],M[2][1]),
                  a.scale(-1,a.mul(M[0][2],M[1][1],M[2][0])),a.scale(-1,a.mul(M[0][1],M[1][0],M[2][2])),a.scale(-1,a.mul(M[0][0],M[1][2],M[2][1])))
            elif (m:=re.fullmatch(r'minor(\d)(\d)\*g(\d+)',tail)):
                i,j,k=map(int,m.groups());p=a.mul(a.sub(a.mul(M[i][i],M[j][j]),a.mul(M[i][j],M[j][i])),g[k-1])
            else:
                m=re.fullmatch(r'quad(\([^)]*\))\*g(\d+)g(\d+)',tail)
                if not m:raise ValueError(name)
                v=ast.literal_eval(m[1]);q=a.add(*(a.scale(v[i]*v[j],M[i][j]) for i in range(3) for j in range(3)))
                p=a.mul(q,g[int(m[2])-1],g[int(m[3])-1])
        cache[name]=p;return p
    def polynomial(name):
        if name.startswith('plain:'):return {tuple(map(int,name[6:].split(','))):1}
        if '*param' in name:
            b,p=name.rsplit('*param',1);return a.mul(base(b),*([t,z,w][i] for i in ast.literal_eval(p)))
        if (m:=re.fullmatch(r'mixedSquare\*g(\d+)\*(1|t|z|w)',name)):
            return a.mul(a.sq(mix),g[int(m[1])-1],{'1':a.c(1),'t':t,'z':z,'w':w}[m[2]])
        if (m:=re.fullmatch(r'scoreSquare(-?\d+),(-?\d+)\*g(\d+)\*(1|t|z|w)',name)):
            x=a.add(a.scale(int(m[1]),score),a.scale(int(m[2]),mix))
            return a.mul(a.sq(x),g[int(m[3])-1],{'1':a.c(1),'t':t,'z':z,'w':w}[m[4]])
        return base(name)
    polys=[a.scale(c,polynomial(e['name'])) for c,e in zip(weights,terms)]
    if a.add(*polys)!=a.scale(Q,target):raise ValueError('EXACT IDENTITY FAILURE')
    return locals()
