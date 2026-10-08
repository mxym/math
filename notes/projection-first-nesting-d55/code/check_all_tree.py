#!/usr/bin/env python3
"""Exact independent extension checker, full arbitrary product/join trees, d=49..55.

Requires the pinned and independently replayable source frontier d<=48.
No producer imports, floating arithmetic, or assert-dependent decisions.
"""
import bisect
import hashlib
import json
import sys
from fractions import Fraction as F
from functools import lru_cache
from math import factorial
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
BASE=ROOT.parent/'exact-product-join-finite-optima'/'certificates'/'frontiers48.json'
EXT=ROOT/'certificates'/'all_tree49to55.json'


def require(condition, message):
    if not condition:
        raise RuntimeError('all-tree extension: '+message)


@lru_cache(maxsize=None)
def g(n):
    require(isinstance(n,int) and n>0,'factorial argument')
    return F(n**n,factorial(n))


def rational(x):
    require(isinstance(x,str),'rational string expected')
    z=F(x)
    require(z>0 and str(z)==x,'invalid or noncanonical positive rational')
    return z


def block_shape(states,d,index):
    """Return a tuple of the join atoms of an explicit saved witness.

    The only permitted atom types are point and product of two simplices.
    A nested product gets a distinct flag, even if one factor is a join.
    """
    op=states[d][index][2]
    if op==['point']:
        require(d==0,'point only in formal dimension zero')
        return (('point',),)
    kind,r,a,s,b=op
    if kind=='join':
        return block_shape(states,r,a)+block_shape(states,s,b)
    def simplex(n,i):
        # Joins of points = simplices; there can be none other.
        expr=states[n][i][2]
        if expr==['point']:
            return n==0
        if expr[0]!='join':return False
        _,rr,aa,ss,bb=expr
        return simplex(rr,aa) and simplex(ss,bb)
    if simplex(r,a) and simplex(s,b):
        return (('block',r,s),)
    return (('nested',r,s),)


def check(path=None, quiet=False):
    new_file=Path(path or EXT)
    new=json.loads(new_file.read_text())
    require(hashlib.sha256(BASE.read_bytes()).hexdigest()==new.get('base_sha256'),
            'the audited 48D parent is not the pinned source')
    old=json.loads(BASE.read_text())
    require(old['max_dimension']==48 and len(old['states'])==49,
            'unexpected parent certificate dimension')
    require(new.get('first_dimension')==49 and new.get('last_dimension')==55 and
            len(new.get('frontiers',[]))==7 and len(new.get('summary',[]))==7,
            'incomplete 49..55 extension')
    states=[[(rational(st['H']),rational(st['Q']),st['op']) for st in row]
            for row in old['states']]
    total=0
    exacts={}
    for n in range(49,56):
        src=new['frontiers'][n-49]
        require(isinstance(src,list) and src,'empty extended dimension')
        front=[]
        for data in src:
            require(isinstance(data,dict) and set(data)=={'H','Q','op'},'malformed state fields')
            h,q=rational(data['H']),rational(data['Q'])
            op=data['op']
            require(isinstance(op,list) and len(op)==5,'malformed operation')
            tag,r,i,s,j=op
            require(tag in ['product','join'] and all(isinstance(v,int) and not isinstance(v,bool)
                for v in [r,i,s,j]), 'nonbinary operation or bad type')
            require(0<=r<=s<n and r+s+(1 if tag=='join' else 0)==n,
                    f'wrong dimension split at n={n}')
            if tag=='product': require(r>0,'neutral product included')
            require(0<=i<len(states[r]) and 0<=j<len(states[s]), 'invalid parent index')
            ha,qa=states[r][i][:2];hb,qb=states[s][j][:2]
            if tag=='join':
                HH=ha+hb;QQ=qa*qb
            else:
                HH=F(n)*ha*hb/(r*hb+s*ha)
                QQ=qa*qb*g(r)*g(s)/g(n)*F(s*ha+r*hb,n)
            require((h,q)==(HH,QQ), f'unattainable state n={n}')
            require(2<=h<=n+1,'state invariant range')
            front.append((h,q,op))
        require(all(front[i][0]>front[i+1][0] and front[i][1]<front[i+1][1]
                    for i in range(len(front)-1)), f'not an antichain in n={n}')
        neg=[-h for h,_,_ in front];qs=[q for _,q,_ in front]
        def covered(h,q):
            ix=bisect.bisect_right(neg,-h)-1
            return ix>=0 and qs[ix]>=q
        # Independently regenerate EVERY binary join split and verify it is
        # dominated by an actually attained state, without enumerating all
        # unpruned expression trees.
        for r in range(n):
            s=n-1-r
            if r>s:break
            for ha,qa,_ in states[r]:
                for hb,qb,_ in states[s]:
                    require(covered(ha+hb,qa*qb),f'uncovered join n={n},r={r},s={s}')
                    total+=1
        for r in range(1,n):
            s=n-r
            if r>s:break
            C=g(r)*g(s)/g(n)
            for ha,qa,_ in states[r]:
                for hb,qb,_ in states[s]:
                    h=F(n)*ha*hb/(r*hb+s*ha)
                    q=qa*qb*C*F(s*ha+r*hb,n)
                    require(covered(h,q),f'uncovered product n={n},r={r},s={s}')
                    total+=1
        states.append(front)
        claimed=new['summary'][n-49]
        require(set(claimed)=={'dimension','frontier_size','best_index','exact_ratio'},
                'wrong summary schema')
        require(claimed['dimension']==n and claimed['frontier_size']==len(front),
                'incorrect reported front size')
        k=claimed['best_index']
        require(isinstance(k,int) and not isinstance(k,bool) and 0<=k<len(front),
                'incorrect winning index')
        v=[h*q/F(n+1) for h,q,_ in front]
        best=max(v)
        require(v[k]==best and rational(claimed['exact_ratio'])==best,
                f'false reported maximum in dimension {n}')
        exacts[n]=best
        # Important: all six dimensions 49..54 still admit a join of
        # two-simplex product blocks (including optional point factors).
        if n<=54:
            expr=block_shape(states,n,k)
            require(all(z[0]!='nested' for z in expr),
                    f'failed to exhibit a two-layer optimizer in n={n}')
    # Independently reconstruct the explicit dimension-55 nested witness.
    q4=F(175,128);q5=F(189,128)
    H_nested=F(24)/(F(7,8)+F(17,10))
    Q_nested=q4*q4*g(7)*g(17)/g(24)*F(17*8+7*10,24)
    H_full=F(5+6+6)+H_nested
    Q_full=q4*q5*q5*Q_nested
    R_full=H_full*Q_full/F(56)
    require(H_nested==F(960,103) and H_full==F(2711,103),'nested H mismatch')
    require(R_full==F(333068659627091928809841719168016922609375,
                     83816757831946947640666468303298107539456),
            'independently reconstructed exact nested fraction wrong')
    require(exacts[55]==R_full,'nested witness does not attain sharp full-tree d55 maximum')
    # Full independent replay of the separate two-layer operation grammar.
    # The checker's Q,H formulas are evaluated from simplex factorials,
    # not from the full-class Pareto producer.
    from check_two_layer import check as check_B
    exact_two_layer=check_B(quiet=True)
    for d in range(49,55):
        require(exacts[d]==exact_two_layer[d],
                f'two-layer witness not optimal in the full class at d={d}')
    require(exacts[55]>exact_two_layer[55],
            'no strict first nesting separation at dimension 55')
    if not quiet:
        print('PASS: independently certified unrestricted product/join tree optima through dimension 55')
        print('pinned exact 48D base SHA256 =',new['base_sha256'])
        print('new 49..55 frontier states =',sum(len(row) for row in new['frontiers']))
        print('new exact binary candidate comparisons =',total)
        print('dimensions 49..54: exact unrestricted optimum = exact two-layer optimum')
        print('sharp two-layer d55 ratio =', exact_two_layer[55])
        print('first strict nesting dimension = 55')
        print('sharp C55 ratio =',R_full)
        print('sharp C55 nested witness = B(4,4) * B(5,5)^(*2) * (T7 x (B(4,4) * B(4,4)))')
        print('all decisions use exact Fraction arithmetic and explicit exceptions')
    return exacts


if __name__=='__main__':
    check(sys.argv[1] if len(sys.argv)>1 else None)
