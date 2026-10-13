#!/usr/bin/env python3
"""Exact actual-state/Born-law checks; finite support, not an all-prime proof."""
from fractions import Fraction
from math import isqrt
from pathlib import Path
import hashlib, json

def require(ok, message):
    if not ok: raise ValueError(message)

def prime(p):
    return p>=2 and all(p%d for d in range(2,isqrt(p)+1))

def rank(a):
    a=[[Fraction(x) for x in row] for row in a]
    r=0
    for j in range(len(a[0])):
        pivot=next((i for i in range(r,len(a)) if a[i][j]),None)
        if pivot is None: continue
        a[r],a[pivot]=a[pivot],a[r]
        d=a[r][j]; a[r]=[x/d for x in a[r]]
        for i in range(len(a)):
            if i!=r and a[i][j]:
                d=a[i][j]; a[i]=[x-d*y for x,y in zip(a[i],a[r])]
        r+=1
    return r

def multiply(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]

def transpose(a): return [list(row) for row in zip(*a)]

def reduce_cyclotomic(coeff):
    return tuple(x-coeff[-1] for x in coeff[:-1])

def absolute_square(coeff):
    p=len(coeff)
    out=[0]*p
    for x,c in enumerate(coeff):
        if c:
            for y,d in enumerate(coeff):
                if d: out[(x-y)%p]+=c*d
    reduced=reduce_cyclotomic(out)
    require(all(x==0 for x in reduced[1:]),'Born probability is not the claimed rational')
    return reduced[0]

def factors(n):
    out={}; d=2
    while d*d<=n:
        while n%d==0: out[d]=out.get(d,0)+1; n//=d
        d+=1
    if n>1: out[n]=out.get(n,0)+1
    return out

def add_log(out,weight,q):
    require(q>0,'Log argument must be positive')
    for sign,n in [(1,q.numerator),(-1,q.denominator)]:
        for p,e in factors(n).items(): out[p]=out.get(p,Fraction(0))+sign*weight*e

def log_form(q,weight=Fraction(1)):
    out={}; add_log(out,weight,Fraction(q)); return {p:c for p,c in out.items() if c}

def mutual_information(table):
    rows=list(map(sum,table)); cols=list(map(sum,zip(*table))); out={}
    require(sum(rows)==1,'Joint probability does not sum to one')
    for j,row in enumerate(table):
        for k,v in enumerate(row):
            if v: add_log(out,v,v/(rows[j]*cols[k]))
    return {p:c for p,c in out.items() if c}

def base_state(p,s=None):
    require(prime(p) and p%2==1,'Require an odd prime')
    if p==3:
        return [[0,1,1],[-1,0,0],[-1,0,0]],4
    require(s is not None and s*s%p==p-1,'Require the actual square root of -1')
    return [[int(y==s*x%p)+int(y==(-s*x)%p) for y in range(p)] for x in range(p)],2*(p+1)

def check_state(p,s,displacements=(0,0,0,0), bob_conjugated=False):
    k,norm=base_state(p,s)
    r=(p+1)//2
    require(sum(x*x for row in k for x in row)==norm,'State normalization failed')
    require(rank(k)==r,'Actual Schmidt rank differs')
    gram=multiply(k,transpose(k)); bob=multiply(transpose(k),k)
    expected=[[Fraction(int(x==y)+int(y==(-x)%p),p+1) for y in range(p)] for x in range(p)]
    require([[Fraction(x,norm) for x in row] for row in gram]==expected,'Alice partial trace failed')
    require([[Fraction(x,norm) for x in row] for row in bob]==expected,'Bob partial trace failed')
    require(multiply(expected,expected)==[[x/r for x in row] for row in expected],
            'Actual marginal does not have the claimed flat nonzero spectrum')
    require(sum(expected[i][i] for i in range(p))==1,'Marginal trace failed')
    u,v,ub,vb=displacements
    inv2=pow(2,-1,p)
    support=[]
    for x,row in enumerate(k):
        for y,c in enumerate(row):
            if c:
                xx=(x+u)%p; yy=(y+ub)%p
                phase=(v*(x+u*inv2)+vb*(y+ub*inv2))%p
                support.append((xx,yy,c,phase))
    computational=[[Fraction(k[(j-u)%p][(l-ub)%p]**2,norm) for l in range(p)] for j in range(p)]
    require(mutual_information(computational)==log_form(r),'Computational mutual information failed')
    checked=p*p
    for a in range(p):
        table=[]
        for j in range(p):
            row=[]
            for l in range(p):
                coeff=[0]*p
                for x,y,c,phase in support:
                    bob_sign=1 if bob_conjugated else -1
                    exponent=(phase-a*x*x-j*x+bob_sign*(a*y*y+l*y))%p
                    coeff[exponent]+=c
                value=Fraction(absolute_square(coeff),p*p*norm)
                jj=(j+2*a*u-v)%p; ll=(l+2*a*ub-vb)%p
                require(value==Fraction(k[jj][ll]**2,norm),'Actual finite-basis Born law failed')
                row.append(value); checked+=1
            table.append(row)
        require(mutual_information(table)==log_form(r),'Actual finite-setting mutual information failed')
    return {'prime':p,'schmidt_rank':r,'root':s,'displacements':displacements,
            'actual_born_entries':checked,'setting_count':p+1,
            'Q_log_coefficients':{str(q):str(c) for q,c in log_form(r,Fraction(2)).items()},
            'E_log_coefficients':{str(q):str(c) for q,c in log_form(r,Fraction(p)).items()}}

def main():
    checks=[]
    for p in [3,5,13,17,29]:
        roots=[None] if p==3 else [s for s in range(p) if s*s%p==p-1]
        for s in roots:
            for displacements in [(0,0,0,0),(1,0,0,0),(0,1,0,0),(0,0,1,1),(1,2,2,1)]:
                checks.append(check_state(p,s,displacements))
    rejected=[]
    for name,fn in [
        ('wrong_square_root',lambda:check_state(5,1)),
        ('Bob_conjugated_basis',lambda:check_state(5,2,bob_conjugated=True)),
        ('composite_dimension',lambda:check_state(9,2)),
    ]:
        try: fn()
        except ValueError: rejected.append(name)
        else: raise ValueError('Corrupted input accepted: '+name)
    report={'schema':1,'scope':'Finite actual-state certificates; arbitrary-prime classification is analytic.',
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'checks':checks,'rejected_controls':rejected,
            'total_actual_born_entries':sum(c['actual_born_entries'] for c in checks)}
    output=Path(__file__).with_name('actual-state-replay.json')
    output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','states':len(checks),'actual_born_entries':report['total_actual_born_entries'],
                      'rejected_controls':rejected}))

if __name__=='__main__': main()
