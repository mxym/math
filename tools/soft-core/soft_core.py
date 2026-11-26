#!/usr/bin/env python3
"""Certify a sampling/cleanup budget or extract a bounded-support subproblem."""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from math import comb
import json
from pathlib import Path

def parse(d):
    groups=defaultdict(lambda:defaultdict(F))
    p,e=F(str(d['p'])),F(str(d['epsilon']))
    m=d['m']
    if type(m) is not int or m<1 or not (0<p<=1 and 0<e<1):
        raise ValueError('require integer m>=1, 0<p<=1, 0<epsilon<1')
    for a,b,x in d['buckets']:
        if not isinstance(a,str) or not isinstance(b,str) or type(x) not in (int,str):
            raise ValueError('bucket must be [owner string, color string, positive rational]')
        w=F(x)
        if w<=0:
            raise ValueError('bucket weight must be positive')
        groups[a][b]+=w
    rows={a:sorted(g.items(),key=lambda bw:(-bw[1],bw[0])) for a,g in sorted(groups.items())}
    if not rows:raise ValueError('at least one bucket is required')
    return p,e,m,rows

def weighted_mass(rows):
    return sum(w for row in rows.values() for _,w in row)

def head_tail_plan(d):
    p,e,m,rows=parse(d)
    E=weighted_mass(rows)
    r=F(2*m)/(p*e)
    K=(r.numerator+r.denominator-1)//r.denominator
    H=sum(w for row in rows.values() for _,w in row[:K])
    result={"K":K,"total_mass":str(E),"head_mass":str(H),"head_threshold":str(e*E/2)}
    if H>e*E/2:
        out=[[a,b,str(w)] for a,row in rows.items() for b,w in row[:K]]
        result.update(branch="restrict",kept_buckets=out,kept_mass=str(H),
                      owner_support_upper_bound=K)
    else:
        U=p*H+F(m,K)*E
        assert U<=e*p*E
        result.update(branch="sample",expected_adaptive_charge_upper=str(U),loss_budget=str(e*p*E))
    return result

def expected_survivors(rows, probs, m):
    out=F(0)
    for row in rows.values():
        if len(row)<m:
            continue
        # Conditional on one color being present, at least m-1 other colors are needed.
        for c,w in row:
            if not probs[c]:continue
            dist=[F(1)]+[F(0)]*(m-1)
            for other,_ in row:
                if other==c:continue
                q=probs[other]
                # State m-1 is an absorbing upper tail.
                old=dist
                dist=old.copy()
                for k in range(m-1):
                    dist[k]-=old[k]*q
                    dist[k+1]+=old[k]*q
            out+=w*probs[c]*dist[-1]
    return out

def tail(U,k,u,t):
    """P[>=t successes] sampling k of U colors, of which u belong to a row."""
    if t<=0:return F(1)
    if t>min(k,u):return F(0)
    start=max(t,k-(U-u))
    return F(sum(comb(u,j)*comb(U-u,k-j) for j in range(start,min(k,u)+1)),comb(U,k))

def expected_fixed(rows,chosen,remaining,k,m):
    U=len(remaining)
    out=F(0)
    for row in rows.values():
        present=[w for c,w in row if c in chosen]
        unknown=[w for c,w in row if c in remaining]
        need=m-len(present)
        out+=sum(present)*tail(U,k,len(unknown),need)
        if k and unknown:
            out+=sum(unknown)*F(k,U)*tail(U-1,k-1,len(unknown)-1,need-1)
    return out

def materialize(d):
    plan=head_tail_plan(d)
    if plan['branch']=='restrict':return plan
    p,e,m,rows=parse(d)
    colors=sorted({b for row in rows.values() for b,_ in row})
    size=p*len(colors)
    if size.denominator!=1:
        raise ValueError('exact fixed-size materializer requires p times number of colors to be an integer; plan needs no such restriction')
    if len(colors)>120 or sum(len(x) for x in rows.values())*len(colors)>100_000:
        raise ValueError('exact materializer size limit; use plan for the general certificate')
    chosen=set()
    remaining=set(colors)
    k=int(size)
    expectation=expected_fixed(rows,chosen,remaining,k,m)
    guarantee=(1-e)*p*weighted_mass(rows)
    assert expectation>=guarantee
    for c in colors:
        remaining.remove(c)
        if not k:continue
        chosen.add(c)
        if k<=len(remaining) and expected_fixed(rows,chosen,remaining,k-1,m)<expected_fixed(rows,chosen-{c},remaining,k,m):
            chosen.remove(c)
        else:k-=1
    assert not k and len(chosen)==size
    kept=[]
    for a,row in rows.items():
        sample=[(b,w) for b,w in row if b in chosen]
        if len(sample)>=m:
            kept.extend([a,b,str(w)] for b,w in sample)
    mass=sum(F(w) for _,_,w in kept)
    assert mass>=expectation
    return {**plan,"application":"fixed-size color sample, then discard owners with fewer than m active colors",
            "initial_expected_retained":str(expectation),"guaranteed_retained":str(guarantee),
            "selected_colors":sorted(chosen),"kept_mass":str(mass),"kept_buckets":kept}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=['plan','materialize','verify'])
    parser.add_argument('input',type=Path)
    parser.add_argument('certificate',type=Path,nargs='?')
    a=parser.parse_args()
    try:
        data=json.loads(a.input.read_text())
        if a.action=='verify':
            c=json.loads(a.certificate.read_text())
            expect=materialize(data) if 'application' in c else head_tail_plan(data)
            if c!=expect:raise ValueError('certificate differs from exact replay')
            result={"verified":True,"branch":c['branch']}
        else:
            result=materialize(data) if a.action=='materialize' else head_tail_plan(data)
        print(json.dumps(result,indent=2))
    except (ValueError,TypeError,KeyError,AttributeError,OSError) as e:
        parser.exit(2,'error: '+str(e)+'\n')

if __name__=='__main__':main()
