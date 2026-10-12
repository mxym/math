#!/usr/bin/env python3
"""Independent standard-library replay. Does not import submitted verifier code."""
import argparse, hashlib, json, math
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path

A=Q(87,2000); B=Q(11,2000); T=A+B
ROUND=2**110

def check(t,m):
    if not t: raise ArithmeticError(m)

def interval(x): return x if type(x) is tuple else (Q(x),Q(x))
def add(x,y):
    x,y=interval(x),interval(y);return x[0]+y[0],x[1]+y[1]
def neg(x): x=interval(x);return -x[1],-x[0]
def sub(x,y): return add(x,neg(y))
def mul(x,y):
    x,y=interval(x),interval(y)
    p=[a*b for a in x for b in y];return min(p),max(p)
def div(x,y):
    y=interval(y);check(y[0]>0 or y[1]<0,'denominator includes zero')
    return mul(x,(1/y[1],1/y[0]))
def pw(x,k):
    x=interval(x);check(type(k) is int and k>=0,'bad exponent')
    if k==0: return interval(1)
    if k%2: return x[0]**k,x[1]**k
    vals=[x[0]**k,x[1]**k]
    return (Q(0) if x[0]<=0<=x[1] else min(vals)),max(vals)
def round_out(v):
    l,h=v;return Q(l.numerator*ROUND//l.denominator,ROUND),Q(-((-h.numerator*ROUND)//h.denominator),ROUND)

def shortlog(y):
    check(Q(1)<=y<=Q(2),'log range')
    w=(y-1)/(y+1);q=w*w;p=w;lo=Q(0)
    # Different order and term count from both submitted implementations.
    for odd in range(1,49,2): lo+=p/odd;p*=q
    return 2*lo,2*lo+2*p/(49*(1-q))
L2=shortlog(Q(2))
@lru_cache(None)
def log(x):
    x=Q(x);check(x>0,'log positive');k=0
    while x<1: x*=2;k-=1
    while x>=2: x/=2;k+=1
    return round_out(add(shortlog(x),mul(k,L2)))
@lru_cache(None)
def logg(m):
    # Integer factorial is formed independently, not a sum of cached integer logs.
    return sub(mul(m,log(Q(m))),log(Q(math.factorial(m))))

def scalar_bound(g,m,L,U):
    check(m>0 and L<=0<=U,'strong concavity or point membership')
    candidates=[]
    # Maximize both endpoint-gradient quadratics on the ENTIRE displacement
    # interval. This is equivalent to, but not the submitted sign-split code.
    for e in g:
        loc=min(U,max(L,e/(2*A*m)))
        candidates.extend([e*L-A*m*L*L,e*U-A*m*U*U,e*loc-A*m*loc*loc])
    return max(candidates)

def finite(data):
    check(data['alpha']==[87,2000] and data['beta']==[11,2000] and data['T']==[49,1000],'finite constants')
    check(data['dimension_max']==199 and data['denominator']==10**9,'finite metadata')
    rows=data['points'];check(len(rows)==19900,'finite row count')
    idx=0;worst=None;digest=hashlib.sha256()
    for r in range(1,200):
        for s in range(r,200):
            row=rows[idx];check(type(row) is list and len(row)==4 and all(type(v) is int for v in row),'finite row types')
            check(row[:2]==[r,s],'finite exact coverage')
            h,j=Q(row[2],data['denominator']),Q(row[3],data['denominator'])
            check(2<=h<=r+1 and 2<=j<=s+1,'finite point box')
            n=r+s;x=(s*h+r*j)/n;v=r*h+s*j
            c4=Q(1,(r+1)**3)-Q(r,n*(n+1)**3)
            d4=Q(1,(s+1)**3)-Q(s,n*(n+1)**3)
            q2=h*h/(r+1)+j*j/(s+1)-v*v/(n*n*(n+1))
            q4=c4*h**4+d4*j**4
            gh=Q(s,n)/x-A*(2*h/(r+1)-2*r*v/(n*n*(n+1)))-4*B*c4*h**3
            gj=Q(r,n)/x-A*(2*j/(s+1)-2*s*v/(n*n*(n+1)))-4*B*d4*j**3
            # Enumerate all 4 corner values instead of submitted sign selection.
            sup=max(gh*(e-h)+gj*(f-j) for e in (Q(2),Q(r+1)) for f in (Q(2),Q(s+1)))
            logc=sub(add(logg(r),logg(s)),logg(n))
            ub=add(logc,log(x))[1]-A*q2-B*q4+T+sup
            check(ub<Q(-3,2000),f'finite tangent {r},{s}')
            if worst is None or ub>worst[0]:worst=(ub,row)
            digest.update(f'{r},{s}:{ub}\n'.encode());idx+=1
    return dict(rectangles=idx,uniform_upper='-3/2000',worst_upper=str(worst[0]),worst_row=worst[1],bounds_sha256=digest.hexdigest())

def tail(data):
    check(data['alpha']==str(A) and data['beta']==str(B) and data['cutoff']==200 and data['point_denominator']==10**8,'tail metadata')
    rows=data['cells'];check(len(rows)==15568,'tail count')
    coverage={r:[] for r in range(1,200)};hist=Counter();worst=None;digest=hashlib.sha256();min_curves=[None,None];min_logarg=None
    for row in rows:
        check(type(row) is list and len(row)==5 and all(type(v) is int for v in row),'tail row types')
        r,i,d,hn,un=row
        check(r in coverage and 0<=d<=7 and 0<=i<2**d,'dyadic coordinates')
        L=Q(i,200*2**d);U=Q(i+1,200*2**d);z=(L,U);h=Q(hn,10**8);u=Q(un,10**8)
        check(2<=h<=r+1 and 0<=u<=1,'tail point box')
        coverage[r].append((L,U));hist[d]+=1
        p2=mul(pw(add(1,mul(r,z)),2),add(1,mul(r+1,z)))
        p4=mul(add(1,mul(r,z)),pw(add(1,mul(r+1,z)),3))
        s2=add(add(3,mul(3*r+2,z)),mul(r*(r+1),pw(z,2)))
        s4=add(add(add(4,mul(6*r+9,z)),mul(4*r*r+9*r+6,pw(z,2))),mul((r+1)**3,pw(z,3)))
        a=sub(Q(1,r+1),div(mul(r*r,pw(z,3)),p2))
        b=neg(div(mul(mul(2*r,z),add(1,z)),p2))
        c=div(mul(mul(r,add(1,z)),s2),p2)
        a4=sub(Q(1,(r+1)**3),div(mul(r,pw(z,4)),p4))
        d4=div(mul(mul(r,add(1,z)),s4),p4)
        check(a[0]>0 and a4[0]>0 and d4[0]>0,'potential coefficient')
        mh=a[0]/2;mu=c[0]-max(abs(b[0]),abs(b[1]))**2/(2*a[0])
        check(mh>0 and mu>0,'positive curvature')
        for k,val in enumerate((mh,mu)):
            if min_curves[k] is None or val<min_curves[k]: min_curves[k]=val
        arg=add(h,mul(mul(r,add(1,z)),u));arg2=add(1,mul(r,z))
        check(arg[0]>0 and arg2[0]>0,'log interval positivity')
        if min_logarg is None or arg[0]<min_logarg:min_logarg=arg[0]
        q2=add(add(mul(a,h*h),mul(b,h*u)),mul(c,u*u))
        q4=add(mul(a4,h**4),mul(d4,u**4))
        val=logg(r)[1]-r+log(arg[1])[1]-log(arg2[0])[0]/2-A*q2[0]-B*q4[0]+T
        gh=sub(sub(div(1,arg),mul(A,add(mul(2*h,a),mul(u,b)))),mul(4*B*h**3,a4))
        gu=sub(sub(div(mul(r,add(1,z)),arg),mul(A,add(mul(h,b),mul(2*u,c)))),mul(4*B*u**3,d4))
        ub=val+scalar_bound(gh,mh,Q(2)-h,Q(r+1)-h)+scalar_bound(gu,mu,-u,Q(1)-u)
        check(ub<Q(-1,10**8),f'tail failure {row}')
        if worst is None or ub>worst[0]:worst=(ub,row)
        digest.update(f'{row}:{ub}\n'.encode())
    cover_counts={}
    for r,cells in coverage.items():
        cursor=Q(0)
        for lo,hi in sorted(cells):
            check(lo==cursor and hi>lo,f'coverage gap/overlap {r}')
            cursor=hi
        check(cursor==Q(1,200),'coverage right endpoint');cover_counts[str(r)]=len(cells)
    return dict(cells=len(rows),dimensions=len(coverage),closed_z_interval=['0','1/200'],depth_histogram=dict(sorted(hist.items())),maximum_depth=max(hist),worst_upper=str(worst[0]),worst_row=worst[1],uniform_upper='-1/100000000',minimum_curvatures=[str(v) for v in min_curves],minimum_log_argument=str(min_logarg),cell_counts_by_dimension=cover_counts,bounds_sha256=digest.hexdigest())

def elementary():
    pi_lo=16*(Q(1,5)-Q(1,3*5**3)+Q(1,5*5**5)-Q(1,7*5**7))-Q(4,239)
    check(pi_lo>Q(157,50),'pi bound')
    c=Q(1615,7536);small=sum((Q(451,500)**m/math.factorial(m) for m in range(11)),Q(0))*2*A
    check(small>c,'large dimension comparison')
    x=Q(1049,1000);upper=sum((x**m/math.factorial(m) for m in range(13)),Q(0))+x**13/Q(math.factorial(13))/(1-x/14)
    check(upper<Q(571,200),'endpoint')
    gap=Q(11,85)*Q(2*(189-128),189+128)-T;check(gap>0,'improvement')
    return dict(pi_lower=str(pi_lo),large_dimension_taylor_gap=str(small-c),exp_upper=str(upper),exp_endpoint_gap=str(Q(571,200)-upper),old_alpha_minus_T_lower=str(gap))

def main():
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--report',type=Path,required=True);args=p.parse_args()
    out={'schema':1,'claim':'Independent exact replay of finite and infinite-tail certificates','proof_arithmetic':'fractions.Fraction only; no supplied checker imports; 24-term logs; outward denominator 2^110'}
    out['finite']=finite(json.loads((args.source/'mixed_finite_points.json').read_text()));print('PASS independent finite 19900',flush=True)
    out['tail']=tail(json.loads((args.source/'mixed_tail_certificate.json').read_text()));print('PASS independent tail 15568',flush=True)
    out['elementary']=elementary();out['certificate_sha256']={n:hashlib.sha256((args.source/n).read_bytes()).hexdigest() for n in ['mixed_finite_points.json','mixed_tail_certificate.json']}
    args.report.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print('PASS independent exact elementary constants',flush=True)
if __name__=='__main__':main()
