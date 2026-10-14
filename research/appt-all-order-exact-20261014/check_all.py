#!/usr/bin/env python3
"""Independent finite polytope descriptions and actual-state controls, no Lean."""
from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import argparse
import hashlib
import json


def require(value, message):
    if not value:
        raise RuntimeError(message)


def normalized(v):
    total=sum(v)
    return tuple(x/total for x in v)


def physical_h(v,m):
    R=m*(m-1)//2; K=m*(m+1)//2
    return sum(v[:R])-sum(v[-K:])


def original_vertices(m,D,p):
    """Original ordered-simplex gap coordinates, at most three positive weights."""
    K=m*(m+1)//2
    u=[tuple([F(1,j)]*j+[F(0)]*(D-j)) for j in range(1,D+1)]
    h=[physical_h(v,m) for v in u]
    cap=[v[0]-p*v[D-K] for v in u]
    found=set()
    for i in range(D):
        if h[i]<=0 and cap[i]<=0:
            found.add(u[i])
    for i,j in combinations(range(D),2):
        for a in (h,cap):
            if a[i]==a[j]:
                continue
            w=a[j]/(a[j]-a[i]); v=tuple(w*x+(1-w)*y for x,y in zip(u[i],u[j]))
            if 0<=w<=1 and physical_h(v,m)<=0 and v[0]-p*v[D-K]<=0:
                found.add(v)
    triples=0
    for i,j,k in combinations(range(D),3):
        weights=[h[j]*cap[k]-h[k]*cap[j],h[k]*cap[i]-h[i]*cap[k],h[i]*cap[j]-h[j]*cap[i]]
        total=sum(weights)
        if not total:
            continue
        weights=[x/total for x in weights]
        if min(weights)<=0:
            continue
        v=tuple(weights[0]*x+weights[1]*y+weights[2]*z for x,y,z in zip(u[i],u[j],u[k]))
        require(physical_h(v,m)==0 and v[0]-p*v[D-K]==0,'Original facet solve')
        found.add(v); triples+=1
    return found,triples


def projective_vertices(m,D,p):
    """Product of two independent ordered simplices, all factor edges."""
    K=m*(m+1)//2; R=m*(m-1)//2; N=D-K
    points={(i,s):tuple([p]*i+[F(1)]*(D-i-s)+[F(0)]*s)
            for i in range(N+1) for s in range(K)}
    values={key:physical_h(v,m) for key,v in points.items()}
    found={normalized(v) for key,v in points.items() if values[key]<=0}
    upper=lower=nonadjacent=0
    def edge(a,b,kind):
        nonlocal upper,lower,nonadjacent
        ha,hb=values[a],values[b]
        if ha*hb>=0:
            return
        w=hb/(hb-ha)
        v=tuple(w*x+(1-w)*y for x,y in zip(points[a],points[b]))
        require(physical_h(v,m)==0,'Projective cut equation')
        found.add(normalized(v))
        if kind=='upper':
            upper+=1
            i,j=a[0],b[0]
            if j-i>1: nonadjacent+=1
            if j>=R:
                r=v[i]
                expected=1+(m-a[1]-(p-1)*i)/(R-i)
                require(r==expected,'Independent r formula')
                if i or a[1]:
                    bound=F(R+m,R)-min(F(1,R),(p-F(R+m,R))/(R-1))
                    require(r<=bound,'Strict nonbulk ratio gap')
        else:
            lower+=1
            if b[1]-a[1]>1: nonadjacent+=1
    for s in range(K):
        for i,j in combinations(range(N+1),2): edge((i,s),(j,s),'upper')
    for i in range(N+1):
        for s,t in combinations(range(K),2): edge((i,s),(i,t),'lower')
    return found,{'upper_cuts':upper,'lower_cuts':lower,'nonadjacent_cuts':nonadjacent}


def dec(v):
    if isinstance(v,F): return Decimal(v.numerator)/Decimal(v.denominator)
    return Decimal(v)


def power(v,a):
    v=dec(v)
    return (a*v.ln()).exp() if v else Decimal(0)


def qmoment(q,D,k,a):
    theta=Decimal(k)/D
    return (1+theta*(power(q,a)-1))/power(1+theta*(q-1),a)


def winning(q,D,a):
    Q=power(q,a); t=q-1
    theta=(Q-1-a*t)/(t*(a-1)*(Q-1))
    k=int(Decimal(D)*theta)
    ranks=sorted({max(1,min(D-1,k)),max(1,min(D-1,k+1))})
    vals=[qmoment(q,D,j,a) for j in ranks]
    return max(vals),ranks


def pmoment(D,a):
    return power(Decimal(D)/(D+2),a)*(power(3,a)+D-1)/D


def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--out',type=Path)
    args=parser.parse_args()
    geometry=[]; vertices=identities=triples=nonadjacent=0; retained=[]
    for m,D in [(3,9),(3,12),(3,18),(3,30),(4,16),(4,20),(4,32),(5,25),(5,30),(6,36),(6,42)]:
        R=m*(m-1)//2; q=F(m+1,m-1); p=q+F(1,10*R)
        left,t=original_vertices(m,D,p); right,counts=projective_vertices(m,D,p)
        require(left==right,f'Two independent vertex descriptions differ m{m} D{D}')
        bulkmax=max(D*sum(x*x for x in v) for v in left)
        expected=max(F(D)*(k*q*q+D-k)/(D+k*(q-1))**2 for k in range(1,D))
        if bulkmax>expected:
            retained.append({'m':m,'D':D,'order':2,'outer_minus_bulk_exact':str(bulkmax-expected)})
        for v in left:
            require(sum(v)==1 and all(v[i]>=v[i+1] for i in range(D-1)) and min(v)>=0,'Trace/order')
            require(physical_h(v,m)<=0 and v[0]<=p*v[D-m*(m+1)//2],'Actual outer constraints')
            compressed=Counter(v)
            for exponent in (2,3,5):
                require(sum(x**exponent for x in v)==sum(n*x**exponent for x,n in compressed.items()),'Exact multiplicity identity')
                identities+=1
        geometry.append({'m':m,'D':D,'p':str(p),'vertices':len(left),'triple_support_vertices':t,**counts})
        vertices+=len(left); triples+=t; nonadjacent+=counts['nonadjacent_cuts']
    require(bool(retained),'Retain genuinely failed small-D relaxation controls')
    crossings=[]; actual_mixtures=0; nonflat_controls=0; small_rank_checks=0; finite_asymptotic_bracket_failures=[]
    with localcontext() as ctx:
        ctx.prec=260
        for m in (3,4,5,8,12):
            q=Decimal(m+1)/Decimal(m-1); t=q-1
            kap=1/(Decimal(3)/q).ln()
            for exponent in (4,8,12,18):
                D=m*m*10**exponent
                X=kap*(Decimal(D).ln()-Decimal(D).ln().ln()-(t*kap).ln()-1)
                lo=X-1; hi=X+1
                if winning(q,D,lo)[0]<=pmoment(D,lo) or winning(q,D,hi)[0]>=pmoment(D,hi):
                    finite_asymptotic_bracket_failures.append({'m':m,'D':D,'bracket':'X-1,X+1'})
                # Locate finite scalar crossings without treating an eventual asymptotic as a finite bound.
                width=Decimal(1)
                while winning(q,D,lo)[0]<=pmoment(D,lo):
                    width*=2; lo=max(Decimal('1.01'),X-width)
                    require(lo>Decimal('1.01'),'No scalar negative branch in selected finite case')
                width=Decimal(1)
                while winning(q,D,hi)[0]>=pmoment(D,hi):
                    width*=2; hi=X+width
                for unused in range(190):
                    mid=(lo+hi)/2
                    if winning(q,D,mid)[0]>pmoment(D,mid): lo=mid
                    else: hi=mid
                eta=(lo+hi)/2
                selected=winning(q,D,eta)[1]
                crossings.append({'m':m,'D':D,'eta':str(eta),'eta_minus_X':str(eta-X),'selected_ranks':selected})
                for a in (Decimal(2),X-1,X,X+1,eta):
                    Q,ranks=winning(q,D,a); P=pmoment(D,a); envelope=max(Q,P)
                    k=ranks[0]
                    for weight in (F(0),F(1,5),F(1,2),F(4,5),F(1)):
                        w=dec(weight); base=Decimal(1)/(D+t*k); polebase=Decimal(1)/(D+2)
                        levels=[(1,w*3*polebase+(1-w)*q*base),
                                (k-1,w*polebase+(1-w)*q*base),
                                (D-k,w*polebase+(1-w)*base)]
                        require(sum(dec(n)*x for n,x in levels).quantize(Decimal('1e-245'))==1,'Actual convex-mixture trace')
                        M=power(D,a-1)*sum(dec(n)*power(x,a) for n,x in levels)
                        require(M<=envelope*(1+Decimal('1e-220')),'Actual projection/pole mixture exceeds candidates')
                        actual_mixtures+=1
                    if m==3:
                        # Direct all-Schmidt sufficient kernel: diagonal2; gaps3/2,7/10,7/10.
                        det=F(8)-2*(F(3,2)**2+2*F(7,10)**2)-2*F(3,2)*F(7,10)**2
                        require(det==F(7,100) and min(4-F(3,2)**2,4-F(7,10)**2)>0,'Actual three-Schmidt PSD control')
                        c=Decimal(17)/10; j=max(2,min(D-2,int(Decimal(D)/(3*(a+1)))))
                        Z=Decimal(5)/2+j*c+D-j-1
                        M=power(D,a-1)*(power(Decimal(5)/2,a)+j*power(c,a)+D-j-1)/power(Z,a)
                        require(M<envelope,'Actual nonflat three-level control')
                        nonflat_controls+=1
                for k in range(1,m):
                    numerator=(D-k)*(F(2)-F(2,m-1)*k)
                    require(numerator>=0,'Exact small-rank majorization sign')
                    for a in (Decimal(2),X,eta+1):
                        require(pmoment(D,a)>qmoment(q,D,k,a),'Pole strictly majorizes small ranks')
                        small_rank_checks+=1
    record={'status':'PASS_FINITE_ORDINARY_DIAGNOSTICS','implementations':1,
            'precision_decimal_digits':260,'infinite_APPT_proof_certificate':False,
            'new_Lean_execution':False,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'independent_original_gap_vs_projective_geometry':{'cases':geometry,'vertices':vertices,
              'three_support_vertices':triples,'nonadjacent_edge_cuts':nonadjacent,'exact_power_identities':identities,
              'retained_small_dimension_outer_failures':retained},
            'crossings':crossings,'actual_convex_projection_pole_mixtures':actual_mixtures,
            'retained_finite_asymptotic_bracket_failures':finite_asymptotic_bracket_failures,
            'actual_nonflat_three_level_APPT_controls':nonflat_controls,'small_rank_majorization_controls':small_rank_checks}
    if args.out: args.out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in record.items() if k not in ('crossings','independent_original_gap_vs_projective_geometry')},indent=2))
    print(json.dumps({'finite_vertices':vertices,'three_support_vertices':triples,
                      'nonadjacent_edge_cuts':nonadjacent,'exact_power_identities':identities,
                      'retained_small_D_failures':len(retained),'scalar_crossings':len(crossings)}))


if __name__=='__main__':
    main()
