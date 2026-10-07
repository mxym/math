#!/usr/bin/env python3
"""Exact finite regressions for integrated determinant-witness selection.

The analytic all-law proof, including nonatomic laws, is in paper.tex.
This checker uses only the Python standard library and explicit exceptions.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import factorial
from pathlib import Path
import argparse
import json


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def det(matrix):
    rows=[list(map(F,row)) for row in matrix]
    value=F(1)
    for j in range(len(rows)):
        pivot=next((k for k in range(j,len(rows)) if rows[k][j]),None)
        if pivot is None:
            return F(0)
        if pivot!=j:
            rows[j],rows[pivot]=rows[pivot],rows[j]
            value=-value
        entry=rows[j][j]
        value*=entry
        for k in range(j+1,len(rows)):
            ratio=rows[k][j]/entry
            for column in range(j+1,len(rows)):
                rows[k][column]-=ratio*rows[j][column]
    return value


def psi(fy,fz):
    return min(max(fy,0),max(-fz,0))+min(max(-fy,0),max(fz,0))


def weight(indices,masses):
    result=F(1)
    for i in indices:
        result*=masses[i]
    return result


def norm2(vector):
    return sum(v*v for v in vector)


def simplex_law(d):
    points=[(-F(1,d),)*d]
    points += [tuple(F(i==j) for j in range(d)) for i in range(d)]
    masses=[F(1,2)]+[F(1,2*d)]*d
    return points,masses


def perturb(d,epsilon,y):
    points,masses=simplex_law(d)
    a0=(1-sum(y))/2
    alpha=[a0]+[y[i]+a0/d for i in range(d)]
    masses=[p-epsilon*a for p,a in zip(masses,alpha)]
    return points+[y],masses+[epsilon]


def check_law(name,points,masses,counters):
    d=len(points[0]); n=d+1; count=len(points)
    b=F(1,1000)
    require(sum(masses)==1 and min(masses)>0,'invalid probability: '+name)
    require(all(norm2(p)<=1 for p in points),'support outside ball: '+name)
    require(all(sum(m*p[j] for m,p in zip(masses,points))==0 for j in range(d)),
            'law not centered: '+name)
    covariance=[[sum(m*p[i]*p[j] for m,p in zip(masses,points)) for j in range(d)]
                for i in range(d)]
    shifted=[[covariance[i][j]-4*b*F(i==j) for j in range(d)] for i in range(d)]
    # Sylvester certifies Sigma>=4b I; |u.X| >= (u.X)^2 implies the
    # uniform directional half-moment >=2b used in the analytic theorem.
    require(all(det([row[:size] for row in shifted[:size]])>0 for size in range(1,d+1)),
            'directional spread certificate failed: '+name)

    @lru_cache(None)
    def lifted(indices):
        return det([points[i]+(F(1),) for i in indices])

    A=sum(weight(base,masses)*abs(det([points[i] for i in base]))
          for base in product(range(count),repeat=d))
    B=F(0); second_moment=F(0)
    for anchors in product(range(count),repeat=n):
        v=lifted(anchors)
        probability=weight(anchors,masses)
        B+=probability*abs(v)
        second_moment+=probability*v*v
    D=B-A
    require(D>=0,'negative cancellation defect')
    require(second_moment==factorial(n)*det(covariance),'affine covariance identity failed')
    cancellation=F(0); two_sample=F(0)
    for base in product(range(count),repeat=d):
        values=[lifted(base+(j,)) for j in range(count)]
        positive=sum(m*max(f,0) for m,f in zip(masses,values))
        negative=sum(m*max(-f,0) for m,f in zip(masses,values))
        cancellation+=weight(base,masses)*2*min(positive,negative)
        conditional=sum(masses[i]*masses[j]*psi(values[i],values[j])
                        for i in range(count) for j in range(count))
        require(conditional<=2*min(positive,negative),'conditional two-sample bound failed')
        two_sample+=weight(base,masses)*conditional
        counters['base_cancellation_checks']+=1
        counters['two_sample_values']+=count*count
    require(cancellation==D,'exact cancellation identity failed')
    require(two_sample<=D,'unconditional two-sample witness bound failed')

    v0=b**d; q0=b**(2*d)/4**d; L=F(2**d)/v0
    m=n*(n+1)//2; Q=n*(n+1)*8**d/b**(4*d)
    require(second_moment>=2*b**(2*d),'conditioned determinant moment bound failed')
    event_probability=F(0); total_H=F(0); best=None
    pairs=list(combinations(range(n),2))
    for anchors in product(range(count),repeat=n):
        signed_v=lifted(anchors); V=abs(signed_v)
        probability=weight(anchors,masses)
        H=F(0); Phi=F(0); assignment_bound=F(0); assigned=[F(0)]*n
        for x in range(count):
            first=[]; second=[]
            for i in range(n):
                base=anchors[:i]+anchors[i+1:]
                first.append(psi(lifted(base+(anchors[i],)),lifted(base+(x,))))
            for i,j in pairs:
                base=(x,)+tuple(anchors[k] for k in range(n) if k not in (i,j))
                second.append(psi(lifted(base+(anchors[i],)),lifted(base+(anchors[j],))))
            H+=masses[x]*(sum(first)+sum(second))
            if not signed_v:
                continue
            alpha=[]
            for i in range(n):
                replaced=anchors[:i]+(x,)+anchors[i+1:]
                alpha.append(lifted(replaced)/signed_v)
            require(sum(alpha)==1,'barycentric coefficients do not sum to one')
            require(all(sum(a*points[v][j] for a,v in zip(alpha,anchors))==points[x][j]
                        for j in range(d)),'barycentric reconstruction failed')
            negative=[max(-a,0) for a in alpha]
            positive=[max(a,0) for a in alpha]
            negative_witness=sum(min(1,a) for a in negative)
            positive_witness=sum(min(positive[i],positive[j]) for i,j in pairs)
            for i in range(n):
                require(first[i]==V*min(1,negative[i]),'first witness sign identity failed')
                counters['first_witness_identities']+=1
            for pair_value,(i,j) in zip(second,pairs):
                require(pair_value>=V*min(positive[i],positive[j]),'pair witness sign bound failed')
                counters['pair_witness_inequalities']+=1
            r=max(range(n),key=lambda i:positive[i])
            assigned[r]+=masses[x]
            Nx=sum(negative); Ux=sum(positive[i] for i in range(n) if i!=r)
            require(Ux<=positive_witness,'rounding positive remainder bound failed')
            bound=2*(Nx+Ux)
            difference=tuple(points[x][j]-points[anchors[r]][j] for j in range(d))
            require(norm2(difference)<=bound*bound,'Euclidean rounding bound failed')
            Phi+=masses[x]*(negative_witness+positive_witness)
            assignment_bound+=masses[x]*bound
        total_H+=probability*H
        counters['anchor_configurations']+=1
        if V>=v0:
            event_probability+=probability
            require(H>=V*Phi,'conditioned witness bound failed')
            require(assignment_bound<=2*L*Phi,'conditioned rounding inequality failed')
            candidate=(H,anchors,Phi,assignment_bound,assigned)
            if best is None or candidate[0]<best[0]:
                best=candidate
    require(total_H==m*two_sample,'independent reindexing of all witness terms failed')
    require(total_H<=m*D,'integrated H estimate failed')
    require(event_probability>=q0 and best is not None,'anchor event probability failed')
    H,anchors,Phi,assignment_bound,assigned=best
    require(H<=m*D/event_probability<=m*D/q0,'conditional anchor selection failed')
    require(assignment_bound<=Q*D,'linear assignment modulus failed')
    if D==0:
        require(assignment_bound==0,'zero defect assignment did not vanish')
    counters['laws']+=1
    return {'name':name,'d':d,'points':points,'masses':masses,'b':b,'A':A,'B':B,'D':D,
            'covariance':covariance,'affine_second_moment':second_moment,
            'cancellation':cancellation,'two_sample_witness_expectation':two_sample,
            'integrated_H_expectation':total_H,'anchor_event_probability':event_probability,
            'q0':q0,'selected_anchors':anchors,'selected_H':H,'selected_Phi':Phi,
            'selected_assignment_bound':assignment_bound,'Q':Q}


def main():
    laws=[]
    for d in (2,3):
        points,masses=simplex_law(d)
        laws.append(('simplex-'+str(d),points,masses))
        axes=[tuple(F(i==j) for j in range(d)) for i in range(d)]
        cross=axes+[tuple(-x for x in a) for a in axes]
        laws.append(('crosspolytope-'+str(d),cross,[F(1,2*d)]*(2*d)))
        for epsilon in (F(1,100),F(1,10)):
            y=(F(1,2),)+(F(0),)*(d-1)
            points,masses=perturb(d,epsilon,y)
            laws.append(('perturbed-simplex-'+str(d)+'-'+str(epsilon),points,masses))
    d=3
    lengths=(F(1),F(1,2),F(1,3))
    points=[tuple(lengths[i]*F(i==j) for j in range(d)) for i in range(d)]
    points+= [tuple(-x for x in p) for p in points]
    laws.append(('anisotropic-crosspolytope-3',points,[F(1,6)]*6))
    counters={'laws':0,'base_cancellation_checks':0,'two_sample_values':0,
              'anchor_configurations':0,'first_witness_identities':0,'pair_witness_inequalities':0}
    records=[check_law(name,points,masses,counters) for name,points,masses in laws]
    gates=[]
    for d in range(3,9):
        R0=d*(d+1);b=F(1,4*(d*R0)**d);M=1/b
        Q=(d+1)*(d+2)*8**d/b**(4*d);C=4*d*d*R0*(M+1)
        threshold=1/((d+1)*M*Q*(8*M*d*C)**d)
        Ad_power=(4*M*d*C)**d*M*Q*(d+1)
        require(Ad_power*threshold==F(1,2)**d,'local threshold equality failed')
        require(Q*(d+1)*threshold<=b,'inradius smallness gate failed')
        require(M*Q*(d+1)*threshold<=1,'volume smallness gate failed')
        require(C**d*M*Q*(d+1)*threshold==1/(8*M*d)**d,'cap-to-maximum smallness gate failed')
        gates.append({'d':d,'b':b,'Q':Q,'M':M,'C':C,'e_star':threshold,
                      'A_star_to_d':Ad_power,'exponent':F(1,d)})
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().with_name('certificate.json'))
    args=parser.parse_args()
    payload={'status':'All exact integrated-witness checks passed','counts':counters,
             'law_certificates':records,'explicit_gate_certificates':gates,
             'scope':'Finite rational laws and exact constants; the complete analytic proof covers all laws including nonatomic laws. No inverse-Minkowski theorem is used.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(payload,indent=2,default=str)+'\n')
    print(payload['status'])
    print(json.dumps(counters,sort_keys=True))
    print('Explicit gates verified in dimensions 3 through 8.')
    print('No inverse-Minkowski input is used or tested.')


if __name__=='__main__':
    main()
