"""Finite ordinary diagnostics; this does not prove all APPT optimizers."""
from __future__ import annotations
import argparse
from decimal import Decimal as Z, getcontext
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json

getcontext().prec = 260
EPS = Z('1e-145')

def require(value, label):
    if not value:
        raise RuntimeError(label)

def dec(x):
    if isinstance(x, F):
        return Z(x.numerator) / Z(x.denominator)
    return Z(x)

def close(x, y, label):
    require(abs(x-y) <= EPS * max(Z(1), abs(x), abs(y)), label)

def theta(r, alpha):
    b = r-1
    if alpha == 1:
        return (r*r.ln()-b)/(b*b)
    Q = (alpha*r.ln()).exp()
    return (Q-1-alpha*b)/(b*(alpha-1)*(Q-1))

def gap(r, alpha, x):
    b = r-1
    if alpha == 1:
        return x*r*r.ln()/(1+b*x)-(1+b*x).ln()
    Q = (alpha*r.ln()).exp()
    return ((1+x*(Q-1)).ln()-alpha*(1+b*x).ln())/(alpha-1)

def derivative(r, alpha, x):
    if alpha == 1:
        return (r*r.ln()-(r-1)-(r-1)**2*x)/(1+(r-1)*x)**2
    Q = (alpha*r.ln()).exp()
    return ((Q-1)/(1+x*(Q-1))-alpha*(r-1)/(1+x*(r-1)))/(alpha-1)

def integers_around(x, lo, hi):
    k = int(x)
    return sorted({max(lo, min(hi, k)), max(lo, min(hi, k+1))})

def interval_sum(high, low, i, j, start, end):
    nh = max(0, min(end, i)-max(start, 1)+1)
    nl = max(0, min(end, j)-max(start, i+1)+1)
    return nh*high+nl*low

def exact_vertices():
    cases=[]; vertices=0; powers=0; sign_checks=0; bell=[]
    for m in [3,4,5,8,12]:
        R=m*(m-1)//2; K=m*(m+1)//2
        for n in [m,m+1,2*m,3*m,10*m]:
            D=m*n; neg=[]; pos=[]; zero=[]
            for i in range(1,D+1):
                h=F(max(0,i-D+K)-min(i,R),i)
                formula=-F(min(i,R),i) if i<=D-K else F(i-D+m,i)
                require(h==formula, 'halfspace sign formula')
                (neg if h<0 else pos if h>0 else zero).append(i)
                sign_checks+=1
            require(neg==list(range(1,D-m)), 'all negative indices')
            require(pos==list(range(D-m+1,D+1)), 'all positive indices')
            require(zero==[D-m], 'unique zero vertex')
            count=0
            for i in neg:
                A=min(i,R)-max(0,i-D+K)
                for j in pos:
                    s=D-j; B=m-s; den=i*B+j*A
                    high=F(A+B,den); low=F(A,den)
                    require(high>low>0 and i<j, 'cut ordering')
                    require(i*high+(j-i)*low==1, 'exact trace')
                    h=interval_sum(high,low,i,j,D-K+1,D)-interval_sum(high,low,i,j,1,R)
                    require(h==0, 'exact actual witness halfspace')
                    weight=F(i*B,den)
                    require(weight/F(i)+(1-weight)/F(j)==high, 'gap cut high')
                    require((1-weight)/j==low, 'gap cut low')
                    ratio=1+F(B,A); th=F(i,j)
                    for alpha in [2,3]:
                        lhs=D**(alpha-1)*(i*high**alpha+(j-i)*low**alpha)
                        rhs=F(D,j)**(alpha-1)*(1+th*(ratio**alpha-1))/(1+(ratio-1)*th)**alpha
                        require(lhs==rhs, 'exact moment normalization')
                        powers+=1
                    count+=1
            require(count==m*(D-m-1), 'complete finite cut count')
            for s in range(m+1):
                j=D-s
                require(F(max(0,j-D+K)-R,j)>=0, 'all old survivors')
            vertices+=count+m+1
            expectation=F(1,1)-F(m,2)
            require(expectation<0, 'fake relaxation spike negative PPT')
            # P is the actual |12>-|21> Bell projector in the original C^m x C^n.
            bell.append({'m':m,'n':n,'density_partial_transpose_expectation':str(expectation/(D+m))})
            cases.append({'m':m,'n':n,'D':D,'cut_vertices':count,'old_vertices':m+1})
    return {'cases':cases,'halfspace_sign_checks':sign_checks,
            'cut_and_old_vertices':vertices,'exact_moment_identities':powers,
            'actual_Bell_negative_controls':bell}

def scalar_checks():
    records=[]
    for m in [3,4,5,8,12]:
        q=F(m+1,m-1); r=dec(q); t=r-1
        for a in [Z('0.1'),Z('0.5'),Z('0.9'),Z(1)-Z('1e-70'),Z(1),Z(1)+Z('1e-70'),Z(2),Z(3),Z(10)]:
            th=theta(r,a)
            require(0<th<1,'scalar stationary rank interior')
            close(derivative(r,a,th),Z(0),'stationary derivative')
            for x in [th/2,(th+1)/2]:
                c=(a*r.ln()).exp()-1
                alternate=t*c*(th-x)/((1+c*x)*(1+t*x))
                close(derivative(r,a,x),alternate,'unimodality identity')
                require(derivative(r,a,th/2)>0 and derivative(r,a,(th+1)/2)<0,'strict derivative signs')
            if a==2:
                close(th,dec(F(m-1,2*m)),'known purity scalar rank')
            records.append({'m':m,'alpha':str(a),'theta':str(th),'B':str(gap(r,a,th))})
        th1=theta(r,Z(1))
        credited=dec(F(m-1,4))*((m+1)*r.ln()-2)
        close(th1,credited,'credited AAW entropy rank')
        for a in [Z(1)-Z('1e-70'),Z(1)+Z('1e-70')]:
            require(abs(theta(r,a)-th1)<Z('1e-68'), 'rank continuity through1')
    return records

def vertex_candidates(m,D,a):
    R=m*(m-1)//2; K=m*(m+1)//2; q=dec(F(m+1,m-1))
    bulk=[]; other=[]
    for k in integers_around(Z(D)*theta(q,a),R,D-K):
        bulk.append((gap(q,a,Z(k)/D),k))
    for s in range(m+1):
        other.append(((Z(D)/Z(D-s)).ln(),{'kind':'uniform','s':s}))
    for s in range(m):
        j=D-s; B=m-s; loss=(Z(D)/Z(j)).ln()
        for i in range(1,R):
            r=dec(1+F(B,i))
            other.append((loss+gap(r,a,Z(i)/j),{'kind':'early','i':i,'s':s}))
        for ell in range(m+1,K):
            i=D-ell; A=ell-m; r=dec(1+F(B,A))
            other.append((loss+gap(r,a,Z(i)/j),{'kind':'late','ell':ell,'s':s}))
        if s:
            r=dec(1+F(B,R))
            for i in integers_around(Z(j)*theta(r,a),R,D-K):
                other.append((loss+gap(r,a,Z(i)/j),{'kind':'middle','i':i,'s':s}))
    # Each finite middle interval has unimodality, so its two neighbors exhaust its maximum.
    # This is a finite scalar reduction, not independent numerical proof of an infinite theorem.
    return max(bulk),max(other,key=lambda v:v[0])

def finite_comparisons():
    rows=[]; failures=[]; rounding=[]; rounding_failures=[]; logrows=[]; false_extension=[]
    orders=[Z('0.1'),Z('0.5'),Z('0.9'),Z(1)-Z('1e-70'),Z(1),Z(1)+Z('1e-70'),Z(2),Z(3),Z(10)]
    for m in [3,4,5,8,12]:
        r=dec(F(m+1,m-1)); t=r-1
        for e in [0,1,2,6,12]:
            n=m*10**e; D=m*n
            for a in orders:
                bulk,other=vertex_candidates(m,D,a)
                passed=bulk[0]>other[0]
                row={'m':m,'n':str(n),'D':str(D),'exponent':e,'alpha':str(a),
                     'bulk_wins_outer':passed,'rank':str(bulk[1]),
                     'other_kind':other[1],'deficit_margin':str(bulk[0]-other[0])}
                rows.append(row)
                if not passed: failures.append(row)
                if e==12:
                    th=theta(r,a); c=(a*r.ln()).exp()-1
                    J=t*c/((1+c*th)*(1+t*th))
                    dist=min(abs(Z(int(Z(D)*th))-Z(D)*th),abs(Z(int(Z(D)*th)+1)-Z(D)*th))
                    loss=gap(r,a,th)-bulk[0]
                    approx=J*dist*dist/(2*Z(D)**2)
                    scaled=(loss-approx)*Z(D)**3
                    rounding.append({'m':m,'alpha':str(a),'scaled_third_order_remainder':str(scaled)})
                    # Loose finite diagnostic bound, not the uniform analytic remainder constant.
                    if abs(scaled)>=1000: rounding_failures.append(rounding[-1])
        sigma=1/Z(m-1).ln()
        for e in [6,12,30,60]:
            D=m*m*10**e
            for ratio in [Z('0.25'),Z('0.5'),Z('0.9'),Z('1.1')]:
                a=ratio*sigma*Z(D).ln()
                bulk,other=vertex_candidates(m,D,a)
                sp=gap(Z(m+1),a,1/Z(D))
                row={'m':m,'exponent':e,'alpha':str(a),'c_over_sigma':str(ratio),
                     'bulk_wins_outer':bulk[0]>other[0],
                     'deficit_margin':str(bulk[0]-other[0]),'competitor':other[1],
                     'fake_spike_beats_continuous_bulk':sp>gap(r,a,theta(r,a))}
                logrows.append(row)
                if ratio>1 and e==60:
                    require(row['fake_spike_beats_continuous_bulk'],'method-ceiling negative extension')
                    false_extension.append(row)
    largest=[x for x in rows if x['exponent']==12]
    require(all(x['bulk_wins_outer'] for x in largest), 'largest compact samples still need investigation')
    require(not rounding_failures, 'finite Taylor-rounding diagnostic unexpectedly large')
    large_log=[x for x in logrows if x['exponent']==60 and Z(x['c_over_sigma'])<1]
    require(all(x['bulk_wins_outer'] for x in large_log), 'largest below-ceiling samples still need investigation')
    return {'compact_cases':rows,'retained_smaller_outer_failures':failures,
            'largest_compact_samples_all_bulk':True,'rounding_cases':rounding,
            'logarithmic_cases':logrows,'largest_below_ceiling_samples_all_bulk':True,
            'above_ceiling_nonAPPT_controls':false_extension}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--out',required=True)
    args=ap.parse_args()
    exact=exact_vertices(); scalars=scalar_checks(); finite=finite_comparisons()
    report={'status':'PASS_FINITE_ORDINARY_DIAGNOSTICS','precision_decimal_digits':260,
            'implementations':1,'infinite_APPT_proof_certificate':False,
            'new_Lean_execution':False,'scope':'Finite rational vertices and scalar diagnostics; smaller relaxation failures retained',
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'exact_geometry':exact,'scalar_cases':scalars,'finite_comparisons':finite}
    Path(args.out).write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':report['status'],
                      'exact_vertices':exact['cut_and_old_vertices'],
                      'exact_moment_identities':exact['exact_moment_identities'],
                      'scalar_cases':len(scalars),
                      'actual_Bell_controls':len(exact['actual_Bell_negative_controls']),
                      'compact_cases':len(finite['compact_cases']),
                      'smaller_outer_failures_retained':len(finite['retained_smaller_outer_failures']),
                      'rounding_cases':len(finite['rounding_cases']),
                      'logarithmic_cases':len(finite['logarithmic_cases']),
                      'above_method_ceiling_controls':len(finite['above_ceiling_nonAPPT_controls']),
                      'ordinary_implementations':1,'infinite_proof_certificate':False},indent=2))

if __name__=='__main__': main()
