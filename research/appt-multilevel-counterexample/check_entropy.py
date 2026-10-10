#!/usr/bin/env python3
"""Exact rational and interval checks supporting ENTROPY_ASYMPTOTIC.md.

The proof is analytic. These finite tests do not certify the uniform graph
limit, the all-unitary quantifier, or the asymptotic optimization by sampling.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
from math import isqrt
from pathlib import Path
from random import Random

ROOT=Path(__file__).resolve().parent

class CheckFailure(RuntimeError):
    pass

def require(ok: bool, text: str) -> None:
    if not ok: raise CheckFailure(text)

def plus(*ivs):
    return (sum((x[0] for x in ivs),F(0)),sum((x[1] for x in ivs),F(0)))

def times(c,iv):
    c=F(c)
    return (c*iv[0],c*iv[1]) if c>=0 else (c*iv[1],c*iv[0])

def constant(x):return (F(x),F(x))

@lru_cache(maxsize=None)
def log_interval(x: F):
    """Certified natural-log bounds via range reduction and the artanh series."""
    x=F(x);require(x>0,'logarithm input positive')
    z=x;k=0
    while z<1:z*=2;k-=1
    while z>=2:z/=2;k+=1
    def core(y):
        N=18
        low=2*sum((y**(2*i+1)/F(2*i+1) for i in range(N)),F(0))
        high=low+2*y**(2*N+1)/(F(2*N+1)*(1-y*y))
        return low,high
    return plus(core((z-1)/(z+1)),times(k,core(F(1,3))))

@lru_cache(maxsize=None)
def f_interval(x: F):
    x=F(x);require(x>=-1,'entropy kernel input at least minus one')
    if x==-1:return constant(1)
    return plus(times(1+x,log_interval(1+x)),constant(-x))

def hplus_interval(a):
    return plus(constant(F(a)*a/2),times(-1,f_interval(F(a))))

def scalar_entropy_check() -> dict:
    count=nonlinear=0;rng=Random(843388)
    for a in [F(i,20) for i in range(61)]:
        low,high=hplus_interval(a)
        bound=a**3/(3*(a+2))
        if a:require(low>=bound,'positive-side cubic correction lower bound')
        else:require(low==high==bound==0,'zero cubic endpoint')
        if 1<=a<=2:
            z=a-1
            polynomial=3*a**4+7*a**3-18*a*a-12*a+24
            sos=3*z**4+19*z**3+21*(z-F(5,14))**2+F(37,28)
            require(polynomial==sos,'exact entropy comparison SOS polynomial')
            require(bound-(1-a*a/4)*(a-1)==polynomial/(12*(a+2)), 'cubic correction minus head cross-term identity')
            nonlinear+=1
        count+=1
    heads=0
    for h in (1,2,4,8,16,32):
        for y in (F(0),F(1,20),F(1,4),F(1,2),F(3,4),F(9,10),F(19,20),F(1)):
            bs=[y]+([F(0)]*h if y==1 else [y/F(3**(i+1)) for i in range(h)])
            budget=4*(1-y)
            require(sum(b*b for b in bs[1:])<=budget,'head test starts feasible')
            base=sorted([F(rng.randrange(1,11),10) for _ in range(h)],reverse=True)
            lo=F(0);hi=F(4)
            for _ in range(18):
                mid=(lo+hi)/2
                if sum((mid*a+b)**2 for a,b in zip(base,bs[1:]))<=budget:lo=mid
                else:hi=mid
            aa=[lo*a for a in base]
            require(sum((a+b)**2 for a,b in zip(aa,bs[1:]))<=budget,'shifted-star budget')
            E=plus(*(f_interval(a) for a in aa),*(f_interval(-b) for b in bs),constant(sum(a*b for a,b in zip(aa,bs))))
            require(E[1]<=2,'nonlinear head bound including paired cross terms')
            a1=aa[0]
            if a1>=1:require(E[1]<=2-F(37,1344),'uniform positive-head rigidity gap')
            elif a1<1:
                gap=hplus_interval(a1)[0]+y*(1-a1)
                require(2-E[0]>=gap,'entropy rigidity inequality intervals are consistent')
            heads+=1
    # All comparisons here use outward rational enclosures, not binary floats.
    low,high=f_interval(F(-1,2))
    require(low>F(1,8),'negative outlier disproves an unrestricted quadratic Taylor upper bound')
    return {'positive_cubic_cases':count,'exact_SOS_comparisons':nonlinear,'feasible_nonlinear_heads':heads}

def appt_families(m,n):
    D=m*n
    families=[[F(1,D)]*D]
    for k in (1,D//2,D-1):
        c=F(2,m-1);den=D+c*k
        families.append([(1+c)/den]*k+[1/den]*(D-k))
        if m>=4:
            raw=[6*m-19]+[2*m-3]*(k-1)+[2*m-5]*(D-k);den=sum(raw)
            families.append([F(x,den) for x in raw])
    # I-t|v><v| is APPT for 0<=t<=1, since each Schmidt witness has largest eigenvalue <=1.
    for t in (F(1),F(19,20)):
        families.append([1/(D-t)]*(D-1)+[(1-t)/(D-t)])
    return families

def entropy_deficit_iv(lam):
    D=len(lam)
    return plus(*(times(multiplicity*x,log_interval(D*x)) for x,multiplicity in Counter(lam).items() if x))

def physical_star_check() -> dict:
    states=assignments=normalizations=tail_checks=upperchecks=0
    for m in range(3,15):
        for n in (m,m+1,2*m):
            D=m*n;R=m*(m-1)//2;S=m*(m+1)//2;h=m-1;j=D-S+1
            C=max(F(8),4+F(D,h*h));Btail=max(F(4),F(D,h*h))
            for lam in appt_families(m,n):
                require(sum(lam)==1 and lam==sorted(lam,reverse=True),'ordered normalized actual-state family')
                b=lam[j-1];require(b>0,'positive pivot')
                aa=[lam[i]/b-1 for i in range(h)]
                bs=[1-lam[-1-i]/b for i in range(h+1)];y=bs[0]
                modified=[a+bb for a,bb in zip(aa,bs[1:])]
                require(sum(v*v for v in modified)<=4*(1-y),'least-eigenvalue-centered physical star')
                # Assign all rank-m witness eigenspaces using distinct actual eigenvalues.
                diag_bottom=[1]+list(range(h+2,2*h+2))
                positive_bottom=list(range(2,h+2))+list(range(2*h+2,S+1))
                require(len(diag_bottom)==m and len(positive_bottom)==R,'all Schmidt-witness slots filled')
                require(sorted(diag_bottom+positive_bottom)==list(range(1,S+1)),'bottom assignment has no duplicate or omitted slot')
                edges=[(0,i) for i in range(1,m)]+[(i,k) for i in range(1,m) for k in range(i+1,m)]
                x=[F(1)]+[v/2 for v in modified]
                value=sum(lam[D-r]*z*z for r,z in zip(diag_bottom,x))
                value-=sum((lam[i]-lam[D-r])*x[a]*x[c] for i,((a,c),r) in enumerate(zip(edges,positive_bottom)))
                require(value>=0,'explicit rational Schmidt expectation on known APPT states')
                assignments+=1
                z=[v/b-1 for v in lam];t=1/(D*b)
                nu=F(m,D)+F(2,h)
                require(abs(t-1)<=nu,'uniform two-sided pivot normalization')
                g=[(lam[i]-lam[-1-i])/b for i in range(R)];w=g[-1]
                V=sum(v*v for v in lam)-F(1,D)
                H=sum((v-w)**2 for v in g[:h])
                require(V/(b*b)<=H+Btail,'tail-only triangular variance budget')
                require(sum(v*v for v in z)<=6*C,'total pivot-centered square budget')
                head_indices=set(range(h))|set(range(D-h-1,D))
                require(all(z[i]*z[i]<=F(4,h) for i in range(D) if i not in head_indices),'all nonexceptional deviations are small')
                # Independently evaluate both sides of the exact normalization formula with certified intervals.
                lhs=times(1/b,entropy_deficit_iv(lam))
                rhs=plus(*(times(mult,f_interval(v)) for v,mult in Counter(z).items()),times(-D,f_interval(t-1)))
                require(max(lhs[0],rhs[0])<=min(lhs[1],rhs[1]),'entropy centering identity agrees in rational enclosures')
                if m>=10:
                    delta=F(2,isqrt(h));nu_m=F(1,m)+F(2,h)
                    require(delta<1 and nu_m<1,'finite entropy upper parameters')
                    bound=C*(F(1,2)+3*delta/(1-delta)+3*nu_m)
                    require(lhs[1]<=bound,'finite unrestricted entropy upper bound on actual APPT families')
                    upperchecks+=1
                normalizations+=1;tail_checks+=1;states+=1
    return {'SOS_projection_and_hole_states':states,'physical_slot_assignments':assignments,'normalizations':normalizations,'tail_budget_tests':tail_checks,'finite_entropy_upper_tests':upperchecks}

def fixed_m_and_renyi_check() -> dict:
    fixed=interval_tests=interpolation=0
    for m in (2,3,4,5,10,20,50):
        r=F(m+1,m-1);lgr=log_interval(r);tau=(r*lgr[0]/(r-1),r*lgr[1]/(r-1))
        require(tau[0]>1 and tau[1]<r,'fixed-m entropy stationary point is interior')
        h_lower=tau[0]-1-log_interval(tau[0])[1]
        h_upper=tau[1]-1-log_interval(tau[1])[0]
        require(0<h_lower<=h_upper,'fixed-m entropy constant positive')
        for n in (m,10*m,100*m):
            D=m*n;theta_mid=(((tau[0]+tau[1])/2)-1)/(r-1)
            k=(D*theta_mid).numerator//(D*theta_mid).denominator
            theta=F(k,D);Z=1+(r-1)*theta
            value=plus(times(r*theta/Z,lgr),times(-1,log_interval(Z)))
            require(value[1]<=h_upper,'actual projection entropy is below continuous interval optimum')
            fixed+=1
        for num in range(1,10):
            # A distribution supported inside an interval of endpoint ratio r.
            raw=[F(1)+(r-1)*F(i,10+num) for i in range(11)];den=sum(raw)
            lam=[v/den for v in raw]
            deficit=entropy_deficit_iv(lam)
            require(deficit[1]<=h_upper,'bulk interval entropy inequality')
            interval_tests+=1
        # At alpha=2 the closed fixed-m Renyi constant is log[m^2/(m^2-1)].
        c=r+1;z=c/(2*(c-1))
        require(c*z/2==F(m*m,m*m-1),'generalized interval moment recovers purity factor')
    alpha=F(3,2)
    for root in (F(1,4),F(1,3),F(1,2),F(2,3),F(3,4),F(1),F(5,4),F(3,2),F(2)):
        t=root*root;x=t-1
        exact=(root**3-1-alpha*x)/(alpha*(alpha-1))
        rhs=plus(constant((alpha-1)*x*x/2),times(2-alpha,f_interval(x)))
        if x:require(exact<=rhs[0],'Renyi kernel bounded by quadratic and entropy mixture')
        else:require(exact==rhs[0]==rhs[1]==0,'Renyi zero endpoint')
        interpolation+=1
    return {'fixed_m_projection_checks':fixed,'bulk_interval_tests':interval_tests,'exact_three_halves_kernel_checks':interpolation}

def explicit_entropy_counterexample() -> dict:
    m=50;n=200;D=m*n;k=4900;Z=3244431
    raw=[861]+[330]*(k-1)+[319]*(D-k)
    require(sum(raw)==Z,'explicit entropy counterexample trace')
    lam=[F(x,Z) for x in raw]
    # This is I/projection/spike positivity from a finite, rational SOS, not the limiting graph test.
    require((2*319-542)*(2*319-47*11)==2*48*11**2,'finite APPT two-block determinant equality')
    # Coefficients of x^2,y^2,xy,xT,yT,T^2,Q, independently expanded.
    lhs_coeff=[F(319),F(319),F(-542),F(-11),F(-11),F(-11,2),F(649,2)]
    rhs_coeff=[F(295+24),F(295+24),F(-590+48),-48*F(11,48),-48*F(11,48),
               -F(649,96)+24*F(11,48)**2,F(649,2)]
    require(lhs_coeff==rhs_coeff,'symbolic quadratic coefficient identity for physical SOS')
    for x,y,T,Q in ((F(2),F(1),F(3),F(7)),(F(1),F(1),F(48),F(48)),(F(3,7),F(-2,5),F(8),F(14))):
        pairs=x*y+(x+y)*T+(T*T-Q)/2
        lhs=319*(x*x+y*y+Q)-11*pairs-531*x*y
        rhs=295*(x-y)**2+F(649,2)*(Q-T*T/48)+24*(x+y-F(11,48)*T)**2
        require(lhs==rhs,'explicit entropy APPT SOS identity')
    r=F(51,49);lr=log_interval(r)
    tau=(r*lr[0]/(r-1),r*lr[1]/(r-1))
    broad=(tau[0]-1-log_interval(tau[0])[1],tau[1]-1-log_interval(tau[1])[0])
    spike=plus(times(F(3,D+2),log_interval(F(3))),times(-1,log_interval(F(D+2,D))))
    hole=log_interval(F(D,D-1))
    rows=[]
    for eps in (F(0),F(1,1000)):
        state=[(1-eps)*x+eps/D for x in lam]
        value=entropy_deficit_iv(state)
        gaps={}
        for name,iv in [('all_two_level_ratio_candidates',broad),('single_spike',spike),('one_hole',hole)]:
            low=D*(value[0]-iv[1]);high=D*(value[1]-iv[0])
            require(low>F(3,10),'explicit entropy violation exceeds three tenths over D')
            # Store outward rational decimal-grid bounds, never rounded floating-point evidence.
            den=10**6
            lo=F((low*den).numerator//(low*den).denominator,den)
            hi=F(-(-(high*den).numerator//(high*den).denominator),den)
            require(lo<=low<=high<=hi,'outward interval recording')
            gaps[name]={'D_times_gap_lower':str(lo),'D_times_gap_upper':str(hi)}
        rows.append({'mixture_weight':str(eps),'uniform_PT_floor':str(eps/D),'gaps':gaps})
    return {'m':m,'n':n,'numerators':[861,330,319],'multiplicities':[1,4899,5100],
            'normalizer':Z,'certified_cases':rows,'comparison_scope':'Continuous spectral-ratio maximum, spike and rank-(D-1) candidates; Theorem 6.10 identifies their discrete maximum as the inner-polytope entropy deficit'}

def higher_renyi_check() -> dict:
    kernels=monotonicity=finite_m=0
    for alpha in (3,4,5,6,8):
        def f(x):return ((1+x)**alpha-1-alpha*x)/F(alpha*(alpha-1))
        def k(x):return f(x)-x*x/2
        xs=[F(i,20) for i in range(1,61)]
        ratios=[k(x)/(x*x) for x in xs]
        require(all(a<b for a,b in zip(ratios,ratios[1:])), 'higher-order positive nonlinear ratio strictly increases')
        monotonicity+=len(xs)-1
        for x in [F(-i,20) for i in range(21)]:
            require(k(x)<=0,'higher-order negative nonlinear correction has favorable sign')
            kernels+=1
        A=F(3**alpha-1-2*alpha,alpha-1)
        for gamma in (F(1),F(2),F(4),F(7),F(100)):
            K=max(F(8),4+gamma)
            require(alpha*(K/2+k(F(2)))==A+F(alpha,2)*max(F(4),gamma),'exact high-order spike correction identity')
        for m in range(2,20):
            r=F(m+1,m-1);c=(r**alpha-1)/(r-1);z=(alpha-1)*c/(alpha*(c-1))
            require(1/r<z<1,'fixed-m high-order secant optimizer interior')
            value=z**(alpha-1)*(c-(c-1)*z)
            require(value==c*z**(alpha-1)/alpha,'fixed-m high-order optimal power value')
            for j in range(11):
                test=1/r+(1-1/r)*F(j,10)
                require(test**(alpha-1)*(c-(c-1)*test)<=value,'fixed-m high-order power objective maximized')
            finite_m+=1
    require(F(3**3-1-6,2)+6==16,'order-three balanced sharp coefficient is sixteen')
    return {'negative_kernel_cases':kernels,'positive_ratio_comparisons':monotonicity,'fixed_m_integer_order_optimizations':finite_m}

def negative_controls() -> list[dict]:
    out=[]
    lo,_=f_interval(F(-1,2));require(lo>F(1,8),'negative-side quadratic upper bound rejected')
    out.append({'name':'Taylor upper bound used at a negative outlier','rejected':True,'diagnostic':'f(-1/2) exceeds one eighth'})
    # Sixteen holes pass the old four-unit head square budget, but not the shifted star.
    require(16*F(1,2)**2==4,'false head saturates old square budget')
    require(16*lo>2 and 15*F(1,2)**2>4*(1-F(1,2)),'least-eigenvalue-centered star is necessary')
    out.append({'name':'drop the modified physical star','rejected':True,'diagnostic':'sixteen half-height holes would exceed the entropy head bound and violate the new star'})
    a=F(3,2);z=a-1
    rhs=3*z**4+19*z**3+21*(z-F(5,14))**2+F(37,28)
    require(rhs!=3*a**4+7*a**3-17*a*a-12*a+24,'altered SOS coefficient rejected')
    out.append({'name':'alter the nonlinear entropy polynomial','rejected':True,'diagnostic':'exact SOS identity fails'})
    require((3**3-1-2*3)/F(2)-F(3,2)*4==4,'order-three spike improves on flat entropy value')
    out.append({'name':'extend the flat Renyi formula past order two','rejected':True,'diagnostic':'existing APPT spike family has an extra four in its order-three deficit coefficient'})
    r=F(3);tau=(r*log_interval(r)[0]/2,r*log_interval(r)[1]/2)
    h_lower=tau[0]-1-log_interval(tau[0])[1]
    require(h_lower>F(1,8),'fixed-qubit constant differs from growing-m approximation')
    out.append({'name':'replace the fixed-m constant by one over two m squared','rejected':True,'diagnostic':'exact qubit interval constant is strictly larger'})
    return out

def run_checks() -> dict:
    rep={'status':'PASS','scope':'Exact rational and outward-interval ancillary calculations; not independent CI, Lean, external review, or a finite proof of the unbounded result',
         'nonlinear_entropy':scalar_entropy_check(),'physical_stars':physical_star_check(),
         'fixed_m_and_renyi':fixed_m_and_renyi_check(),'higher_renyi':higher_renyi_check(),'explicit_entropy_counterexample':explicit_entropy_counterexample(),'negative_controls':negative_controls()}
    names=['ENTROPY_ASYMPTOTIC.md','check_entropy.py','TWO_ENDED_GRAPH_LIMIT.md','FLAT_EXTREMIZERS.md','SHARP_ASYMPTOTIC.md']
    rep['source_hashes']={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in names}
    return rep

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--report',type=Path)
    args=ap.parse_args();rep=run_checks();text=json.dumps(rep,indent=2)+'\n'
    if args.report:args.report.parent.mkdir(parents=True,exist_ok=True);args.report.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
