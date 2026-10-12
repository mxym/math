#!/usr/bin/env python3
"""Independent exact finite and numerical root-overlap regression controls.

These tests do not prove the infinite-dimensional Sobolev characterization.
No source manuscript is modified. Exact lattice tests include translated zeros.
"""
from fractions import Fraction as Q
import json, math, random
from pathlib import Path
from scipy.special import roots_legendre

def require(p, msg):
    if not p: raise ArithmeticError(msg)

def exact_profiles():
    rng=random.Random(20261007); count=0
    for case in range(120):
        roots=[Q(rng.randrange(6),rng.randrange(1,5)) for _ in range(20)]
        if not any(roots): roots[0]=Q(1)
        for s in (2,3,4,5):
            mass=sum(a**s for a in roots)
            for shift in (1,2,7,21):
                def sig(i): return roots[i] if 0<=i<len(roots) else Q(0)
                bp=ap=am=wp=Q(0)
                for i in range(-shift,len(roots)+shift):
                    a=sig(i); b=sig(i+shift); c=sig(i-shift)
                    dp=max(Q(0),1-(b/a)**s) if a else Q(0)
                    dm=max(Q(0),1-(c/a)**s) if a else Q(0)
                    w=6*abs(dp-dm)+2*dp
                    require(0<=w<=8,'weight bound')
                    require(w>=2*max(dp,dm),'pointwise lower bound')
                    require(max(a-b,0)<=a*dp<=s*max(a-b,0),'root-downward bound')
                    bp+=abs(a-b)**s/mass
                    ap+=a**s*dp**s/mass; am+=a**s*dm**s/mass
                    wp+=a**s*w**s/mass
                xi=max(ap,am)
                require(2**s*xi<=wp<=14**s*xi,'loss norm equivalence')
                require(bp<=Q(2)**(1-s)*wp,'root lower bound includes upward zero support')
                require(wp<=(14*s)**s*bp,'root upper bound')
                count+=1
    return {'cases':count,'arithmetic':'Fraction only','zero_extension':True,'all_pass':True}

def triangle_tests():
    rows=[]; a=.23
    quadrature={n:roots_legendre(n) for n in (256,512)}
    for s in (1.1,1.5,2.,3.,5.):
        C=(s+1)**(1/s)
        def sig(x):
            if 0<x<a: return C*x/a
            if a<=x<1: return C*(1-x)/(1-a)
            return 0.
        def target(x):
            if 0<x<a: return 6*s*C/a
            if a<x<1: return 8*s*C/(1-a)
            return 0.
        exact=s*C*(6**s*a**(1-s)+8**s*(1-a)**(1-s))**(1/s)
        seq=[]
        for h in (.02,.005,.001,.0001,.00001):
            def approx(x):
                sx=sig(x)
                if sx==0: return 0.
                def deficit(t):
                    if t<=0: return 1.
                    if t>=1: return 0.
                    return -math.expm1(s*math.log(t))
                dp=deficit(sig(x+h)/sx)
                dm=deficit(sig(x-h)/sx)
                return sx*(6*abs(dp-dm)+2*dp)/h
            pts=sorted(set([0.,1.,a,a*(1-h),a+(1-a)*h,a+(1-2*a)*h]+[v for c in (0.,a,1.) for v in (c-h,c+h) if 0<v<1]))
            # Resolve the shrinking endpoint layers on a geometric mesh.
            scale=h
            while scale<.5:
                pts.extend((scale,1-scale)); scale*=2
            pts=sorted(set(pts))
            resolutions=[]
            for n,(nodes,weights) in quadrature.items():
                err=norm=0.
                for l,r in zip(pts,pts[1:]):
                    for z,w in zip(nodes,weights):
                        x=(l+r)/2+(r-l)*z/2; v=approx(x)
                        err+=(r-l)*w/2*abs(v-target(x))**s
                        norm+=(r-l)*w/2*v**s
                resolutions.append({'points_per_piece':n,'relative_Ls_error':err**(1/s)/exact,'norm_ratio':norm**(1/s)/exact})
            drift=max(abs(resolutions[0][k]-resolutions[1][k]) for k in ('relative_Ls_error','norm_ratio'))
            require(drift<2e-5,f'quadrature resolution consistency s={s} h={h} drift={drift}')
            seq.append({'h':h,**resolutions[-1],'resolution_drift':drift})
        require(seq[-1]['relative_Ls_error']<.2,'triangle convergence control')
        require(abs(seq[-1]['norm_ratio']-1)<.002,'exact 6/8 first-order constant')
        require(seq[-1]['relative_Ls_error']<seq[0]['relative_Ls_error'],'decreasing error')
        rows.append({'s':s,'positive_slope_coefficient':6*s,'negative_slope_coefficient':8*s,'expected_norm':exact,'sequence':seq})
    return rows

def boundary_controls():
    # r=1_(0,1); h<1/2 gives disjoint edge strips with W=6 and W=8.
    rows=[]
    for s in (1,2,3,5):
        seq=[{'h':h,'norm_over_h':((6**s+8**s)*h)**(1/s)/h} for h in (.1,.01,.001)]
        if s==1: require(all(abs(v['norm_over_h']-14)<1e-10 for v in seq),'BV endpoint 14')
        else: require(seq[-1]['norm_over_h']>seq[0]['norm_over_h'],'boundary jump rejection')
        rows.append({'s':s,'sequence':seq})
    return rows

if __name__=='__main__':
    result={'scope':'finite regression and numerical diagnostics only; proof is in CORE_PROOF_REVIEW.md','exact_profiles':exact_profiles(),'asymmetric_triangle_strong_limit':triangle_tests(),'boundary_endpoint_controls':boundary_controls()}
    dest=Path(__file__).with_name('root-overlap-results.json'); dest.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS:',result['exact_profiles']['cases'],'exact zero-extended profile tests; 25 numerical limit cases; 12 boundary controls')
