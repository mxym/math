"""Author finite relative-deformation controls, not a domain certificate."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import sys
import mpmath as mp
import sympy as sy

sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'appt-exact-purity-onset-20261014'))
from check_onset import solve, positive_definite, nearint, frac, body, parameters


def vals(d, kap, p, y, z, pos=F(0),neg=F(0)):
    trace=d+kap*y+p+pos-neg
    square=d+2*kap*y+kap*kap*z+2*(1+kap)*p+p*p+2*(1+kap)*pos+pos*pos-2*neg+neg*neg
    return trace,square,square/trace**2


def to_mp(x):
    return mp.mpf(x.numerator)/x.denominator


def main():
    mp.mp.dps=260
    d,k,p,y,z=sy.symbols('D k p Y Z',positive=True)
    a=d+2*k*y+k*k*z+2*(1+k)*p+p*p
    s=d+k*y+p
    deriv=sy.diff(a,k)/a-2*sy.diff(s,k)/s
    u=sy.symbols('u',positive=True)
    mu,nu=sy.symbols('mu nu',real=True)
    # At infinite D the fixed-body derivative is uniformly 2k variance+O(k^2).
    infinite=deriv.subs({y:mu*d,z:nu*d})
    infinite=sy.limit(infinite,d,sy.oo)
    assert sy.cancel(sy.diff(infinite,k).subs(k,0)-2*(nu-mu*mu))==0
    assert infinite.subs(k,0)==0
    r=sy.symbols('r',real=True)
    rest_a=a+2*(1+k)*r+r*r-2*r+r*r
    assert sy.expand(rest_a-a-2*k*r-2*r*r)==0
    bp=d*(1+k)-k*p-p*p
    rank=sy.simplify((2*bp/(2+k)-d-p)/k)
    assert sy.cancel(rank-(d/(2+k)-p*(2+k+2*k+2*p)/((2+k)*k)))==0
    ratio=sy.simplify((2+k)*s-bp-a)
    assert sy.cancel(ratio-k*k*(y-z))==0
    symbolic=['body_derivative_variance','zero_contrast_derivative','exact_tail_increment',
              'actual_real_trace_rank','body_chord_deficit']
    slots=[(i,i) for i in range(6)]+[(i,j) for i in range(6) for j in range(i+1,6)]
    matrices,relative,interior,slack_only,invalid_variance=[],[],[],[],[]
    for mm in [256,512,1024]:
        zz,k0,pp,c0,h=parameters(mm)
        nn=-(-(mm*mm+5*mm+7)//4)-mm
        dd=mm*nn
        for tau in [F(1,mm*mm),F(1,10**30),F(1,10**100)]:
            gap=64*tau
            kap=k0-gap/(mm*mm)
            tail=tau/2
            aa=2+kap
            for edge in [(0,2),(2,3)]:
                for ns in slots:
                    mat=[[aa if i==j else F(0) for j in range(6)] for i in range(6)]
                    for (i,j),w in [((0,1),pp),(edge,tail),(ns,tail)]:
                        if i==j:mat[i][i]-=2*w
                        else:
                            mat[i][j]-=w
                            mat[j][i]-=w
                    assert positive_definite(mat)
                    resolvent=sum(solve(mat,[F(1)]*6),F(0))+F(mm-6)/aa
                    assert kap*resolvent<=1
                    ka=resolvent-F(mm)/aa
                    assert ka>=2*pp/(aa*(aa-pp))+2*tau/aa**2
                    matrices.append({'m':mm,'tau':frac(tau),'positive_edge':edge,
                                     'negative_slot':ns,'exact_psd_slack':frac(1-kap*resolvent)})
            # Actual endpoint counts, and one interior body coordinate.
            bp=dd*(1+kap)-kap*(pp+tau)-pp*pp-2*tail*tail
            rk=nearint((2*bp/aa-dd-pp)/kap)
            assert mm*(mm-1)//2<=rk<=dd-mm*(mm+1)//2
            for yy,zv,kind in [(F(rk),F(rk),'endpoint'),(F(rk)-F(1,2),F(rk)-F(3,4),'one_interior')]:
                st,at,pt=vals(dd,kap,pp,yy,zv,tail,tail)
                so,ao,po=vals(dd,kap,pp,yy,zv)
                sn,an,pn=vals(dd,k0,pp,yy,zv)
                assert pt>body(mm,nn)
                assert pn>pt
                anomaly=dd*mp.log(to_mp(pt)/to_mp(po))/to_mp(tau)
                improvement=dd*mp.log(to_mp(pn)/to_mp(po))/to_mp(gap)
                assert anomaly<mp.mpf('0.02')
                assert improvement>mp.mpf('0.1')
                relative.append({'m':mm,'n':nn,'tau':frac(tau),'body':kind,'rank':rk,
                                 'old_profit_over_bulk':frac(pt-body(mm,nn)),
                                 'feasible_improvement':frac(pn-pt),
                                 'anomaly_gain_per_tau':mp.nstr(anomaly,45),
                                 'body_gain_per_protection_slack':mp.nstr(improvement,45)})
                if kind=='one_interior':
                    _,_,p0=vals(dd,k0,pp,F(rk-1),F(rk-1))
                    _,_,p1=vals(dd,k0,pp,F(rk),F(rk))
                    assert max(p0,p1)>pn
                    interior.append({'m':mm,'tau':frac(tau),'strict_endpoint_improvement':frac(max(p0,p1)-pn)})
        for gap in [F(1,10**30),F(1,10**100)]:
            kap=k0-gap/(mm*mm)
            rk=nearint((2*(dd*(1+k0)-k0*pp-pp*pp)/(2+k0)-dd-pp)/k0)
            _,_,old=vals(dd,kap,pp,F(rk),F(rk))
            _,_,new=vals(dd,k0,pp,F(rk),F(rk))
            assert new>old
            slack_only.append({'m':mm,'slack':frac(gap),'strict_improvement':frac(new-old)})
        rr,kk=mm*(mm-1)//2,mm*(mm+1)//2
        middle=dd-rr-kk
        yy,zv=F(rr)+F(middle,2),F(rr)+F(middle,4)
        ss,aa,ppur=vals(dd,k0,pp,yy,zv)
        de=(2*yy+2*k0*zv+2*pp)/aa-2*yy/ss
        assert de<k0/4
        assert ppur<body(mm,nn)
        invalid_variance.append({'m':mm,'n':nn,'actual_body_derivative_over_kappa':frac(de/k0),
                                 'body_not_profitable':True,'false_universal_derivative_bound_rejected':True})
    files={f:{'sha256':hashlib.sha256(Path(f).read_bytes()).hexdigest(),
              'lines':len(Path(f).read_text().splitlines())}
           for f in ['PAPER.md','THEOREM_MAP.md','check_critical.py']}
    report={'status':'PASS_AUTHOR_FINITE_CONTROLS','scope':'finite symbolic/Fraction/mp only; no Lean',
            'versions':{'sympy':sy.__version__,'mpmath':mp.__version__,'digits':mp.mp.dps},
            'files':files,'credited_helper':'../appt-exact-purity-onset-20261014/check_onset.py (functions only; no old main run)',
            'symbolic_groups':symbolic,'all_slot_psd_controls':matrices,'tiny_tail_relative_comparisons':relative,
            'strict_endpoint_body_controls':interior,'tiny_protection_slack_controls':slack_only,
            'false_unconditional_variance_bound_controls':invalid_variance,
            'logical_guard':'Actual profitable multi-head states retained: localization alone does not force an exact finite optimizer; a strictly better feasible state is exhibited.'}
    Path('author_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'symbolic_groups':len(symbolic),
                      'all_slot_psd':len(matrices),'relative_tiny_tail':len(relative),
                      'body_endpoint':len(interior),'slack_only':len(slack_only),
                      'false_variance_rejections':len(invalid_variance)}))


if __name__=='__main__':main()
