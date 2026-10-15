"""Finite author controls on exact compressed physical spectra, not an M* solver."""
from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib, json, shutil, traceback
import sympy as s
import mpmath as mp

base=Path(__file__).resolve().parent
run=base/'control-runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
run.mkdir(parents=True)
for name in ('PAPER.md','checks.py','CREDITED_INPUTS.json'):
    shutil.copyfile(base/name,run/name)
result={'utc':datetime.now(timezone.utc).isoformat(),'status':'RUNNING',
        'kind':'author finite exact/symbolic and arbitrary-precision diagnostics; no global optimizer computation',
        'source_hashes':{n:hashlib.sha256((base/n).read_bytes()).hexdigest()
                         for n in ('PAPER.md','checks.py','CREDITED_INPUTS.json')},'groups':{}}
def store(): (run/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
store()
try:
    credited=json.loads((base/'CREDITED_INPUTS.json').read_text())
    for rel,v in credited['files'].items():
        p=base/'credited-inputs'/rel
        assert hashlib.sha256(p.read_bytes()).hexdigest()==v['sha256']
    result['groups']['credited_inputs_literal']=len(credited['files'])

    z,a,beta,v=s.symbols('z a beta v')
    assert s.expand((z-a*v)+(beta-a)*(1-v)-(1+beta-a-(1-z+beta*v)))==0
    assert s.expand((z-a*v)+(a-beta)*v-(1-(1-z+beta*v)))==0
    H,m,r,T,Q0=s.symbols('H m r T Q0')
    b0=(H+1)*m;d=b0-H**2
    lhs=b0*(r*r+Q0)-2*H*r*T-H*(T*T-Q0)-d*r*r
    rhs=(H*r-T)**2+(H+1)*((m-1)*Q0-T*T)+(2*H+1)*Q0
    assert s.expand(lhs-rhs)==0
    result['groups']['exact_symbolic_identities']=3

    def raw_state(m,n,levels):
        D=m*n
        combined={}
        for x,k in levels:
            assert k>=0 and F(x)>=0
            if k:combined[F(x)]=combined.get(F(x),0)+k
        levels=sorted(combined.items(),reverse=True)
        assert sum(k for x,k in levels)==D
        tr=sum((x*k for x,k in levels),F(0));assert tr>0
        y=[(F(D)*x/tr,k) for x,k in levels]
        assert sum((x*k for x,k in y),F(0))==D
        Q=sum((k*(x-1)**2 for x,k in y),F(0))
        j=D-m*(m+1)//2+1
        count=0;pivot=None
        for x,k in y:
            if count<j<=count+k:pivot=x
            count+=k
        assert pivot is not None and pivot>0
        t=1/pivot;ell=y[-1][0];h=m-1
        vv=F(h*h,D)*max(F(0),t*t*Q-8)
        u=F(h)*t*ell
        assert F(0)<=ell<=1
        assert F(0)<=vv<=min(F(1),u)
        assert t*t*Q<=8+F(D,h*h)*min(F(1),u)
        assert abs(t-1)<=F(1,m)+F(2,m-1)
        return {'m':m,'n':n,'D':D,'y':y,'Q':Q,'t':t,'ell':ell,'v':vv}

    def negative(m,n,H,strength):
        D=m*n;k=D//2;b0=F((H+1)*m);p=F(H*H)
        assert p<=b0 and 0<=strength<=1 and k+1<=D
        return raw_state(m,n,[(b0+2*H*strength,k),(b0,D-k-1),(p,1)])

    states=[]
    for m in (3,4,8,16):
        for factor in (1,2,7):
            n=m*factor;D=m*n
            states += [raw_state(m,n,[(1,D)]),raw_state(m,n,[(1,D-1),(0,1)]),
                       raw_state(m,n,[(3,1),(1,D-1)]),
                       raw_state(m,n,[(1+F(2,m-1),D//2),(1,D-D//2)])]
            for strength in (F(0),F(1,2),F(1)):
                states.append(negative(m,n,1,strength))
    result['groups']['exact_actual_integer_spectrum_physical_bounds']=len(states)

    def mm(q):return mp.mpf(q.numerator)/q.denominator if isinstance(q,F) else mp.mpf(q)
    mp.mp.dps=180
    controls=0
    for st in states:
        for order in (F(1,100),F(1,7),F(1,2)):
            t,ell,vv=mm(st['t']),mm(st['ell']),mm(st['v'])
            al=mm(order);aa=mp.power((st['m']-1)*t,-al)
            zz=mp.power(ell,al) if ell else mp.mpf(0)
            bb=al*st['D']/(2*(st['m']-1)**2*t*t)
            Wt=1+max(0,bb-aa)
            losses=(zz-aa*vv,max(0,bb-aa)*(1-vv),max(0,aa-bb)*vv)
            assert min(losses)>-mp.mpf('1e-160')
            assert abs(sum(losses)-(Wt-(1-zz+bb*vv)))<mp.mpf('1e-150')
            exact_r=order*st['Q']/2-F(order*st['D'],2*(st['m']-1)**2)*st['v']/st['t']**2
            assert 0<=exact_r<=4*order/st['t']**2
            controls+=1
    result['groups']['nonnegative_loss_and_both_deflation_branches']=controls

    # Large D is never enumerated. Exact integer counts and rational trace,
    # pivot, variance and v are formed before any real-power diagnostics.
    continuum=[]
    for l in (2,4,8,16,24):
        m=l**(l*l);n=2*l*m
        for strength in (F(0),F(1,2),F(1)):
            st=negative(m,n,l,strength)
            digits=max(210,int(st['D'].bit_length()*0.302)+120)
            with mp.workdps(digits):
                al=mp.mpf(1)/(l*l);t=mm(st['t']);vv=mm(st['v'])
                zz=mp.power(mm(st['ell']),al)
                aa=mp.power((m-1)*t,-al)
                bb=al*st['D']/(2*(m-1)**2*t*t)
                Wt=1+max(0,bb-aa)
                loss=zz-aa*vv+max(0,bb-aa)*(1-vv)+max(0,aa-bb)*vv
                assert loss>=0 and loss<=Wt
                # Stable exact-trace centering, including every real nonzero term.
                centered=mp.fsum(k*(mp.expm1(al*mp.log(mm(y)))-al*(mm(y)-1))
                                 if y else k*(al-1) for y,k in st['y'])/st['D']
                De=-st['D']*mp.log1p(centered)/(1-al)
                W=mp.mpf(1) # canonical tie: m^-alpha=1/l, alpha*gamma=2/l
                assert abs(mp.log(m)*al-mp.log(l))<mp.mpf(10)**(-80)
                assert abs(mm(st['Q'])/(2*l)-mm(strength*strength))<mp.mpf(3)/l
                assert abs(De-(1-loss/Wt))<mp.mpf(20)/l
                continuum.append({'l':l,'strength':str(strength),'exact_integer_rank':True,
                                  'Q_over_gamma':mp.nstr(mm(st['Q'])/(2*l),25),
                                  'deflated_v':mp.nstr(vv,25),'least_power':mp.nstr(zz,25),
                                  'D_entropy_deficit':mp.nstr(De,25),
                                  'finite_uniform_loss_profile':mp.nstr(1-loss/Wt,25),
                                  'comparison':'W=1 on canonical tie; not actual finite optimal entropy'})
    result['groups']['actual_degenerate_tie_families']=continuum

    bad=[]
    def reject(name,fn):
        try:fn()
        except AssertionError:
            (run/(name+'.expected-trace.txt')).write_text(traceback.format_exc())
            bad.append({'name':name,'actual_expected_failure':'AssertionError'})
        else:raise AssertionError('Wrong variant was not rejected: '+name)
    def no_deflation():
        st=raw_state(8,8,[(1,63),(0,1)])
        z=F(0);a=F(1);v_bad=st['Q']/F(1)
        assert z-a*v_bad>=0
    def signed_deflation():
        st=raw_state(8,8,[(1,64)])
        assert F(7*7,64)*(st['t']**2*st['Q']-8)>=0
    def independent_feasibility():
        u=F(0);v=F(1,2)
        assert v<=min(F(1),u)
    def discrete_rule_at_collapsing_tie():
        # Proven asymptotic actual family, strength=1/2, has variance limit1/4.
        actual_limiting_pair=(F(0),F(1,4))
        assert actual_limiting_pair in {(F(0),F(0)),(F(0),F(1))}
    def omitted_normalization():
        m=8;n=32;H=2;D=m*n;k=D//2;b0=F((H+1)*m)
        raw=[(b0+2*H,k),(b0,D-k-1),(F(H*H),1)]
        assert sum(x*k for x,k in raw)==1
    def force_singular_positive_order():
        st=negative(16,64,2,F(1,2))
        assert st['ell']==0
    for name,fn in [('delete_deflation',no_deflation),('delete_positive_part',signed_deflation),
                    ('independent_hole_bulk_choices',independent_feasibility),
                    ('extend_discrete_tie_rule',discrete_rule_at_collapsing_tie),
                    ('omit_trace_normalization',omitted_normalization),
                    ('positive_order_implies_singular',force_singular_positive_order)]:reject(name,fn)
    result['groups']['actual_rejected_wrong_variants']=bad
    result['status']='PASS'
except Exception:
    result['status']='FAIL';result['unexpected_failure']=traceback.format_exc()
    store();raise
store()
print(json.dumps({'run':str(run),'status':result['status'],'groups':list(result['groups']),
                  'paper_sha256':result['source_hashes']['PAPER.md']}))
