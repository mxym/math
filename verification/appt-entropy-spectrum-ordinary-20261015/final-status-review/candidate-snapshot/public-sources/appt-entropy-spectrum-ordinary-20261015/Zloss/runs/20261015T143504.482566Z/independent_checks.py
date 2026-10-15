"""Independent finite controls for the zero-order three-loss manuscript.
No author helper is imported or executed. Samples do not certify the
quantified all-APPT statement; that proof is reviewed separately.
"""
from pathlib import Path
from fractions import Fraction as F
import datetime,hashlib,json,platform,subprocess,sys,traceback
import sympy as sy
import mpmath as mp

R=Path(__file__).resolve().parent
mp.mp.dps=1250

def mm(q):
    return mp.mpf(q.numerator)/q.denominator if isinstance(q,F) else mp.mpf(q)

def state(m,n,raw):
    D=m*n; combined={}
    for level,count in raw:
        level=F(level)
        assert level>=0 and count>=0
        if count:combined[level]=combined.get(level,0)+count
    levels=sorted(combined.items(),reverse=True)
    assert sum(c for y,c in levels)==D
    Z=sum(c*y for y,c in levels); assert Z>0
    y=[(F(D)*raw/Z,c) for raw,c in levels]
    assert sum(c*v for v,c in y)==D
    Q=sum(c*(v-1)**2 for v,c in y)
    j=D-m*(m+1)//2+1; position=1; pivot=None
    for v,c in y:
        if position<=j<=position+c-1:pivot=v
        position+=c
    assert pivot is not None and pivot>0
    t=1/pivot;ell=y[-1][0];h=m-1
    vv=F(h*h,D)*max(F(0),t*t*Q-8)
    cap=min(F(1),h*t*ell)
    assert 0<=ell<=1 and 0<=vv<=cap
    assert t*t*Q<=8+F(D,h*h)*cap
    return dict(m=m,n=n,D=D,levels=y,trace=Z,Q=Q,t=t,ell=ell,v=vv,h=h,
                full_rank=ell>0)

def negative(m,n,H,strength):
    D=m*n;k=D//2;b0=(H+1)*m
    strength=F(strength)
    assert H>=1 and H*H<=b0 and 0<=strength<=1 and k<=D-1
    # The separately checked Schmidt SOS proves original APPT for all U.
    return state(m,n,[(F(b0)+2*H*strength,k),(b0,D-k-1),(H*H,1)])

def loss(st,alpha):
    al=mm(alpha); t=mm(st['t']);ell=mm(st['ell']);v=mm(st['v']);h=st['h'];D=st['D']
    a=mp.exp(-al*mp.log(h*t));z=mp.exp(al*mp.log(ell)) if ell else mp.mpf(0)
    beta=al*D/(2*h*h*t*t);Wt=1+max(beta-a,0)
    ls=[z-a*v,max(beta-a,0)*(1-v),max(a-beta,0)*v]
    bracket=1-z+beta*v
    assert min(ls)>=-mp.mpf('1e-1100')
    assert abs(sum(ls)-(Wt-bracket))<mp.mpf('1e-1100')
    assert 0<=bracket<=Wt+mp.mpf('1e-1100')
    return dict(z=z,a=a,beta=beta,Wt=Wt,L=sum(ls),profile=bracket/Wt)

def actual_De(st,alpha):
    al=mm(alpha)
    centered=mp.fsum(c*(mp.expm1(al*mp.log(mm(y)))-al*(mm(y)-1))
                      if y else c*(al-1) for y,c in st['levels'])/st['D']
    return -st['D']*mp.log1p(centered)/(1-al)

def canonical(l,strength):
    m=l**(l*l);return negative(m,2*l*m,l,strength)

def wrong(name):
    if name=='undeﬂated_variance':
        st=state(8,8,[(1,63),(0,1)])
        alpha=F(1,2);a=mp.exp(-mm(alpha)*mp.log(st['h']*mm(st['t'])))
        rawv=F(st['h']**2,st['D'])*st['t']**2*st['Q']
        assert -a*mm(rawv)>=0,'WRONG undeﬂated_variance'
    elif name=='signed_variance':
        st=state(8,8,[(1,64)])
        assert F(st['h']**2,st['D'])*(st['t']**2*st['Q']-8)>=0,'WRONG signed_variance'
    elif name=='drop_upper_phase_loss':
        z=mp.mpf(0);a=mp.mpf('.25');beta=mp.mpf(4);v=mp.mpf(0)
        wrongL=z-a*v
        assert 1-wrongL/(1+beta-a)==(1-z+beta*v)/(1+beta-a),'WRONG drop_upper_phase_loss'
    elif name=='drop_lower_phase_loss':
        z=mp.mpf('.5');a=mp.mpf('.5');beta=mp.mpf('.1');v=mp.mpf(1)
        wrongL=z-a*v
        assert 1-wrongL==(1-z+beta*v),'WRONG drop_lower_phase_loss'
    elif name=='finite_tie_rule_at_zero_corner':
        st=canonical(16,F(1,2));q=mm(st['Q'])/32
        assert min(abs(q),abs(q-1))<mp.mpf('.05'),'WRONG finite_tie_rule_at_zero_corner'
    elif name=='positive_order_forces_zero_rank':
        st=canonical(16,F(1,2))
        assert st['ell']==0,'WRONG positive_order_forces_zero_rank'
    elif name=='ignore_normalization':
        m=8;n=40;D=m*n;H=2;b0=24;k=D//2
        trace=k*(b0+2*H)+(D-k-1)*b0+H*H
        assert trace==1,'WRONG ignore_normalization'
    else:raise ValueError(name)

def run_checks(folder):
    counts={};data={}
    z,a,b,v,al,Q,t,D,h=sy.symbols('z a b v al Q t D h')
    assert sy.expand((z-a*v)+(b-a)*(1-v)-(1+b-a-(1-z+b*v)))==0
    assert sy.expand((z-a*v)+(a-b)*v-(1-(1-z+b*v)))==0
    beta=al*D/(2*h*h*t*t);vactive=h*h*(t*t*Q-8)/D
    assert sy.cancel(al*Q/2-beta*vactive-4*al/t**2)==0
    H,m,r,T,Q0=sy.symbols('H m r T Q0')
    b0=(H+1)*m;d=b0-H*H
    lhs=b0*(r*r+Q0)-2*H*r*T-H*(T*T-Q0)-d*r*r
    rhs=(H*r-T)**2+(H+1)*((m-1)*Q0-T*T)+(2*H+1)*Q0
    assert sy.expand(lhs-rhs)==0
    kap,p=sy.symbols('kap p');tt=1+kap/2-(1-p)/D
    raw2=D*(1+kap)**2/2+(D/2-1)+p*p
    assert sy.expand(raw2-D*tt**2-(D*kap**2/4+(1-p)*kap+(1-p)**2*(1-1/D)))==0
    counts['exact_symbolic_identities']=5

    states=[]
    for m in [3,5,12,37]:
        for n in [m,m+3,7*m+1]:
            D=m*n
            states.extend([state(m,n,[(1,D)]),state(m,n,[(1,D-1),(0,1)]),
                           state(m,n,[(3,1),(1,D-1)]),
                           state(m,n,[(1+F(2,m-1),D//3),(1,D-D//3)]),
                           negative(m,n,1,F(1,3)),negative(m,n,int(m**.5),F(3,4)),
                           negative(m,n,int(m**.5),F(1))])
    counts['exact_actual_compressed_integer_states']=len(states)
    tested=0; both={'active':0,'inactive':0}
    for st in states:
        for alpha in [F(1,2),F(1,9),F(1,128),F(1,10**1000)]:
            x=loss(st,alpha)
            remainder=alpha*st['Q']/2-F(alpha*st['D'],2*st['h']**2)*st['v']/st['t']**2
            assert 0<=remainder<=4*alpha/st['t']**2
            both['active' if st['t']**2*st['Q']>8 else 'inactive']+=1
            de=actual_De(st,alpha)
            assert de>=-mp.mpf('1e-1100')
            if st['ell']==0:
                assert not st['full_rank'] and st['v']==0
                expected=st['D']*mp.log1p(mp.mpf(1)/(st['D']-1))
                assert abs(de-expected)<mp.mpf('1e-1100')
            tested+=1
    assert min(both.values())>0
    counts['loss_deflation_and_actual_entropy_cases_including_alpha_1e_1000']=tested
    data['deflation_branches']=both

    continuum=[]
    for l in [2,4,8,16,32]:
        for strength in [F(0),F(1,3),F(1,2),F(3,4),F(1)]:
            st=canonical(l,strength)
            digits=max(1250,int(st['D'].bit_length()*.302)+150)
            with mp.workdps(digits):
                alpha=F(1,l*l);x=loss(st,alpha);de=actual_De(st,alpha)
                q=mm(st['Q'])/(2*l); vv=mm(st['v']);target=mm(strength*strength)
                assert abs(q-target)<=mp.mpf(3)/l
                assert abs(vv-target)<=mp.mpf(7)/l
                assert abs(de-1)<=mp.mpf(3)/l
                assert abs(de-x['profile'])<=mp.mpf(10)/(l*l)
                # Exact canonical tie and actual integer ranks, not approximate dimensions.
                assert alpha*F(st['n'],st['m'])==F(2,l)
                assert st['D']%2==0 and st['full_rank']
                assert st['D']//2<st['D']-st['m']*(st['m']+1)//2+1<=st['D']-1
                continuum.append({'l':l,'strength':str(strength),'variance_target':str(strength*strength),
                    'Q_over_gamma':mp.nstr(q,25),'v':mp.nstr(vv,25),'least_power':mp.nstr(x['z'],25),
                    'D_entropy':mp.nstr(de,25),'relative_loss_profile':mp.nstr(x['profile'],25),
                    'mp_dps':digits,'full_rank':True,'rank_zero_entropy_deficit':0,
                    'scope':'Known asymptotic scale W=1, not a finite exact optimum'})
    counts['actual_collapsing_tie_examples']=len(continuum);data['collapsing_tie']=continuum

    corners=[]
    for l in [4,8,16]:
        m=l**(l*l);alpha=F(1,l*l)
        for gamma in [1,2*l,l*l,l*l*l]:
            for strength in [F(0),F(1,2),F(1)]:
                st=negative(m,gamma*m,l,strength)
                digits=max(1250,int(st['D'].bit_length()*.302)+150)
                with mp.workdps(digits):
                    x=loss(st,alpha);de=actual_De(st,alpha)
                    W=max(mp.mpf(1),1-mp.mpf(1)/l+mm(alpha)*gamma/2)
                    assert abs(de/W-x['profile'])<mp.mpf(10)/(l*l)
                    corners.append({'l':l,'gamma':gamma,'strength':str(strength),
                                    'D_entropy_over_known_W':mp.nstr(de/W,20),
                                    'loss_profile':mp.nstr(x['profile'],20)})
    counts['other_degenerate_corner_actual_diagnostics']=len(corners);data['other_corners']=corners

    bad=[]
    for name in ['undeﬂated_variance','signed_variance','drop_upper_phase_loss',
                 'drop_lower_phase_loss','finite_tie_rule_at_zero_corner',
                 'positive_order_forces_zero_rank','ignore_normalization']:
        p=subprocess.run([sys.executable,str(Path(__file__).resolve()),'--wrong',name],capture_output=True,text=True)
        (folder/(name+'.stdout.txt')).write_text(p.stdout)
        (folder/(name+'.stderr.txt')).write_text(p.stderr)
        assert p.returncode!=0 and 'AssertionError: WRONG '+name in p.stderr,(name,p.returncode,p.stderr)
        bad.append({'variant':name,'returncode':p.returncode,'intended_assertion_error':True})
    return counts,data,bad

def main():
    utc=datetime.datetime.now(datetime.timezone.utc)
    folder=R/'runs'/utc.strftime('%Y%m%dT%H%M%S.%fZ');folder.mkdir(parents=True)
    source=Path(__file__).read_bytes();(folder/'independent_checks.py').write_bytes(source)
    result={'utc':utc.isoformat(),'status':'RUNNING','source_sha256':hashlib.sha256(source).hexdigest(),
            'paper_sha256':'5b1fa3732ec3dd2448e0cf5c54a79e321b08928aeaf9c7fbd6bd6f61e56c2602',
            'runtime':{'python':platform.python_version(),'sympy':sy.__version__,'mpmath':mp.__version__,'initial_mp_dps':mp.mp.dps},
            'author_programs_imported_or_executed':False,'scope':'Independent finite controls, not global APPT optimization or quantified proof'}
    try:
        counts,data,bad=run_checks(folder)
        result.update(status='PASS',counts=counts,details=data,actual_rejected_wrong_variants=bad)
    except Exception:
        result.update(status='FAIL',unexpected_failure=traceback.format_exc())
        (folder/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
        raise
    result['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    (folder/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    (R/'LATEST_RUN.json').write_text(json.dumps({'run':str(folder),'source_sha256':result['source_sha256']},indent=2)+'\n')
    print(json.dumps({'status':'PASS','run':str(folder),'counts':counts,'rejected_variants':len(bad)},indent=2))

if __name__=='__main__':
    if len(sys.argv)==3 and sys.argv[1]=='--wrong':wrong(sys.argv[2])
    else:main()
