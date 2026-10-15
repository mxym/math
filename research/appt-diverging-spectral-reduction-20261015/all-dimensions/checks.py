"""Finite author controls: exact physical integer spectra and scalar bridges, not M* sampling."""
from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction as F
import hashlib,json,shutil,traceback
import sympy as s
import mpmath as mp

base=Path(__file__).resolve().parent
run=base/'control-runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
run.mkdir(parents=True)
for name in ('PAPER.md','checks.py','CREDITED_INPUTS.json'):shutil.copyfile(base/name,run/name)
r={'utc':datetime.now(timezone.utc).isoformat(),'status':'RUNNING','groups':{},
   'kind':'author finite exact physical-spectrum/scalar controls; no global APPT optimizer computation',
   'source_hashes':{n:hashlib.sha256((base/n).read_bytes()).hexdigest() for n in ('PAPER.md','checks.py','CREDITED_INPUTS.json')}}
def store():(run/'RESULT.json').write_text(json.dumps(r,indent=2)+'\n')
store()
try:
    inputs=json.loads((base/'CREDITED_INPUTS.json').read_text())['files']
    for rel,v in inputs.items():
        p=(base/'credited-author-S9'/rel.split('/',1)[1] if rel.startswith('author-S9/') else
           base/'credited-X'/rel.split('/',1)[1] if rel.startswith('X/') else base/'credited-inputs'/rel)
        assert hashlib.sha256(p.read_bytes()).hexdigest()==v['sha256']
    r['groups']['literal_inputs']=len(inputs)
    k,a,theta,m=s.symbols('k a theta m',positive=True)
    eta=2*(m-2)*k*k/(2-(m-3)*k)
    assert s.factor(s.diff(eta,k)-2*(m-2)*k*(4-(m-3)*k)/(2-(m-3)*k)**2)==0
    assert s.factor(eta.subs(k,2/(m-1))-2*(m-2)/(m-1))==0
    zz=s.symbols('zz',positive=True);num=1+theta*((1+k)*zz-1);den=1+k*theta
    derivative=a*theta*zz/num-a*theta/den
    target=a*theta*(1-theta)*(zz-1)/(num*den)
    assert s.factor(derivative-target)==0
    r['groups']['exact_symbolic_identities']=3

    def state(m,n,raw,label):
        D=m*n;joined={}
        for val,count in raw:
            assert count>=0 and F(val)>=0
            if count:joined[F(val)]=joined.get(F(val),0)+count
        assert sum(joined.values())==D
        total=sum((v*c for v,c in joined.items()),F(0));assert total>0
        levels=sorted(((F(D)*v/total,c) for v,c in joined.items()),reverse=True)
        assert sum((y*c for y,c in levels),F(0))==D
        lo=max(2,m*(m-1)//2);hi=D-m*(m+1)//2+1;assert hi>=lo
        body=[];omitted=[];pos=1
        for y,count in levels:
            inside=max(0,min(pos+count-1,hi)-max(pos,lo)+1)
            if inside:body.append((y,inside))
            if count>inside:omitted.append((y,count-inside))
            pos+=count
        y1=levels[0][0];removed=[];peak_removed=False
        for y,count in omitted:
            c=count
            if not peak_removed and y==y1:c-=1;peak_removed=True
            if c:removed.append((y,c))
        assert peak_removed
        N=sum(c for y,c in body);A=body[-1][0];Ap=body[0][0]
        assert A>0 and N==(D-m*m+2 if m>=3 else D-3)
        mu=sum((y*c for y,c in body),F(0))/N
        width=Ap/A-1;th=(mu/A-1)/width if width else F(0)
        qe=sum((c*(y-1)**2 for y,c in omitted),F(0))
        assert 0<=th<=1 and 1<=y1<=F(3*D,D+2)
        if m>=3:
            # Actual finite unshifted-star consequence and pivot order bound.
            y2=levels[0][0] if levels[0][1]>=2 else levels[1][0]
            assert (y2/A-1)**2<=2
            assert A<=F(D,hi)
        else:
            assert sum(c for y,c in removed)==2
            assert max(y for y,c in removed)<=F(D,D-1)
        return dict(m=m,n=n,D=D,levels=levels,body=body,removed=removed,
                    N=N,A=A,mu=mu,kappa=width,theta=th,y1=y1,QE=qe,label=label)
    states=[]
    for m in (2,3,4,6):
        for factor in (1,3):
            n=m*factor;D=m*n;t=F(2,m-1)
            cases=[([(1,D)],'uniform'), ([(3,1),(1,D-1)],'peak'),
                   ([(1,D-1),(0,1)],'singular'), ([(1,D-1),(F(1,2),1)],'downward')]
            for rank in sorted({1,2,D//2,D-1}):
                cases.append(([(1+t,rank),(1,D-rank)],'projection-'+str(rank)))
            # Orthogonal projection+pure state, a+(m-1)c=2: actual APPT sufficiency.
            rank=D//3;c=F(1,m-1)
            cases.append(([(2,1),(1+c,rank),(1,D-rank-1)],'orthogonal-spike-body'))
            for raw,label in cases:states.append(state(m,n,raw,label))
    exact=0;constant_nonzero=0;nonzero_chord=0
    def H(y,p):return y**p-1-p*(y-1)
    for st in states:
        for p in (2,3,7,st['D']+3,3*st['D']+1):
            D=st['D'];M=sum((c*y**p for y,c in st['levels']),F(0))/D
            K=1+(H(st['y1'],p)+sum((c*H(y,p) for y,c in st['body']),F(0)))/D
            RE=sum((c*H(y,p) for y,c in st['removed']),F(0))
            assert M-K==RE/D and M>=K>=1
            kap,th,A,N=st['kappa'],st['theta'],st['A'],st['N']
            if kap:
                Zk=(1+kap)**p-1
                bodyraw=sum((c*y**p for y,c in st['body']),F(0))
                Lambda=1-(bodyraw/(N*A**p)-1)/(th*Zk)
                assert 0<=Lambda<=1
                nonzero_chord+=int(Lambda>0)
                bracket=A**p*(1+th*Zk*(1-Lambda))-1-p*(st['mu']-1)
            else:
                bracket=A**p-1-p*(st['mu']-1)
                constant_nonzero+=int(bracket>0)
            assert 1+(H(st['y1'],p)+N*bracket)/D==K
            assert RE<=2*st['QE']*p*p*(1+H(st['y1'],p))
            assert M<=(1+2*st['QE']*p*p)*K
            exact+=1
    r['groups']['actual_compressed_integer_states']=len(states)
    r['groups']['exact_centered_chord_and_polynomial_controls']=dict(cases=exact,
              constant_body_nonzero_kernel_cases=constant_nonzero,nonzero_chord_cases=nonzero_chord)

    mp.mp.dps=180
    def mm(q):return mp.mpf(q.numerator)/q.denominator if isinstance(q,F) else mp.mpf(q)
    real_cases=0
    for st in states[::4]:
        for p in (mp.mpf(17)/8,2+mp.sqrt(2),mp.mpf(st['D'])+mp.mpf('.25')):
            def hr(y):
                y=mm(y)
                return mp.power(y,p)-1-p*(y-1)
            M=mp.fsum(c*mp.power(mm(y),p) for y,c in st['levels'])/st['D']
            K=1+(hr(st['y1'])+mp.fsum(c*hr(y) for y,c in st['body']))/st['D']
            RE=mp.fsum(c*hr(y) for y,c in st['removed'])
            tol=mp.mpf('1e-140')*max(1,abs(M))
            assert abs(M-K-RE/st['D'])<=tol
            assert K>=1-tol and RE>=-tol
            assert RE<=2*mm(st['QE'])*p*p*(1+hr(st['y1']))+tol
            real_cases+=1
    r['groups']['noninteger_order_centered_and_actual_peak_controls']=real_cases
    def Fq(q,p):
        t=q-1;Q=mp.power(q,p)
        th=(Q-1-p*t)/(t*(p-1)*(Q-1))
        return (1+th*(Q-1))/mp.power(1+t*th,p),th
    lattice=[];sandwich=[]
    for m in (3,4,7):
        q=mp.mpf(m+1)/(m-1);t=q-1;delta=t/2
        for factor in (100,1000):
            D=m*factor;u=mp.mpf(3*D)/(D+2)
            for p in (mp.mpf(2),mp.mpf(10),mp.log(D),4*mp.log(D),mp.mpf(D)/4):
                if p<2:continue
                Fstar,th=Fq(q,p);R=mp.power(u,p)/D
                c=1-(2*(m-2)*delta**2/(2-(m-3)*delta))/3
                err=max(mp.power(1+delta,p)/Fstar,mp.power(c,p))
                sampled=[]
                for numerator in range(17):
                    k=t*numerator/16
                    if not k:vv=1+R
                    else:
                        eta=2*(m-2)*k*k/(2-(m-3)*k)
                        aa=1+R*mp.power(1-eta/3,p);bb=mp.power(1+k,p)-1
                        x=max(mp.mpf(0),min(mp.mpf(1),(bb-p*k*aa)/(k*bb*(p-1))))
                        vv=(aa+bb*x)/mp.power(1+k*x,p)
                    assert vv<=max(Fstar,R)*(1+err)*(1+mp.mpf('1e-150'))
                    sampled.append(vv)
                sandwich.append({'m':m,'D':D,'alpha':mp.nstr(p,18),
                                 'width_samples':17,'not_global_optimization':True})
                if p<=4*mp.log(D) and th>1/D:
                    rank=max(1,min(D-1,int(mp.floor(D*th+mp.mpf('.5')))))
                    x=mp.mpf(rank)/D
                    assert min(x,th)>=th/2
                    Fgrid=(1+x*(mp.power(q,p)-1))/mp.power(1+t*x,p)
                    loss=mp.log(Fstar/Fgrid)
                    bound=(4/th**2+p*t*t)/(8*D*D)
                    assert loss>=-mp.mpf('1e-150') and loss<=bound+mp.mpf('1e-145')
                    lattice.append({'m':m,'D':D,'alpha':mp.nstr(p,18),'actual_integer_rank':rank,
                                    'log_loss':mp.nstr(loss,20),'proved_local_Hessian_bound':mp.nstr(bound,20)})
    r['groups']['fixed_m_V_split_sampled_controls']=sandwich
    r['groups']['fixed_m_diverging_band_integer_lattice_controls']=lattice

    wrong=[]
    def reject(name,fn):
        try:fn()
        except AssertionError:
            (run/(name+'.expected-trace.txt')).write_text(traceback.format_exc())
            wrong.append({'name':name,'actual_expected_failure':'AssertionError'})
        else:raise AssertionError('False extension not rejected: '+name)
    def qubit_double_count():
        st=state(2,10,[(3,1),(1,19)],'peak');p=7
        M=sum(c*y**p for y,c in st['levels'])/st['D']
        body=sum(c*H(y,p) for y,c in st['body'])
        Kbad=1+(2*H(st['y1'],p)+body)/st['D']
        assert Kbad<=M
    def qubit_second_gap():
        st=state(2,100,[(3,2),(1,198)],'two-upper')
        assert st['y1']<=F(15,16)*F(600,202)
    def constant_body_is_one():
        st=state(3,9,[(3,1),(1,26)],'peak')
        assert st['kappa']==0 and H(st['mu'],7)==0
    def replace_calibrated_peak():
        D=20;p=400;u=F(3*D,D+2)
        assert F(3)**p/u**p<=2
    def logarithms_imply_moment_accuracy():
        # Scalar method countercontrol, not an APPT state claim.
        exact=mp.e**100;candidate=2*exact
        assert abs(mp.log(candidate)/mp.log(exact)-1)<mp.mpf('.01')
        assert abs(candidate/exact-1)<mp.mpf('.1')
    def tiny_excess_raw_ratio():
        # The actual maximally mixed state has M1 and zero entropy deficit.
        # The assigned positive scalar benchmark is illustrative, not a
        # computed finite-dimensional APPT optimum. The algebra fails at ANY
        # strictly positive true optimum excess, as the paper proves.
        actual=F(1);optimum=1+F(1,10**12)
        assert (actual-1)/(optimum-1)==1
    for name,fn in [('qubit_peak_double_count',qubit_double_count),('qubit_false_second_gap',qubit_second_gap),
                    ('constant_body_mean_erased',constant_body_is_one),('replace_u_by_three',replace_calibrated_peak),
                    ('log_accuracy_implies_sharp_moment',logarithms_imply_moment_accuracy),
                    ('raw_moment_near_one_as_excess',tiny_excess_raw_ratio)]:reject(name,fn)
    r['groups']['rejected_wrong_variants']=wrong
    r['status']='PASS'
except Exception:
    r['status']='FAIL';r['unexpected_failure']=traceback.format_exc();store();raise
store()
print(json.dumps({'run':str(run),'status':r['status'],'groups':list(r['groups']),
                  'paper_sha256':r['source_hashes']['PAPER.md']}))
