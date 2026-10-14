"""Reviewer-created ordinary controls. No author script or Lean is imported."""
from pathlib import Path
from fractions import Fraction as F
from datetime import datetime, timezone
import hashlib, json, sys, traceback
import sympy as s
import mpmath as mp

OUT=Path(__file__).resolve().parent
ROOT=OUT.parent
REPO=Path('/home/mxym/math-appt-multiscale-20261013/research')
mp.mp.dps=180
checks=[]
def add(kind,name,ok,data=None):
    checks.append(dict(kind=kind,name=name,passed=bool(ok),data=data))
    if not ok:
        raise AssertionError(name)
def h(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot():
    files=[]
    for name,expected in [('PAPER.md','f0a38d5e994dfdb3b0b2ef810b04c1f9e0db565d9afe6e72a7b86153b4f8661c'),('THEOREM_MAP.md','cd8187d302640d8bcfd899a34a54c03000f117010cd9673776924e672e26d98f')]:
        p=ROOT/name
        add('binding','initial_'+name,h(p)==expected,dict(actual=h(p),expected=expected))
        b=p.read_bytes(); (OUT/('SNAPSHOT_'+name)).write_bytes(b)
        files.append(dict(path=str(p),sha256=h(p),lines=len(b.decode().splitlines()),reviewed_lines='all'))
    for stage in ['appt-critical-purity-optimizer-20261014','appt-exact-purity-onset-20261014']:
        p=REPO/stage/'PAPER.md'
        b=p.read_bytes(); (OUT/('DEPENDENCY_'+stage+'_PAPER.md')).write_bytes(b)
        files.append(dict(path=str(p),sha256=h(p),lines=len(b.decode().splitlines()),reviewed_lines='all',role='credited prior ordinary result, not re-reviewed formal certificate'))
    return files

def symbolic():
    m,n,z,a,u,kk=s.symbols('m n z a u k', positive=True)
    D=m*n; t=2/(m-1); kap=2/(m-1+z); aa=2+kap; p=aa*z/(z+2)
    c=m*m*(t-kap); b=(m*m-1)/(4*m**3); B=D*(1+kap)-kap*p-p*p
    V=p*p+kap*p-(n/m**2)*(c-b*c*c)
    R=(2+t)**2/(4*(1+t)*(1+kap-(kap*p+p*p)/D))
    Pb=aa*aa/(4*B); PGreal=(2+t)**2/(4*D*(1+t))
    add('symbolic','exact_RV_trace_comparison',s.cancel(D*D*(Pb-PGreal)-R*V)==0)
    S=D+kap*kk+p; Sstar=2*B/aa
    PQ=(D+(2*kap+kap*kap)*kk+2*(1+kap)*p+p*p)/S**2
    # Verify the same identity after clearing denominators in abstract a,B,S;
    # then verify the physical chord separately. Expanding substituted rational
    # denominators directly made the initial SymPy run unnecessarily slow.
    ax,bx,sx,dx,kx,px,jx=s.symbols('a0 B0 S0 D0 kappa0 p0 j0')
    add('symbolic','exact_integer_trace_loss',s.expand(ax*ax*sx*sx-4*bx*(ax*sx-bx)-ax*ax*(sx-2*bx/ax)**2)==0)
    add('symbolic','physical_chord_identity',s.expand((2+kx)*(dx+kx*jx+px)-(dx*(1+kx)-kx*px-px*px)-(dx+(2*kx+kx*kx)*jx+2*(1+kx)*px+px*px))==0)
    kstar=(Sstar-D-p)/kap
    add('symbolic','exact_continuous_rank',s.expand(2*(dx*(1+kx)-kx*px-px*px)-(2+kx)*(dx+px)-(dx*kx-px*(2+kx+2*kx+2*px)))==0)
    add('symbolic','rank_base_shift',s.cancel(D/aa-(m-1)*n/2-n*z/(2*(m+z)))==0)
    tu=2*u/(1-u); ku=2*u/(1+(z-1)*u); au=2+ku; pu=au*z/(z+2)
    cu=2*z/((1-u)*(1+(z-1)*u)); bu=(u-u**3)/4; delta=s.Rational(1,4)+a*u
    Vu=pu*pu+ku*pu-delta*(cu-bu*cu*cu)
    Ru=(2+tu)**2/(4*(1+tu)*(1+ku-(ku*pu+pu*pu)*u**3/delta))
    rc=[s.factor(s.diff(Ru,u,i).subs(u,0)/s.factorial(i)) for i in range(3)]
    vc=[s.factor(s.diff(Vu,u,i).subs(u,0)/s.factorial(i)) for i in range(3)]
    fc=[s.factor(sum(rc[j]*vc[i-j] for j in range(i+1))) for i in range(3)]
    add('symbolic','R_coefficients',rc==[s.Integer(1),s.Integer(-2),2*z+3],[str(x) for x in rc])
    add('symbolic','f0_entire_rational',s.cancel(fc[0]+z*(z-2)**2/(2*(z+2)**2))==0,str(fc[0]))
    f0pp=s.diff(fc[0],z,2).subs(z,2)
    f1at=fc[1].subs(z,2); f1p=s.diff(fc[1],z).subs(z,2); f2at=fc[2].subs(z,2)
    add('symbolic','four_coefficients_at_2',all(s.cancel(x-y)==0 for x,y in zip([f0pp,f1at,f1p,f2at],[s.Rational(-1,8),5-4*a,s.Rational(7,2)-2*a,12*a-12])),[str(x) for x in [f0pp,f1at,f1p,f2at]])
    shift=s.factor(-f1p/f0pp)
    fmax2=s.factor(f2at-f1p*f1p/(2*f0pp))
    add('symbolic','stationary_shift_and_max_second_coefficient',s.cancel(shift-(28-16*a))==0 and s.cancel(fmax2-(16*a*a-44*a+37))==0,dict(shift=str(shift),second=str(fmax2)))
    add('symbolic','head_and_protection_rates',s.diff(pu.subs(z,2+shift*u),u).subs(u,0)==8-4*a and s.cancel(s.diff(cu.subs(z,2+shift*u),u).subs(u,0)-(56-32*a))==0)
    add('symbolic','constant_control_not_missing_displacement',s.cancel(fmax2.subs(a,s.Rational(5,4))-7)==0 and s.cancel(f2at.subs(a,s.Rational(5,4))-7)!=0)
    wrong_extensive=pu*pu+ku*pu-delta*cu
    add('symbolic','retained_c_centering_contributes',s.cancel(s.diff((Vu-wrong_extensive),u).subs(u,0)-z*z/4)==0)
    return dict(f=[str(v) for v in fc],R=[str(v) for v in rc])

def exact_fraction():
    cases=[]
    for m in [64,127,128,255,256,1023]:
        onset=(m*m+5*m+7+3)//4
        for n in [onset-2,onset-1,onset,onset+1]:
            D=m*n; t=F(2,m-1); H=n*(m*m-1); qbase=F((m-1)*n,2)
            qrank=(qbase.numerator+qbase.denominator-1)//qbase.denominator
            qval=(D+(2*t+t*t)*qrank)/(D+t*qrank)**2
            Pb=(2+t)**2/(4*D*(1+t))
            qloss=F(0) if ((m-1)*n)%2==0 else F(m,H*(H+1)**2)
            add('Fraction','q_exact_parity_m{}_n{}'.format(m,n),Pb-qval==qloss)
            for zz in [F(1),F(2),F(3),F(2)+F(8,m)]:
                kap=F(2,m-1+zz); aa=2+kap; p=aa*zz/(zz+2)
                c=m*m*(t-kap); b=F(m*m-1,4*m**3)
                B=D*(1+kap)-kap*p-p*p; Sstar=2*B/aa
                kstar=(Sstar-D-p)/kap; lo=kstar.numerator//kstar.denominator; hi=lo+(kstar.denominator!=1)
                vals=[]
                for k in [lo,hi]:
                    S=D+kap*k+p
                    v=(D+(2*kap+kap*kap)*k+2*(1+kap)*p+p*p)/S**2
                    loss=aa*aa*(S-Sstar)**2/(4*B*S*S)
                    add('Fraction','one_exact_normalization_m{}_n{}_z{}_k{}'.format(m,n,zz,k),aa*aa/(4*B)-v==loss)
                    vals.append(v)
                R=(2+t)**2/(4*(1+t)*(1+kap-(kap*p+p*p)/D))
                V=p*p+kap*p-F(n,m*m)*(c-b*c*c)
                add('Fraction','exact_RV_m{}_n{}_z{}'.format(m,n,zz),D*D*(aa*aa/(4*B)-Pb)==R*V)
                # All edge placements are permutation congruent; rank-one PSD criterion is exact.
                add('Fraction','actual_boundary_PSD_m{}_z{}'.format(m,zz),p<aa and kap*F(m+zz,aa)==1)
                add('Fraction','physical_rank_counts_m{}_n{}_z{}'.format(m,n,zz),m*(m-1)//2<=lo<=hi<=D-m*(m+1)//2)
                if zz==F(2)+F(8,m) and n==onset-1 and m>=127:
                    add('Fraction','actual_lower_beyond_trial_onset_m{}'.format(m),max(vals)>Pb>=qval)
                cases.append(dict(m=m,n=n,z=str(zz),qrank=qrank,rank_candidates=[lo,hi],scaled_integer_loss=str(D*D*(aa*aa/(4*B)-max(vals))),genuine_one_head_beats_q=max(vals)>qval))
    # Reviewer independently retains the forbidden all-small-m extension.
    add('Fraction','reject_all_m_onset_extension_m3n8',F(32,676)>F(3,64))
    return cases

def numerical():
    rows=[]
    def values(m,n,z):
        D=mp.mpf(m)*n; t=mp.mpf(2)/(m-1); kap=2/(m-1+z); aa=2+kap; p=aa*z/(z+2)
        B=D*(1+kap)-kap*p-p*p
        qb=(2+t)**2/(4*D*(1+t)); pb=aa*aa/(4*B)
        c=m*m*(t-kap); b=mp.mpf(m*m-1)/(4*m**3)
        R=(2+t)**2/(4*(1+t)*(1+kap-(kap*p+p*p)/D)); V=p*p+kap*p-mp.mpf(n)/(m*m)*(c-b*c*c)
        return R*V,kap,p,c,B,aa,D,qb,pb
    for m in [256,1024,4096,16384]:
        for desired in [-3,-1,0,1,mp.mpf(5)/4,2,3]:
            n=int(mp.nint(mp.mpf(m*m)/4+desired*m)); a=(mp.mpf(n)-mp.mpf(m*m)/4)/m
            shift=28-16*a
            f=lambda z: values(m,n,z)[0]
            zc=mp.findroot(lambda z: mp.diff(f,z),(mp.mpf(2)+shift/m-mp.mpf('0.1'),mp.mpf(2)+shift/m+mp.mpf('0.1')))
            val,kap,p,c,B,aa,D,qb,pb=values(m,n,zc)
            Sstar=2*B/aa; kstar=(Sstar-D-p)/kap
            choices=[int(mp.floor(kstar)),int(mp.ceil(kstar))]
            qrank=((m-1)*n+1)//2
            t=mp.mpf(2)/(m-1)
            pg=(D+(2*t+t*t)*qrank)/(D+t*qrank)**2
            actual=max((D+(2*kap+kap*kap)*k+2*(1+kap)*p+p*p)/(D+kap*k+p)**2 for k in choices)
            pred=(5-4*a)/m+(16*a*a-44*a+37)/(m*m)
            # A scalar sample at continuous zc is an ACTUAL lower, not a computed whole-set oracle.
            sampled=max(pg,actual)
            scaled_sample=D*D*(sampled-pg)
            add('mp180','exact_RV_numeric_m{}_a{}'.format(m,a),abs(val-D*D*(pb-qb))<mp.mpf('1e-140'))
            add('mp180','stationary_interior_negative_curvature_m{}_a{}'.format(m,a),1<zc<3 and mp.diff(f,zc,2)<mp.mpf('-0.01'))
            add('mp180','finite_cubic_remainder_control_m{}_a{}'.format(m,a),abs(val-pred)*m**3<mp.mpf('50000'))
            add('mp180','integer_gap_scale_m{}_a{}'.format(m,a),0<=D*D*(pb-actual)*m**5<mp.mpf('10'))
            H=n*(m*m-1)
            qexact=mp.mpf(0) if ((m-1)*n)%2==0 else D*D*m/(mp.mpf(H)*(H+1)**2)
            # The exactly zero even-parity loss can round to a tiny negative
            # number when two separately evaluated MP expressions subtract.
            add('mp180','q_gap_scale_m{}_a{}'.format(m,a),abs(D*D*(qb-pg)-qexact)<mp.mpf('1e-130') and 0<=qexact*m**5<mp.mpf('10'),dict(exact_scaled_loss=str(qexact),numeric_residual=str(D*D*(qb-pg)-qexact)))
            add('mp180','uniform_stationary_displacement_m{}_a{}'.format(m,a),abs(zc-2-shift/m)*m*m<mp.mpf('10000'))
            add('mp180','positive_part_sample_control_m{}_a{}'.format(m,a),abs(scaled_sample-max(0,pred))*m**3<mp.mpf('50000'))
            add('mp180','optimizing_head_c_rank_rates_sample_m{}_a{}'.format(m,a),abs(p-1-(8-4*a)/m)*m*m<mp.mpf('10000') and abs(c-4-(56-32*a)/m)*m*m<mp.mpf('100000') and max(abs(k-mp.mpf((m-1)*n)/2+mp.mpf(3)*m/4) for k in choices)<mp.mpf('1000'))
            rows.append(dict(m=m,n=n,a=str(a),zc=str(zc),scaled_continuous=str(val),cubic_remainder=str((val-pred)*m**3),integer_gap_m5=str(D*D*(pb-actual)*m**5),q_gap_m5=str(D*D*(qb-pg)*m**5),scaled_actual_sample=str(scaled_sample),positive_part_prediction=str(max(0,pred))))
    return rows

start=datetime.now(timezone.utc).isoformat()
report=dict(start=start,reviewer_script_sha256=h(Path(__file__)),versions=dict(Python=sys.version,Sympy=s.__version__,mpmath=mp.__version__,mp_digits=mp.mp.dps),author_scripts_executed=False,Lean_executed=False)
try:
    report['sources']=snapshot()
    report['symbolic_coefficients']=symbolic()
    report['fraction_cases']=exact_fraction()
    report['numeric_rows']=numerical()
    report['result']='PASS'
except BaseException as exc:
    report['result']='INTERRUPTED' if isinstance(exc,KeyboardInterrupt) else 'FAIL'
    report['error']=repr(exc); report['traceback']=traceback.format_exc()
finally:
    report['checks']=checks; report['counts']={k:sum(x['kind']==k for x in checks) for k in sorted({x['kind'] for x in checks})}
    report['finish']=datetime.now(timezone.utc).isoformat()
    dest=OUT/('RUN_'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')+'.json')
    dest.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(dict(report=str(dest),result=report.get('result'),counts=report['counts'],error=report.get('error')),indent=2))
    if report['result']!='PASS': sys.exit(1)
