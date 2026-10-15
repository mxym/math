from pathlib import Path
import hashlib
import json
import sympy as sp

K,x,z,t=sp.symbols('K x z t',positive=True)
sf=sp.Function('s');rf=sp.Function('R')
delta=1-x;k=K*x
s=sf(k);ss=sp.diff(sf(t),t).subs(t,k);sss=sp.diff(sf(t),t,2).subs(t,k)
R=rf(k);Rp=sp.diff(rf(t),t).subs(t,k)
Y=2+delta**2*(3*s-2)
M=3*R*Y*delta**2+k*Y**2-9*k*ss*delta**4-12*x*delta
Yx=-2*delta*(3*s-2)+3*K*delta**2*ss
Mx=(3*(K*Rp*Y*delta**2+R*Yx*delta**2-2*R*Y*delta)
    +K*Y**2+2*k*Y*Yx-9*(K*ss*delta**4+k*K*sss*delta**4-4*k*ss*delta**3)-12*(1-2*x))
identities={'M_x':sp.simplify(sp.diff(M,x)-Mx)==0}
y=s+sp.Rational(2,3)*(delta**-2-1)
N=R*y+k*y*y-k*ss-sp.Rational(4,3)*x/delta**3
identities['M_scaled_log_derivative']=sp.factor(M-9*delta**4*N)==0

xx=1-K*z;kk=K*xx
ss0=sf(kk);sp0=sp.diff(sf(t),t).subs(t,kk);spp0=sp.diff(sf(t),t,2).subs(t,kk)
rr0=rf(kk);rp0=sp.diff(rf(t),t).subs(t,kk)
Z=sp.Rational(2,3)+K**2*z**2*(ss0-sp.Rational(2,3))
T=K*rr0*Z*z**2+xx*Z**2-K**4*xx*sp0*z**4-sp.Rational(4,3)*xx*z
Zz=2*K**2*z*(ss0-sp.Rational(2,3))-K**4*z**2*sp0
Tz=(K*(-K**2*rp0*Z*z**2+rr0*Zz*z**2+2*rr0*Z*z)
    -K*Z**2+2*xx*Z*Zz-K**4*(-K*sp0*z**4-K**2*xx*spp0*z**4+4*xx*sp0*z**3)
    -sp.Rational(4,3)*(xx-K*z))
identities['T_z']=sp.simplify(sp.diff(T,z)-Tz)==0
identities['two_charts_match']=sp.simplify(M.subs(x,xx)-9*K*T)==0
v,dd=sp.symbols('v dd',positive=True)
mid=M.subs({x:1-dd,K:v*dd},simultaneous=True)/dd
kmid=v*dd*(1-dd)
ymid=2+dd**2*(3*sf(kmid)-2)
mid_written=3*rf(kmid)*ymid*dd+v*(1-dd)*ymid**2-9*v*(1-dd)*sp.diff(sf(t),t).subs(t,kmid)*dd**4-12*(1-dd)
identities['middle_chart']=sp.simplify(mid-mid_written)==0
assert all(identities.values()),identities
source=Path(__file__)
out={'scope':'Author symbolic identity control, not independent review',
     'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'exact_identities':identities}
source.with_name('GLOBAL_TURN_ALGEBRA_CONTROL.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
