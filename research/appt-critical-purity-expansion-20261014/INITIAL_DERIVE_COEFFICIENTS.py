from pathlib import Path
import json
import sympy as s

u,z,a,h=s.symbols('u z a h')
t=2*u/(1-u)
kap=2*u/(1+(z-1)*u)
p=(2+kap)*z/(z+2)
c=2*z/((1-u)*(1+(z-1)*u))
b=(u-u**3)/4
delta=s.Rational(1,4)+a*u
d=delta/u**3
v=p*p+kap*p-delta*(c-b*c*c)
r=(2+t)**2/(4*(1+t)*(1+kap-(kap*p+p*p)/d))
vs=s.series(v,u,0,3).removeO().expand()
rs=1-2*u+(2*z+3)*u*u
fs=s.expand(vs*rs)
f=[s.factor(fs.coeff(u,j)) for j in range(3)]
assert s.cancel(f[0]+z*(z-2)**2/(2*(z+2)**2))==0
assert s.diff(f[0],z,2).subs(z,2)==-s.Rational(1,8)
assert s.simplify(f[1].subs(z,2))==5-4*a
assert s.simplify(s.diff(f[1],z).subs(z,2))==s.Rational(7,2)-2*a
assert s.simplify(f[2].subs(z,2))==12*a-12
second=s.expand(f[2].subs(z,2)+4*(s.Rational(7,2)-2*a)**2)
assert second==16*a*a-44*a+37
assert second.subs(a,s.Rational(5,4))==7
assert s.series(r,u,0,3).removeO().expand()==rs
report={'status':'PASS_EXACT_SYMBOLIC_EXPLORATION','sympy':s.__version__,
        'F0':str(f[0]),'F1_at_2':str(s.simplify(f[1].subs(z,2))),
        'F1_prime_at_2':str(s.simplify(s.diff(f[1],z).subs(z,2))),
        'F2_at_2':str(s.simplify(f[2].subs(z,2))),'optimized_second':str(second),
        'scope':'Exact coefficient calculation; not a full-domain proof or independent review'}
Path('EXPLORATORY_COEFFICIENTS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
