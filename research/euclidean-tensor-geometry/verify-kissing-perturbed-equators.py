#!/usr/bin/env python3
"""All scalar inequalities in the perturbed-equator certificate; standard library."""
from fractions import Fraction as F
if not __debug__:raise RuntimeError('enable assertions')
for name,d,p,R2,den,lower in [
    ('A5',6,15,F(3,2),160,F(109,10000)),('D5',6,20,F(5,4),100,F(42,10000)),
    ('D6',7,30,F(3,2),360,F(92,10000)),('E6',7,36,F(4,3),260,F(37,10000))]:
    P={6:36,7:63}[d];q=P+1-p;c=F(3,4*P);z=F(1,den)
    a=F(1,2)+F(13,15)*z-z*z/4;u=2*R2*a*a
    T=F(p,d-1)*u*(a*a-F(1,4));b=max(F(1,2),2*u-1)
    f=b*b*(b*b-F(1,4));A=F(3*p,4)-c*p*p;B=q*(c*p-T)
    gap=c*q*q-F(3*q,4)-q*f+B*B/A
    assert u<=F(9,11) and A>0 and B>0 and gap>lower
    print(name,'chord tolerance 1/'+str(den),'strict gap >',lower)
# i+(j-i)*((sqrt(6)-i)/(L-i))^2 <= 9/4.
# Equivalently D + E*sqrt(6) >= 0 with E>=0.
for i in range(3):
    for j in range(3,7):
        L=j if j<6 else 4
        D=(F(9,4)-i)*(L-i)**2-(j-i)*(6+i*i)
        E=2*i*(j-i)
        assert D>=0 or 6*E*E>=D*D
        if i==0 and j==6:assert D==E==0
c=F(4,3*6)-F(1,9*6)-F(4,81)
assert c==F(25,162) and (1-F(1,9))*(1+F(2,3))**2==16*c
assert (1+15*F(1,9))/(F(2,3)+F(1,9))==F(24,7)
print('44-point covering edges and 15-per-side bound: PASS')
