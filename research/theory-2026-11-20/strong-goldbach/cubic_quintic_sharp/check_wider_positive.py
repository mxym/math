#!/usr/bin/env python3
"""Exact rational DHR/linear positive intersection on the .123 rough floor."""
from fractions import Fraction as F
S=10**14
def req(ok,why):
    if not ok:raise ArithmeticError(why)
def ce(n,d):return (n+d-1)//d

# DHR F_2 decreasing; v is rounded downward. For grid i/JQ the
# Dickman2 denominator at (i/JQ)/2 is exactly at tick i below.
a=F(".123"); theta=F(".499")
JQ=10000; DX=2*JQ; AL=53577;AH=53578;BL=42664;BH=42665
v0=F(".999")/a; nv=v0.numerator*JQ//v0.denominator
req(nv>AH,"true DHR branch")
v=F(nv,JQ)
rrlo=[S]*(DX+1); rrhi=rrlo.copy()
for i in range(DX,nv):
    rrlo.append(max(0,rrlo[-1]-ce(2*(i+1-DX)*rrhi[i-DX],i*i)))
    rrhi.append(max(0,rrhi[-1]-2*(i-DX)*rrlo[i+1-DX]//((i+1)**2)))
    req(rrlo[-1]<=rrhi[-1],"Dickman-2 enclosure")
glo=[0];ghi=[0]
for j in range(nv):
    glo.append(glo[-1]+(2*j+1)*rrlo[j+1])
    ghi.append(ghi[-1]+(2*j+1)*rrhi[j])
Alo=[0]*(nv+1); Ahi=Alo.copy(); Blo=Alo.copy(); Bhi=Alo.copy()
# In units S, A(u)=u²/G(u/2); the G-tick denominator 2 DX²S is exact.
for j in range(2,AL+1):
    num=j*j * 2*DX*DX*S*S
    Alo[j]=num//(JQ*JQ*ghi[j])
    Ahi[j]=ce(num,JQ*JQ*glo[j])
Alo[AH]=Alo[AL]
Ahi[AH]=ce(AH**2*2*DX*DX*S*S,JQ**2*glo[AL])
for j in range(BL,nv):
    k=j-JQ
    Blo[j+1]=Blo[j]+(0 if j< BH else 2*j*Alo[k]//(k+1)**2)
    Bhi[j+1]=Bhi[j]+ce(2*(j+1)*Ahi[k+1],k*k)
    if j>=AH:
        Alo[j+1]=Alo[j]+2*j*Blo[k]//(k+1)**2
        Ahi[j+1]=Ahi[j]+ce(2*(j+1)*Bhi[k+1],k*k)
    req(Alo[j+1]<=Ahi[j+1] and Blo[j+1]<=Bhi[j+1],"DHR delay enclosure")
C=F(Ahi[nv],S)/(v*v*a*a)
B_amb=F(Blo[nv],S)/(v*v*a*a)

# Linear lower: B_1=s e^-gamma f_1(s), A_1=s e^-gamma F_1(s).
# Need only lower ticks, using monotone delayed numerators.
s0=theta/a; ns=s0.numerator*JQ//s0.denominator
A=[2*S]*(3*JQ+1)+[0]*ns
B=[0]*(ns+1)
A2=A.copy(); B2=B.copy()
for j in range(2*JQ,ns):
    k=j-JQ
    B[j+1]=B[j]+A[k]//(k+1)
    B2[j+1]=B2[j]+ce(A2[k+1],k)
    if j>=3*JQ:
        A[j+1]=A[j]+B[k]//(k+1)
        A2[j+1]=A2[j]+ce(B2[k+1],k)
k=F(B[ns],S)/(F(ns,JQ)*a)
U=F(A2[ns],S)/(F(ns,JQ)*a)
aa=1230; H=10000; allm=0
prefix=None
for j in range(1,9):
    row=[0]*(j*aa)
    for i in range(j*aa,H+1):
        row.append(ce(H*S,i) if j==1 else ce(prefix[i-aa+1],i))
    allm+=row[-1]
    prefix=[0]
    for x in row:prefix.append(prefix[-1]+x)
Mass=F(allm,S)

# Positive rank2/3 angular layers: fixed strictly ordered interior boxes.
P=1000; floor=123; R=200; den=P**5
req(F(floor,P)==a and (1-2*a)**2+2*a*a<F(".6"),"true ranks positive")
def pp(i):
    z=P-2*i
    return 2*z**3*P**2-z**5
psi=[pp(i) for i in range(P+1)]
mass=[0]*(R+1)
n2=n3=0
def inject(score,weight):
    i=min(R,(score*R-1)//den)
    if i>0:mass[i]+=weight
for i in range(floor,P//2):
    inject(den-psi[i],P*S//((i+1)*(P-i)))
    n2+=1
for i in range(floor,P//3+1):
    for j in range(i+1,(P-i-3)//2+1):
        w=P-i-j
        inject(den-psi[i]-psi[j]-psi[w-2],P*S//((i+1)*(j+1)*w))
        n3+=1
means=[F(sum(mass[i:]),S) for i in range(1,R+1)]
credit=sum(max(0,k*(u+v)-C) for u in means for v in means)/R**2
full=sum(max(0,k*(u+v)-C,B_amb-U*(2*Mass-u-v)) for u in means for v in means)/R**2
print("actual complement upper U, lower ambient, ordinary rough upper",float(U),float(B_amb),float(Mass),"enhanced",float(full))
print("DHR common ambient, true linear marginal:",float(C),float(k))
print("actual rank2/3 box counts:",n2,n3)
print("marginal-lower-only:",float(credit))
print("true positive lower and new reserve:",float(full),float(full-F(".493039")))
req(C<F("20.881873") and B_amb>F("20.7916331") and k>F("4.4784588") and U<F("4.651445")
    and Mass<F("4.566568"),"ambient/marginal normalization")
req((n2,n3)==(377,32970),"true interior cells")
req(credit>F("1.25") and full>F("1.2976") and full-F(".493039")>F(".804"),"whole weighted true lower")
