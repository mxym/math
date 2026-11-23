import two_type_true_hoffman as H
import sympy as sm, numpy as np

from fractions import Fraction as F
os,ix,by,m,b,rr=H.buildcore()
def sel(k,d):
 return [int(z==dict(by[k])[d]) for z in os]if d in dict(by[k])else [0]*len(os)
def eq(v,z=0):
 m.append(v);b.append(z)
eq(rr({(1,27):1,(0,18):-9}));eq(sel((2,22),22),1);eq(rr({(0,14):1}));eq(sel((2,22),15));eq(rr({(2,22):1}),1)
for d in [2,4,6,8]:
 for y in H.moments(by,ix,[d],[((0,0,0,0),1),((1,2,3,1),1),((1,-1,1,-2),1),((2,-1,1,2),1)]):eq(y)
M=sm.Matrix([r+[s]for r,s in zip(m,b)])
m0,pi=M.to_DM().rref();a=m0.to_Matrix();ff=[i for i in range(len(os))if i not in pi]
U=np.array([[F(x)for x in r]for r in a.tolist()],dtype=object)
xs=np.zeros((len(os),len(ff)+1),dtype=object);xs[ff,:-1]=np.eye(len(ff),dtype=int)
xs[list(pi),-1]=U[:len(pi),-1];xs[list(pi),:-1]=-U[:len(pi),ff]
fun=lambda v: np.array(v,dtype='object')@xs

S=fun(rr({(1,23):1}));S[-1]-=99
J=np.zeros(len(S),dtype=object);J[-1]=1

n=fun(rr({(0,18):1}));q=fun(rr({(0,22):1}))
def check(k,q0):
 assert np.all(fun(rr({k:1}))==q0),k
check((0,28),-1386*J+90*n+8*q)
check((3,39),221*J+55*n+8*q)
check((1,37),121432*J+768*n)
check((4,46),24*n-108*J)
check((1,33),10169*J+57*n)
assert np.all(4*q+2*fun(rr({(3,35):1}))-3*S-172*J==0)
assert np.all(3*q-3*fun(rr({(3,33):1}))-S-19*J==0)
print("verified seven exact original shell identities on the rank-42 M=1 two-type chart")
for k in (50,51,52,53):
 s=3*k-148;lo=F(19+s,3);hi=F(172+3*s,4)
 print(k,s,"W022",lo,hi,"N28",90*k-1386+8*lo,90*k-1386+8*hi)
