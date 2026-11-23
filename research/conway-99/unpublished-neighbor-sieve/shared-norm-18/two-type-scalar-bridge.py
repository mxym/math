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
check((0,24),fun(rr({(3,35):1}))+F(13,2)*n-93*J)
check((3,39),221*J+55*n+8*q)
check((1,37),121432*J+768*n)
check((4,46),24*n-108*J)
check((1,33),10169*J+57*n)
assert np.all(4*q+2*fun(rr({(3,35):1}))-3*S-172*J==0)
assert np.all(3*q-3*fun(rr({(3,33):1}))-S-19*J==0)
print("verified eight exact original shell identities on the rank-42 M=1 two-type chart")
for k in (50,51,52,53):
 s=3*k-148;lo=F(19+s,3);hi=F(172+3*s,4)
 print(k,s,"W022",lo,hi,"N28",90*k-1386+8*lo,90*k-1386+8*hi)

# Final two-type exclusion with the graph-side inequality 2D <= 3L + 42S.
# The excess of the T upper bound over sqrt(2) times B increases
# with L because 35 - 14 sqrt(2) > 0. Check only the maximum even L.
for n0, s0 in [(50, 2), (51, 5), (52, 8), (53, 11)]:
    lmax = 2 * ((172 + 3 * s0) // 2)
    half_n24 = -28 + 6 * s0 + 26 * n0 - 2 * lmax
    B = 4 * n0**2 - 7 * half_n24
    T_upper = 14 * (-693 + 45 * n0) + 35 * lmax + 294 * s0 - 12 * n0 * (n0-7)
    assert T_upper >= 0 and B > 0 and T_upper**2 < 2 * B**2
    print("two-type contradiction", n0, s0, lmax, B, T_upper, 2 * B**2 - T_upper**2)
