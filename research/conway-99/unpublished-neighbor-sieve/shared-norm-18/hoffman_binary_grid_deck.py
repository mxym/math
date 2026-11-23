"""Numerical constants only; the graph, congruence and determinant arguments are in the note."""
from math import comb

def K(i,w):
    return sum((-1)**j*comb(w,j)*comb(22-w,i-j)
               for j in range(max(0,i-22+w),min(i,w)+1))
allowed=[]
for w in range(23):
    a,b,c=w*(w-8),w*(22-w),(22-w)*(14-w)
    if min(a,b,c)>=0 and a%4==0 and b%2==0 and c%4==0:
        allowed.append(w)
assert allowed==[0,8,10,12,14,22]
assert [K(4,w)+7*K(2,w)+28 for w in allowed]==[8960,0,0,0,0,8960]
assert [(17920//(2**k)-105)//7 for k in (5,6,7)]==[65,25,5]
assert all(25<=23+2*k+2*j<=49 for k in range(1,8) for j in range(k))
print("Weights 0,8,10,12,14,22; grid caps 65,25,5 at binary nullity 5,6,7.")
print("Dyadic discriminant exponent (determinant valuation): 25..49.")
