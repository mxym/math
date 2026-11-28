#!/usr/bin/env python3
"""Four frozen degree-five Runge certificates and ordinary-integer full scans.
Requires SymPy. Use --tail-only to skip the finite scans.
"""
from sympy import Poly, QQ, ZZ, invert, resultant, symbols
from math import prod
from sys import argv

t,u,Z,Y = symbols("t u Z Y")

def expansion(a,b,d):
 g=Poly(1-(1+t)**a*t**b,t,domain=QQ)
 fs=Poly(1-(1+t)**a*t**b,t).factor_list()[1]
 cand=[f.monic() for f,m in fs if f.eval(0)*f.eval(1)<0]
 assert len(cand)==1
 G=cand[0]
 if G.domain!=QQ:G=G.set_domain(QQ)
 f=Poly(prod(1-k*u for k in range(a+b))-prod(1+t-k*u for k in range(a))*prod(t+k*u for k in range(1,b+1)),t,u,domain=QQ)
 zero=Poly(0,t,domain=QQ)
 one=Poly(1,t,domain=QQ)
 K=lambda x:Poly(x,t,domain=QQ).rem(G)
 X=K(t)
 def mult(A,B,m):
  C=[zero for j in range(m+1)]
  for i,x in enumerate(A[:m+1]):
   if not x:continue
   for j,y in enumerate(B[:m+1-i]):
    if y:C[i+j]+=x*y
  return [x.rem(G) for x in C]
 def tpowers(T,m,k):
  A=[[one]+[zero]*m]
  for i in range(k):
   A.append(mult(A[-1],T,m))
  return A
 invder=Poly(invert(g.diff(),G),t,domain=QQ)
 T=[X]
 for j in range(1,d+1):
  powers=tpowers(T,j,f.degree(t))
  err=sum((powers[i][j-k].mul_ground(v) for (i,k),v in f.terms() if k<=j),zero)
  T.append((-err*invder).rem(G))
 powers=tpowers(T,d,d)
 return G,T,powers


# A coefficient entry [[i,j],c] represents c*Y**i*Z**j.
CERTS = [
    (2,4,13600000,[[[5,0],-1727744],[[4,1],-5369600],[[4,0],-7226752],[[3,2],-3641856],[[3,1],-35404544],[[3,0],1273216],[[2,3],1727744],[[2,2],-42092928],[[2,1],-36421440],[[2,0],12892864],[[1,4],3641856],[[1,3],-27862016],[[1,2],-16613984],[[1,1],-24422144],[[1,0],12209552],[[0,4],10925568],[[0,3],-84612672],[[0,2],121491712],[[0,1],-40244942],[[0,0],-5238353]]),
    (4,2,3900000,[[[5,0],-1979776],[[4,1],-3959552],[[4,0],-2443200],[[3,2],-1979776],[[3,1],-13848960],[[3,0],16660976],[[2,3],1979776],[[2,2],-29277312],[[2,1],45128048],[[2,0],4588560],[[1,3],2389632],[[1,2],-47103312],[[1,1],113751216],[[1,0],-37808403],[[0,4],3023232],[[0,3],-28574080],[[0,2],70787544],[[0,1],-51473643],[[0,0],18521514]]),
    (3,6,842000,[[[5,0],7713],[[4,1],22851],[[4,0],31257],[[3,2],25230],[[3,1],107091],[[3,0],-113371],[[2,3],2379],[[2,2],236367],[[2,1],-469208],[[2,0],-169521],[[1,4],-15138],[[1,3],267321],[[1,2],-750498],[[1,1],308056],[[1,0],-300098],[[0,5],-10092],[[0,4],143811],[[0,3],-522228],[[0,2],325128],[[0,1],738676],[[0,0],-272220]]),
    (6,3,1070000,[[[5,0],-13407],[[4,1],-35388],[[4,0],43482],[[3,2],-26268],[[3,1],-10080],[[3,0],16334],[[2,3],13407],[[2,2],-300186],[[2,1],739531],[[2,0],-253488],[[1,4],12861],[[1,3],-183315],[[1,2],422523],[[1,1],277],[[1,0],763546],[[0,5],-4287],[[0,4],115749],[[0,3],-919707],[[0,2],1885437],[[0,1],1597284],[[0,0],-2470760]]),
]

def finite(a,b,B):
    D=a+b
    y=0; L=R=prod(range(1,D+1))
    sol=[(D,y)]
    for z in range(D+1,B+1):
        L=(L*z)//(z-D)
        x=z+y
        R=(R*x)//(x-a)
        while R<L:
            R=(R*(x+1)*(y+b+1))//((x+1-a)*(y+1))
            y+=1; x+=1
        if R==L:
            assert prod(z-k for k in range(D)) == (
                prod(x-k for k in range(a))*prod(y+k for k in range(1,b+1)))
            sol.append((x,y))
        if z%1_000_003==0:
            assert L==prod(z-k for k in range(D))
            assert R==prod(x-k for k in range(a))*prod(y+k for k in range(1,b+1))
    assert sol==[(D,0)]
    return sol

def run(a,b,B,cert):
    F=prod(Z-k for k in range(a+b))-prod(Z+Y-k for k in range(a))*prod(Y+k for k in range(1,b+1))
    P=sum(c*Y**i*Z**j for (i,j),c in cert)
    _,T,A=expansion(a,b,5)
    C=[Poly(0,t,domain=QQ) for i in range(6)]
    for (i,j),c in cert:
        for k,Fj in enumerate(A[i][:i+j+1]):
            C[5-i-j+k]+=Fj.mul_ground(c)
    assert all(p.is_zero for p in C), "does not vanish through order five"
    for s in (-1,0,1):
        R=Poly(resultant(F,P+s,Y),Z,domain=ZZ).shift(B)
        co=R.all_coeffs()
        assert min(co)>0 or max(co)<0, (a,b,s,co)
    print("exact tail certificate",a,b,B,flush=True)
    if "--tail-only" not in argv:
        print("complete solutions",a,b,finite(a,b,B),flush=True)

if __name__=="__main__":
    for C in CERTS:run(*C)
    print("PASS",flush=True)
