#!/usr/bin/env python3
"""Exact weighted full-atom slices and direction-space compiler checks."""
from itertools import combinations, permutations, product
from collections import Counter
from fractions import Fraction

if not __debug__:
    raise RuntimeError("enable Python assertions")

def mul(a,b,high,mod):
    x=0
    while b:
        if b&1:
            x^=a
        a<<=1
        if a&high:
            a^=mod
        b>>=1
    return x

def powef(a,t):
    r=1
    while t:
        if t&1:
            r=mul(r,a,1024,0x41b)
        a=mul(a,a,1024,0x41b)
        t>>=1
    return r

# Direct binary polynomial arithmetic with an independent modulus.
H=1024
F=[t for t in range(H) if powef(t,4)==t]
assert len(F)==4
assert all(powef(a,H-1)==1 for a in range(1,H))
q=len(F)
Q=H**2
base=H-1
setups=[(2,3,F[0],F[1],(9,1111%H)),
        (5,16,F[1],F[3],(101,0)),
        (17,0,F[2],F[3],(511,1023))]
slices=0
weight_total=0
for theta,slope,ti,tj,u in setups:
    assert theta not in F
    c={f:f^mul(theta,mul(f,f,H,0x41b),H,0x41b) for f in F}
    maps={s:[mul(s,a,H,0x41b) for a in range(H)] for s in list(c.values())+[slope]}
    ks=maps[slope]
    atoms=[0]*Q
    ui,uj=maps[c[ti]],maps[c[tj]]
    # Count exact integral numerators at a fixed first-share value u.
    # B is uniquely determined by u for each A/branch choice.
    # Denominator: Q choices of B times Q*(H-1) for the branch/A law.
    for x in range(H):
        bx=u[0]^ui[x]
        zjx=bx^uj[x]
        line_y=ks[x]
        for y in range(H):
            if not(x or y):
                continue
            by=u[1]^ui[y]
            zjy=by^uj[y]
            w=base-(q-2)*int(x!=0 and y==line_y)
            assert w>0
            atoms[zjx*H+zjy]+=w
    hits=0
    for h in F[1:]:
        ui=maps[c[min(ti,ti^h)]]
        uj=maps[c[min(tj,tj^h)]]
        if h==ti^tj:
            assert ui==uj
            hits+=1
        else:
            assert ui!=uj
        for x in range(1,H):
            y=ks[x]
            bx,by=u[0]^ui[x],u[1]^ui[y]
            zjx,zjy=bx^uj[x],by^uj[y]
            atoms[zjx*H+zjy]+=1
    assert hits==1
    assert atoms==[base]*Q
    assert sum(atoms)==Q*base
    # Negative control: preserve the branch probabilities but replace the
    # nonmatching direction sampler by a uniform draw from all V without zero.
    wrong_on_line=Fraction(Q-q+1,Q*(Q-1))+Fraction(q-2,Q*base)
    wrong_off_line=Fraction(Q-q+1,Q*(Q-1))
    assert wrong_on_line>Fraction(1,Q)>wrong_off_line
    slices+=Q
    weight_total+=sum(atoms)
print(f"direct joint-atom enumeration: {slices} full joint atoms in 3 fixed-first slices; integer mass {weight_total}; repair negative control PASS")

def m4(x,y):
    return mul(x,y,4,7)

def inv4(x):
    assert x
    return m4(x,x)

def subrows(a,b):
    return tuple(x^y for x,y in zip(a,b))

def scale(c,a):
    return tuple(m4(c,x) for x in a)

def rref(rows,d):
    r=[list(row) for row in rows]
    top=0
    piv=[]
    for j in range(d):
        if top==len(r):
            break
        i=next((i for i in range(top,len(r)) if r[i][j]),None)
        if i is None:
            continue
        r[top],r[i]=r[i],r[top]
        r[top]=list(scale(inv4(r[top][j]),r[top]))
        for i in range(len(r)):
            if i!=top:
                r[i]=list(subrows(r[i],scale(r[i][j],r[top])))
        top+=1
        piv.append(j)
    return tuple(map(tuple,r[:top])),tuple(piv)

trials=0
pairtests=0
ranks=set()
for d in [1,2]:
    vec=list(product(range(4),repeat=d))
    for S in vec:
        counts={I:Counter() for I in combinations(range(4),2)}
        for a,b in product(vec,repeat=2):
            Y=tuple(subrows(a,subrows(scale(i,b),scale(m4(i,i),S))) for i in range(4))
            for I in counts:
                counts[I][tuple(Y[i] for i in I)]+=1
            basis,piv=rref([S,b],d)
            ranks.add(len(basis))
            theta=tuple(S[j] for j in piv)+(0,)*(2-len(basis))
            for i,j,k in permutations(range(4),3):
                b2,p2=rref([subrows(Y[j],Y[i]),subrows(Y[k],Y[i])],d)
                assert (basis,piv)==(b2,p2)
                out=(0,)*d
                for z,row in zip(theta,b2):
                    out=subrows(out,scale(z,row))
                assert out==S
                trials+=1
        for count in counts.values():
            assert len(count)==len(vec)**2 and set(count.values())=={1}
            pairtests+=1
assert ranks=={0,1,2}
length_cases=0
for n in range(3,257):
    m=(n-1).bit_length()
    assert n<=2**m<2*n
    for L in range(0,2*m+3):
        M=0 if not L else L if n==3 else m*((L+m-1)//m)+10*m
        assert L<=M<=L+11*m-1
        if n==3 or L==0:
            assert M==L
        if n>=4 and L==1:
            assert M==11*m
        length_cases+=1
print(f"payload compiler: {trials} ordered reconstructions; {pairtests} exact ordered-pair tables; ranks 0/1/2; {length_cases} length cases")
print("verify_independent: PASS")
