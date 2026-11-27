#!/usr/bin/env python3
"""Exact Newton, functional equation, factor, and residue recurrence checks."""
from fractions import Fraction
from hashlib import sha256
from math import gcd
from pathlib import Path
import sys

GENERA = {1:2, 2:3, 3:5, 6:33}
KEYS = [(k,n) for k,g in GENERA.items() for n in range(1,g+1)]


def convolution(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j]+=x*y
    return out


def sparse(d, coeff):
    return [coeff.get(i,0) for i in range(d+1)]


def newton(G,g):
    a=[1]
    for i in range(1,g+1):
        value=sum(G[j-1]*a[i-j] for j in range(1,i+1))
        assert value % i == 0
        a.append(value//i)
    a += [a[2*g-i]*(1<<(i-g)) for i in range(g+1,2*g+1)]
    assert all(a[2*g-i]==a[i]*(1<<(g-i)) for i in range(g+1))
    return a


def sums(L,nmax):
    g=[0]
    d=len(L)-1
    for n in range(1,nmax+1):
        a_n=L[n] if n<=d else 0
        g.append(n*a_n-sum(g[j]*L[n-j] for j in range(max(1,n-d),n)))
    return g


def residue_check(L, muted=False):
    need={r:len(L[6])+len(L[gcd(6,r)])-2 for r in (1,2,3,4,5)}
    top=max(r+6*(length-1) for r,length in need.items())
    seq={k:sums(p,top) for k,p in L.items()}
    good=all(seq[6][r+6*j]==seq[gcd(6,r)][r+6*j] for r,length in need.items()
             for j in range(length))
    if not muted:
        assert good and sum(need.values()) == 360 and top == 453
        print("power recurrence check by residue 1..5:", list(need.values()),
              "initial terms, 360 total through index 453")
    return good


def bits_mul(a,b,mod):
    out=0
    while a:
        bit=a&-a
        out^=b<<(bit.bit_length()-1)
        a^=bit
    while out.bit_length()>=mod.bit_length():
        out^=mod<<(out.bit_length()-mod.bit_length())
    return out


def bits_pow(a,e,mod):
    z=1
    while e:
        if e&1:z=bits_mul(z,a,mod)
        a=bits_mul(a,a,mod)
        e>>=1
    return z


def direct_sum(n,k,p):
    q=1<<n
    out=0
    for x in range(1,q):
        t=bits_pow(x,(1<<k)+1,p)^bits_pow(x,q-2,p)
        tr=0
        for _ in range(n):
            tr^=t
            t=bits_mul(t,t,p)
        assert tr==0 or tr==1
        out+=1-2*tr
    return out


def check_weil(Q):
    # Normalize the degree-nine quotient by U=z/8; clear denominator 2.
    T=[Fraction(2*c, 8**i) for i,c in enumerate(Q)]
    S=[2,-3,3,-2,2,-2,3,-3,2]
    assert T==convolution(S,[1,1])
    # z^-4 S(z) at x=z+z^-1 is x times 2x^3-3x^2-5x+7.
    # Generate z^j+z^-j using C_j=x*C_(j-1)-C_(j-2), and check identity.
    C=[[2],[0,1]]
    for i in range(2,5):
        p=[0]+C[-1]
        for j,t in enumerate(C[-2]):p[j]-=t
        C.append(p)
    R=[S[4],0,0,0,0]
    for j in range(1,5):
        for k,t in enumerate(C[j]):R[k]+=S[4+j]*t
    assert R == [0,7,-5,-3,2]
    def cubic(x):
        return ((2*x-3)*x-5)*x+7
    grid=[-2,-1,1,Fraction(3,2),2]
    vals=[cubic(x) for x in grid]
    assert vals==[-11,7,1,Fraction(-1,2),1]
    assert vals[0]*vals[1]<0 and vals[2]*vals[3]<0 and vals[3]*vals[4]<0
    print("exact Weil check for the new quotient: reciprocal, cubic sign brackets",
          [(str(x),str(y)) for x,y in zip(grid,vals)])


def read_fixture():
    lines = Path("COUNTS.tsv").read_text().splitlines()
    assert lines[0].split()==["k","n","field_modulus","recurrence_modulus","G"]
    rows=[tuple(map(int,row.split())) for row in lines[1:]]
    assert [(k,n) for k,n,p,q,v in rows]==KEYS and len(rows)==43
    assert all(p!=q for k,n,p,q,v in rows if n>=3)
    assert all(v&1 and abs(v)<1<<n for k,n,p,q,v in rows)
    return rows


def read_actual(path):
    return [tuple(map(int,row.split())) for row in Path(path).read_text().splitlines()]


def main():
    rows=read_fixture()
    if len(sys.argv)==3:
        expected0=[(k,n,p,G) for k,n,p,q,G in rows]
        expected1=[(k,n,q,G) for k,n,p,q,G in rows]
        assert read_actual(sys.argv[1])==expected0
        assert read_actual(sys.argv[2])==expected1
        print("both compiled engines match all 43 frozen point counts and modulus encodings")
    else:
        assert len(sys.argv)==1
        print("certificate-only mode: no compiled engines replayed")
    G={k:[v for i,n,p,q,v in rows if i==k] for k in GENERA}
    for k,n,p,q,v in rows:
        if n <= 10:
            assert direct_sum(n,k,p)==v
    print("unblocked direct power/inverse/trace check on all fixture rows with n<=10")
    L={k:newton(G[k],g) for k,g in GENERA.items()}
    F=[1,1,0,2,4]
    A=[1,0,2]
    B=[1,0,0,-4,0,0,8]
    Q=[1,-4,0,256,0,0,131072,0,-8388608,134217728]
    C=sparse(54,{6*i:x for i,x in enumerate(Q)})
    assert L[1]==F and L[2]==convolution(F,A) and L[3]==convolution(F,B)
    assert L[6]==convolution(convolution(convolution(F,A),B),C)
    coeff_file=Path("L6_COEFFS.txt").read_bytes()
    assert list(map(int,coeff_file.split())) == L[6]
    print("L1, L2, L3 verified; L6 full 67 coefficients verified from Newton and FE")
    print("L6_COEFFS.txt SHA256:",sha256(coeff_file).hexdigest())
    print("L6 auxiliary R(U) coefficient list:",Q)
    check_weil(Q)
    residue_check(L)
    badG=G[6][:]
    badG[-1]+=66
    mutant=L.copy()
    mutant[6]=newton(badG,33)
    assert mutant[6]!=L[6] and not residue_check(mutant,muted=True)
    print("negative control: changing G33 by 66 destroys the factor and residue certificate")
    print("PASS: exact all-extension-degree proof for exponent k=6")


if __name__=="__main__":
    main()
