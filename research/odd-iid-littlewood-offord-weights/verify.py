#!/usr/bin/env python3
"""Exact direct enumeration of the actual one-dimensional laws, not the column proof."""
from math import comb

def ensure(b, msg):
    if not b: raise ArithmeticError(msg)

def pmf():
    f={0:1}
    for i in range(9):
        fnew={}
        shift=(1 if i==0 else -1)*10**i
        a,b=(3,1) if i<2 else (3,2)
        for x,v in f.items():
            fnew[x]=v*a
            fnew[x+shift]=v*b
        ensure(len(fnew)==2*len(f), 'colliding input digit')
        f=fnew
    return f

def addlaw(f,g,scale):
    out={}
    entries=[(x*scale,c) for x,c in g.items()]
    for x,a in f.items():
        for y,b in entries:
            z=x+y
            out[z]=out.get(z,0)+a*b
    return out

def bernrow(n,k,a,b):
    row=[1]
    for i in range(n):
        l,h=(b-a,a) if i<n-k else (a,b-a)
        new=[0]*(len(row)+1)
        for j,v in enumerate(row):
            new[j]+=l*v
            new[j+1]+=h*v
        row=new
    return max(row)

def main():
    f=pmf();h=addlaw(f,f,1);den=sum(f.values())**3
    ensure((len(f),sum(f.values()),len(h))==(512,1250000,19683),'input or pair shape')
    expect=(976076478078336,977280228179739,994151968413120)
    for scale,want in zip((1,-1,10),expect):
        totals=addlaw(h,f,scale);height=max(totals.values())
        ensure(sum(totals.values())==den and height==want,'triple mismatch')
        print('Third coefficient',scale,':',len(totals),'distinct integer totals; peak',height,'/',den)
    ensure(expect[2]>max(expect[:2]),'no strict counterexample')
    for n in range(3,32,2):
        m=n//2
        small=[bernrow(n,k,1,2*n+1) for k in range(m+1)]
        b=100*(n+1)**2
        near=[bernrow(n,k,b//2-1,b) for k in range(m+1)]
        ensure(small[m]>max(small[:m]) and near[0]>max(near[1:]),'opposing signs')
    print('Exact opposing Bernoulli maximizers checked for odd n=3,5,...,31.')
    print('PASS. The all-odd unbounded ratio is proved analytically.')

if __name__=='__main__':main()
