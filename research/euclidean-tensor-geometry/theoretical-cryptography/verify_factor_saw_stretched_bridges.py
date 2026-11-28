#!/usr/bin/env python3
"""Replay the square-lattice SAW lower bound from Numaro's archived bridge table.

Normal use:
    python3 verify_factor_saw_stretched_bridges.py bridge_table_record_L17.json
Use --small-test alone for an independent geometric replay on short walks.
No compiler, package or network access is needed by the checker.
"""
import hashlib
import json
import sys
from pathlib import Path

if not __debug__:
    raise RuntimeError("Do not use Python -O")

TABLE_MD5 = "17a65c9ac2990e13785b79639abc6861"
NUM, DEN = 262738682602, 100000000000
OLD_NUM, OLD_DEN = 2**128, 129513673858566230428673965530967449326

def counts(walk):
    span = walk[-1][0]
    h = [0]*span
    for (x,y),(u,v) in zip(walk,walk[1:]):
        if x!=u: h[min(x,u)] += 1
    return h

def cut_condition(walk):
    return not any(
        all(0<x<=walk[i][0] for x,_ in walk[1:i])
        and all(walk[i][0]<x<=walk[-1][0] for x,_ in walk[i+1:])
        for i in range(1,len(walk)-1)
    )

def stretch(walk,j,h):
    new = [walk[0]]
    for (x,y),(u,v) in zip(walk,walk[1:]):
        if min(x,u)==j and max(x,u)==j+1:
            new.extend((j+a,y) for a in (range(1,h+1) if u>x else range(h,0,-1)))
        new.append((u+(h if u>j else 0),v))
    return tuple(new)

def contract(walk,j,h):
    return tuple((x-(h if x>j+h else 0),y) for x,y in walk if not j<x<=j+h)

def odd_floor(n,w):
    v = n//w
    return v if v%2 else v-1

def small_test(depth=12,max_span=4):
    step=((1,0),(-1,0),(0,1),(0,-1))
    p=[(0,0)]
    visited={(0,0)}
    used=[set(),set()]
    total=0
    def dfs():
        nonlocal total
        x,y=p[-1]
        if x>=2 and all(u<=x for u,_ in p):
            h=counts(p)
            assert h[0]==1 and all(c%2 for c in h)
            test=all(c>=3 for c in h[1:])
            assert test==cut_condition(p)
            if test:
                total+=1
                j=min(range(1,x),key=h.__getitem__)
                assert h[j]<=odd_floor(len(p)-1,x)
                for k in (1,2):
                    out=stretch(p,j,k)
                    assert len(set(out))==len(out) and len(out)==len(p)+k*h[j]
                    assert out[0]==(0,0) and out[-1][0]==x+k
                    assert all(0<u<=x+k for u,_ in out[1:])
                    assert all(abs(u-x0)+abs(v-y0)==1 for (x0,y0),(u,v) in zip(out,out[1:]))
                    h2=counts(out)
                    assert j==min(range(1,x+k),key=h2.__getitem__)
                    assert cut_condition(out) and contract(out,j,k)==tuple(p)
                    assert out not in used[k-1]
                    used[k-1].add(out)
        if len(p)-1==depth:return
        for dx,dy in step:
            z=(x+dx,y+dy)
            if z not in visited and 0<z[0]<=max_span:
                visited.add(z);p.append(z);dfs();p.pop();visited.remove(z)
    dfs()
    return total

def calculate(a):
    nmax,w=a["N"],a["L"]
    b=a["b_nl"]
    assert (nmax,w)==(260,17) and len(b)==nmax+1
    assert all(len(row)==w+1 and all(type(c) is int and c>=0 for c in row) for row in b)
    irred=[[0]*(nmax+1) for _ in range(w+1)]
    # Coefficient renewal: a bridge's first irreducible piece is unique.
    for span in range(1,w+1):
        for n in range(1,nmax+1):
            irred[span][n]=b[n][span]-sum(
                irred[i][j]*b[n-j][span-i]
                for i in range(1,span) for j in range(i,n-(span-i)+1)
            )
            assert irred[span][n]>=0
    assert irred[w][50:56]==[0,2,98,3504,87742,1775410]
    base=[sum(irred[i][n] for i in range(1,w+1)) for n in range(nmax+1)]
    result=base+[0]*60
    for n,a_n in enumerate(irred[w]):
        if a_n:
            h=odd_floor(n,w)
            assert h>=3
            for k in range(1,5):
                result[n+k*h]+=a_n
    return base,result

def excess(poly,num,den):
    n=len(poly)-1
    u=num**n
    v=sum(c*den**j*num**(n-j) for j,c in enumerate(poly) if c)
    return v-u,u

def main():
    if len(sys.argv)==2 and sys.argv[1]=="--small-test":
        print("irreducible short walks independently checked:",small_test())
        return
    if len(sys.argv)!=2:
        raise SystemExit(__doc__)
    raw=Path(sys.argv[1]).read_bytes()
    assert len(raw)==206604 and hashlib.md5(raw).hexdigest()==TABLE_MD5
    base,added=calculate(json.loads(raw))
    assert excess(base,OLD_NUM,OLD_DEN)[0]>0
    assert excess(base,NUM,DEN)[0]<0
    assert excess(added,NUM+1,DEN)[0]<0
    diff,normalization=excess(added,NUM,DEN)
    assert diff>0
    assert diff*10**30//normalization == 4754550554063873066
    print("certified:",f"mu > {NUM}/{DEN}","=", "2.62738682602")
    print("floor(10^30 * normalized excess):",diff*10**30//normalization)

if __name__=="__main__":
    main()
