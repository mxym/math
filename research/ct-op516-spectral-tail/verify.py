#!/usr/bin/env python3
"""Exact arithmetic boundary checks, geometric samples and APN tensor examples."""
from collections import Counter, defaultdict
from itertools import combinations
from hashlib import sha256

ROW11 = (1,2,4,8,16,4,6,16,26,8,5,53,32,39,62)


def dot(u,v):
    return (u&v).bit_count()&1


def xor(seq):
    z=0
    for a in seq:z^=a
    return z


def rank(rows):
    piv={}
    for x in rows:
        while x:
            k=x.bit_length()
            if k in piv:x^=piv[k]
            else:
                piv[k]=x
                break
    return len(piv)


def wedge(x,y,n):
    return sum((dot(x,1<<i)*dot(y,1<<j)^dot(x,1<<j)*dot(y,1<<i))<<k
               for k,(i,j) in enumerate(combinations(range(n),2)))


def bounds(n,d):
    s=((1<<d)-1)//3
    rho=min(s-1,d*(d-1)//2)
    L=s if n<=rho else (2*s if 2*d<=n<=2*rho else 3*s)
    return max(n+1,L)


def check_integer_boundaries():
    def q(N,D,j):return N*(N+1)-2*(2*j+1)*D*N+4*j*(j+1)*D*D
    for d in range(4,82,2):
        D=1<<(d-1)
        assert q(2*D+2,D,1)==q(4*D-3,D,1)==6-2*D<0
        assert q(4*D+3,D,2)==q(6*D-4,D,2)==12-2*D<0
        assert q(4*D-2,D,1)==2 and q(4*D+1,D,1)==6*D+2
        s=(2*D-1)//3
        assert (4*D+1)%3==0 and (2*D)%3==1 and (2*D+1)%3==2
        assert 3*s==2*D-1 and 6*s==4*D-2 and 9*s==6*D-3
    assert [bounds(n,4) for n in (6,8,10,12,14)]==[15,10,15,15,15]
    assert [bounds(n,6) for n in (14,16,30,32,60,62,64)]==[21,42,42,63,63,63,65]
    assert [bounds(n,8) for n in (28,30,56,58,252,254)]==[85,170,170,255,255,255]
    print("moment polynomial endpoints, exceptional residues and bound transitions: PASS")


def spread(d):
    def omega(x):
        return sum((0,2,3,1)[(x>>i)&3]<<i for i in range(0,d,2))
    out=[]
    for x in range(1,1<<d):
        y=omega(x)
        if x<min(y,x^y):
            out.append((x,y,x^y))
    assert sorted(x for L in out for x in L)==list(range(1,1<<d))
    return out


def check_geometry():
    for d in (4,6):
        planes=spread(d)
        q=1<<d
        D=q//2
        m=len(planes)
        for k in (1,2):
            r=k*d
            ls=[tuple(x<<(d*j) for x in L) for j in range(k) for L in planes]
            pts={x for L in ls for x in L}
            ws=Counter(sum(dot(u,x) for x in pts) for u in range(1<<r))
            expected=Counter({0:1,D:k*(q-1)})
            if k==2:expected[2*D]=(q-1)**2
            assert ws==expected
            ps=[wedge(x,y,r) for x,y,z in ls]
            for j in range(k):assert xor(ps[j*m:(j+1)*m])==0
            assert rank(ps)==k*(d*d//4)
            print(f"sample d={d}, {k} flat(s): planes={k*m}; weights={sorted(ws.items())}; wedge rank={rank(ps)}")
        pts_bad={x for L in planes[1:] for x in L}
        assert any(sum(dot(u,x) for x in pts_bad)%D for u in range(q))
    print("negative control: deleting one spread line breaks divisibility")


def gf16_mul(a,b):
    result=0
    while b:
        if b&1:result^=a
        a<<=1
        if a&16:a^=0x13
        b>>=1
    return result


def cube4():
    return [gf16_mul(gf16_mul(x,x),x) for x in range(16)]


def lut6():
    return [xor(c for c,(i,j) in zip(ROW11,combinations(range(6),2)) if x>>i&1 and x>>j&1)
            for x in range(64)]


def check_apn(F,n):
    q=1<<n
    beta=lambda x,y:F[x]^F[y]^F[x^y]^F[0]
    pair=list(combinations(range(n),2))
    assert all(F[x] == F[0]^xor(F[0]^F[1<<j] for j in range(n) if x>>j&1)^xor(
               beta(1<<i,1<<j) for i,j in pair if x>>i&1 and x>>j&1) for x in range(q))
    groups=defaultdict(list)
    for x in range(1,q):
        counts=Counter(F[x^y]^F[y] for y in range(q))
        assert len(counts)==q//2 and set(counts.values())=={2}
        [mask]=[b for b in range(1,q) if all(not dot(b,beta(x,y)) for y in range(q))]
        groups[mask].append(x)
    ls=[(b,rr[0],rr[1]) for b,rr in groups.items() if len(rr)==3]
    m=len(ls)
    p=[wedge(x,y,n) for b,x,y in ls]
    val=[beta(x,y) for b,x,y in ls]
    assert xor(p)==xor(val)==0
    for v in range(q):
        assert xor(val[i] for i,(b,x,y) in enumerate(ls) if dot(v,b))==v
    assert rank(p)>=n
    assert all(not dot(b,d) for (b,x,y),d in zip(ls,val))
    if m==n+1:
        assert all(dot(b,z)==(i!=j) for i,(b,x,y) in enumerate(ls) for j,z in enumerate(val))
        for u in range(q):
            s=[int(dot(u,x) or dot(u,y)) for b,x,y in ls]
            eps=xor(ls[j][0] for j in range(m) if s[j])
            assert all(dot(val[j],eps)==s[j] for j in range(m))
    distro=Counter((len(L)+1).bit_length()-1 for L in groups.values())
    exp={2:5} if n==4 else {2:16,4:1}
    assert distro==Counter(exp)
    if n==6:assert sha256(bytes(F)).hexdigest()=="bcf79b0f86e54bd1fd63c779ae0ca2c44a71c7dfa26666622ab814bb44c1809a"
    print(f"n={n} APN: positive radical dimensions {sorted(distro.items())}; m={m}; "
          f"wedge rank={rank(p)}; D B^T=I; equality case={m==n+1}")


def main():
    check_integer_boundaries()
    check_geometry()
    check_apn(cube4(),4)
    check_apn(lut6(),6)
    print("PASS: structural tails, APN tensors and equality witness")


if __name__=="__main__":
    main()
