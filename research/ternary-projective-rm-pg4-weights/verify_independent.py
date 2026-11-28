#!/usr/bin/env python3
"""Rebuild both projective zero configurations and rank them over F3."""
from functools import lru_cache
from hashlib import sha256
from itertools import combinations,product
from math import prod


@lru_cache(None)
def projective(m):
    return tuple((0,)*j+(1,)+a for j in range(m+1) for a in product(range(3),repeat=m-j))


@lru_cache(None)
def affpoints(m):
    return tuple((1,)+a for a in product(range(3),repeat=m))


def shapes(m,n,side):
    if not n:
        return ()
    power,s=1,0
    while power*3<=n:
        power*=3
        s+=1
    # split into a full number of affine s-planes and a remainder.
    b=n%power
    if b<=(power-1)//2:
        y=affpoints(m)[:n-b]
        return y+tuple((0,)*(m-s+1)+p for p in shapes(s-1,b,side))
    if side==0:
        local=affpoints(s+1)[:n]
    else:
        h=projective(s)
        local=tuple((0,)+p for p in h)+affpoints(s+1)[:n-len(h)]
    return tuple((0,)*(m-s-1)+p for p in local)


@lru_cache(None)
def homogen(m,d):
    if not m:
        return ((d,),)
    return tuple((a,)+x for a in range(d+1) for x in homogen(m-1,d-a))


def encoding(xs,d):
    mon=homogen(len(xs[0])-1,d)
    a={}
    for x in xs:
        one,two=0,0
        for i,ex in enumerate(mon):
            z=prod(pow(y,e,3) for y,e in zip(x,ex))%3
            if z==1:
                one |= 1<<i
            if z==2:
                two |= 1<<i
        a[x]=(one,two)
    return a


def rank(vectors):
    # Trinary bit-sliced elimination. A row stores the masks for values 1 and 2.
    basis={}
    for one,two in vectors:
        while one or two:
            p=(one|two)&-(one|two)
            ab=basis.get(p)
            if ab is None:
                basis[p]=(two,one) if two&p else (one,two)
                break
            a,b=ab
            if one&p:
                a,b=b,a  # add negative of the normalized pivot row.
            zero=~(one|two)
            c=~(a|b)
            one,two=(one&c)|(zero&a)|(two&b),(two&c)|(zero&b)|(one&a)
    return len(basis)


def weights(m,d):
    xs=projective(m)
    p=len(xs)
    rows=encoding(xs,d)
    dim=rank(rows.values())
    cap={}
    for n in range(p+1):
        h=dim+1
        for side in (0,1):
            z=shapes(m,n,side)
            assert len(z)==len(set(z))==n and all(x in rows for x in z)
            h=min(h,rank(rows[x] for x in z))
        cap[n]=dim-h
    assert cap[0]==dim and cap[p]==0
    return (0,)+tuple(p-max(n for n,k in cap.items() if k>=r) for r in range(1,dim+1))


@lru_cache(None)
def affine_hp(m,d):
    # Use the other HP ordering: high digit sums and increasing lex order.
    data=[i+1 for i,t in enumerate(product(range(3),repeat=m)) if sum(t)>=2*m-d]
    return [0]+data


def geom_counts(m):
    n=len(projective(m))
    masks=[]
    for x in projective(m):
        mask=0
        for i,y in enumerate(projective(m)):
            if sum(a*b for a,b in zip(x,y))%3==0:
                mask |= 1<<i
        masks.append(mask)
    counts={mask.bit_count() for mask in masks}
    second={(u&v).bit_count() for u,v in combinations(masks,2)}
    assert len(set(masks))==n and len(counts)==len(second)==1
    return n,counts.pop(),second.pop()


def check_lower(m,d,cs,counts,table):
    n,a2,a3=counts
    D,C=affine_hp(m,d),affine_hp(m,d-1)
    U,V=cs[m-1,d],cs[m-1,d-2]
    lo=[]
    for r in range(1,len(cs[m,d])):
        # Here g=kernel on the affine block and x=rank on the projective block.
        lr={}
        for g in range(len(V)):
            for x in range(g,len(U)):
                if not ((0<=r-g<len(D)) and (0<=r-x<len(C))):
                    continue
                inner=max(U[x],V[g])
                outer=max(C[r-x],D[r-g])
                lr[x,g]=inner,outer
        l=min(x+y for x,y in lr.values())
        b=cs[m,d][r]
        if l==b:
            continue
        # Check every excluded candidate weight separately; no minimum-hyperplane
        # formula or rounding is used by this verifier.
        assert l<b
        for w in range(l,b):
            survivors=sorted((x,g,i,w-j) for (x,g),(i,j) in lr.items() if i+j<=w)
            extrema=[v for _,_,u,t in survivors for v in range(u,t+1)]
            x,y=min(extrema),max(extrema)
            total=w*a2
            square=total+w*(w-1)*a3
            assert not x*n<=total<=y*n or square>(x+y)*total-x*y*n
            if total>=x*n:
                assert l==w and b==w+1
                table[m,d,r]=(w,b,survivors)
                lo.append(r)
    return lo


def main():
    checks={}
    for m in (2,3,4):
        for d in range(1,2*m+2):
            checks[m,d]=weights(m,d)
    assert checks[2,1]==(0,9,12,13) and checks[2,2]==(0,6,8,9,11,12,13)
    assert checks[3,3][11]==30 and checks[3,4][7]==16
    print("Independent projective shapes: 21 layers by direct F3 evaluation/rank")
    count3=geom_counts(3)
    count4=geom_counts(4)
    assert count3==(40,13,4) and count4==(121,40,13)
    print(f"Direct point/pair incidence counts: {count3}, {count4}")
    table={}
    for m,d in ((3,3),(3,4),(4,3),(4,4),(4,5),(4,6)):
        g=check_lower(m,d,checks,count3 if m==3 else count4,table)
        assert g=={(4,3):[11],(4,6):[31]}.get((m,d),[])
    assert {key[2]: (o[0],o[1],tuple(sorted({i for _,_,i,j in o[2]})))
            for key,o in table.items() if key[0]==4}=={11:(76,77,(22,25)),31:(44,45,(14,17,18))}
    # Negative control: omitting the restriction interval cannot rule out w=44.
    N,K,J=count4
    s=44*K
    ss=s+44*43*J
    assert ss <= 40*s and ss > (14+18)*s-(14*18)*N
    print(f"Independent remaining gap: w=44 required second sum {ss}, interval ceiling {(14+18)*s-(14*18)*N}")
    print("Independent profile SHA256:",sha256(repr(tuple(checks[4,d] for d in range(1,10))).encode()).hexdigest())


if __name__=="__main__":
    main()
