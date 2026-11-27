#!/usr/bin/env python3
"""Exhaustive verification of the first non-scalar field case; stdlib only."""
from itertools import combinations
if not __debug__:
    raise SystemExit('Run without -O')

# Re-evaluate the four coordinate polynomials on bit masks.
MON = ((2,3,4,5,6),(4,6,8,10,12),(3,9,10),(1,9,4,12,5))
def pi(y):
    return sum((sum(y&m == m for m in seq)&1)<<i for i,seq in enumerate(MON))


def prod(a,b,r):
    modulus={1:3,2:7,3:11}[r]
    out=0
    while b:
        if b&1:
            out^=a
        b>>=1
        a<<=1
        if a>>r:
            a^=modulus
    return out


def lifted(r,y,wrong=False):
    vals=[(y>>(r*i))&((1<<r)-1) for i in range(4)]
    parity=[v.bit_count()&1 for v in vals]
    z=[a^b for a,b in zip(vals,parity)]
    bits=sum(a<<i for i,a in enumerate(parity))
    shifted=pi(bits)
    step=1 if parity[0]^parity[1]^wrong else 2
    return sum((z[i^step]^((shifted>>i)&1))<<(r*i) for i in range(4))


def check_perm(r,wrong=False):
    q=1<<(4*r)
    pp=[lifted(r,y,wrong) for y in range(q)]
    assert sorted(pp)==list(range(q))
    if not wrong:
        print('r=%d: lifted permutation has %d distinct images'%(r,q))
    return pp


def vector_value(r,u,v,p):
    out=0
    for i in range(4):
        shift=i*r
        mask=(1<<r)-1
        out^=prod((v>>shift)&mask,(p[u^v]>>shift)&mask,r)
    return out


def transform(vals,walsh=False):
    f=list(vals)
    h=1
    while h<len(f):
        for s in range(0,len(f),2*h):
            for i in range(s,s+h):
                j=i+h
                if walsh:
                    f[i],f[j]=f[i]+f[j],f[i]-f[j]
                else:
                    f[j]^=f[i]
        h*=2
    return f


def check_low(r,p):
    d=4*r; mask=(1<<d)-1
    return all(vector_value(r,x&mask,x>>d,p)==0
               for t in range(3) for I in combinations(range(2*d),t)
               for x in [sum(1<<i for i in I)])


def main():
    assert [pi(i) for i in range(16)]==[0,8,1,12,11,10,9,13,2,6,5,4,3,14,7,15]
    for r in (1,2,3):
        p=check_perm(r)
        assert check_low(r,p)
        print(f'r={r}: vanished on the entire radius-2 Hamming ball')
        if r!=2:
            continue
        q=1<<(4*r)
        vec=[vector_value(r,u,v,p) for v in range(q) for u in range(q)]
        for a in (1,2,3):
            scalar=[(x&a).bit_count()&1 for x in vec]
            anf=transform(scalar)
            assert {i.bit_count() for i,x in enumerate(anf) if x}=={3}
            wal=transform((1-2*x for x in scalar),True)
            assert set(wal)=={-q,q}
            print(f'(16,2) output mask {a}: {sum(anf)} cubic terms; all {len(wal)} Walsh magnitudes {q}')
    wrong=check_perm(2,wrong=True)
    assert not check_low(2,wrong)
    print('PASS: reversed switch is still a permutation but fails the low-weight homogeneity check')


if __name__=='__main__':
    main()
