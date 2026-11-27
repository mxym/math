#!/usr/bin/env python3
"""Sanity checks for OddHarmonicParitySpectrum.md (standard library)."""

def compositions(n, hi):
    if not n:
        yield ()
    for v in range(1, min(n,hi)+1):
        for rest in compositions(n-v,v):
            yield (v,)+rest

def main():
    totals=[0,0,0]
    for k in range(1,102,2):
        for r in range(2,2*k+3,2):
            assert all(min(j,r-j)<=k for j in range(1,r,2))
            totals[0]+=1
        for m in range(1,k+1,2):
            # Monomials z^a zbar^b h^c span all homogeneous functions.
            for a in range(m+1):
                for b in range(m+1-a):
                    c=m-a-b; freq=a-b
                    assert freq%(k+1) or c%2
                    if not c: assert freq%(k+2)
                    totals[1]+=1
    for k in range(1,10):
        for t in range(2*k+1):
            for parts in compositions(t,k):
                order=[j for j,m in enumerate(parts) for _ in range(m)]
                order += [None]*(2*k-t)
                assert all(a is None or b is None or a!=b for a,b in zip(order,order[k:]))
                totals[2]+=1
    print('PASS: parity ranges, Fourier monomials, pair partitions:',*totals)

if __name__=='__main__':
    main()
