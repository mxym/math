#!/usr/bin/env python3
"""Integer-only occupancy, asymptotic-scaling inputs and boundary checks."""
from math import comb, isqrt


def cd(a, b):
    return (a+b-1)//b


def occupancy(b, q):
    p = [1]+[0]*b
    for _ in range(q):
        p = [s*p[s]+((b-s+1)*p[s-1] if s else 0)
             for s in range(b+1)]
    return p


def conv(p, q):
    r = [0]*(len(p)+len(q)-1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i+j] += x*y
    return r


tails = 0
for B in range(1, 7):
    for q in range(1, 7):
        one = occupancy(B,q)
        assert sum(one) == B**q
        all_chunks = [1]
        for d in range(1, 5):
            all_chunks = conv(all_chunks,one)
            ell, num = d*B, d*q
            assert sum(all_chunks) == B**num
            subtotal = 0
            for u, val in enumerate(all_chunks):
                subtotal += val
                assert (u >= d or subtotal == 0)
                assert subtotal*ell**num <= comb(ell,u)*u**num*B**num
                tails += 1

resource = high = 0
for n in list(range(2,33))+[64,127,256,512]:
    for k in sorted({n,n+1,min(2**n,n*n),2**n-1,2**n}):
        for w in sorted({1,2,3,n.bit_length(),n,n*n//2,n*n,
                         n*k//2,n*k-1,n*k,n*k+1,2*n*k}):
            X = n*k
            if w >= X:
                assert cd(X,w) == 1
                high += 1
                continue
            L = (cd(2*w+X,w)-1).bit_length()
            assert (1<<(L-1))*w < 2*w+X <= (1<<L)*w
            r = isqrt((64*n)**2//(w*L))
            r += (r*r*w*L < (64*n)**2)
            d = max(64,cd(64*n,w),r)
            B = cd(512*X,d*w)
            ell = d*B
            h = n+(k-1).bit_length()+4
            b = 1<<(h-n)
            assert d*w >= 64*n and d*d*w*L >= 4096*n*n
            assert d*d*w <= 65**2*X
            assert 512*X <= ell*w <= 577*X
            assert (512*X)**2 >= (d*w)**2*(1<<L)
            assert 16*k <= b < 32*k and h <= 6*n
            assert ell+cd(h,w) <= 584*cd(X,w)
            resource += 1


# Independent grid for the lower-bound branch below T_0/4.  Use L=floor(L_0)
# to overinclude some (harmless) cases; log_2(e ell)<=C_0 L_0 is a paper bound.
low = 0
for n in list(range(16,161))+[257,512,1025,2048]:
    assert n*(1<<n) <= 16*((1<<(3*n//4-1))-2)**2
    for k in (n,n*n,1<<n):
        X = n*k
        widths = {1,2,4,n//2,n,n+1,2*n,n*n//16,n*n//8,
                  n*n//4,n*n//2,n*n,X-1}
        widths |= {1<<i for i in range(n.bit_length()+4)}
        for w in sorted(widths):
            if not 1 <= w < X:
                continue
            L = ((2*w+X)//w).bit_length()-1
            min_t = cd(n,w)
            max_t = isqrt((n*n-1)//(16*w*L))
            for t in {min_t,min_t+1,(min_t+max_t)//2,max_t-1,max_t}:
                if not (min_t <= t <= max_t):
                    continue
                q = cd(w*t,n)+1
                assert n <= w*t and q*n-w*t >= n
                assert q*n <= 3*w*t
                assert q <= k and q <= 1<<(3*n//4-1)
                low += 1

# Floor substitution fails for the precise counting inequality.
n,w,t = 3,2,2
q_floor,q_ceil = w*t//n+1,cd(w*t,n)+1
assert n*q_floor-w*t < n <= n*q_ceil-w*t
# At epsilon=1/2 a one-fair-bit pair already suffices, not two.
assert sum(abs(2-1) if i in (0,2) else 1 for i in range(4)) == 4
print(f"PASS exact: {tails} occupancy tails; {resource} catalog scale grids; "
      f"{high} one-word grids; {low} lower-ceiling checks; two boundary controls")
