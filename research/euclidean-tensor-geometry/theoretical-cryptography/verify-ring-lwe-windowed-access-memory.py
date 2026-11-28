#!/usr/bin/env python3
"""Synthetic finite tapes for bounded-window and outstanding-position simulations."""
from itertools import product
from math import comb, exp, isqrt, log
from random import Random

modes=0
for d in range(1,8):
    n=isqrt(d)
    mode=[u for u in product(range(-n,n+1),repeat=d) if sum(x*x for x in u)<=d]
    assert all(sum(abs(x) for x in u)<=d for u in mode)
    assert len(mode)<=2**d*comb(2*d,d)<=8**d
    modes+=len(mode)

rng=Random(2005)
window_steps=buffer_steps=0
def raw(token, seed, i):
    # This arbitrary finite interpretation models immutable position seeds,
    # not a sampler for any hidden-label distribution.
    return (token*1237+seed*3812+i*1171)%104729

for trial in range(300):
    T=rng.randrange(4,35)
    B=rng.randrange(0,T)
    P=rng.randrange(1,5)
    tokens=[0]+[rng.randrange(128) for _ in range(T)]
    seeds=[0]+[rng.randrange(1024) for _ in range(T)]
    data=[0]+[raw(tokens[i],seeds[i],i) for i in range(1,T+1)]
    def next_request(H,s,j,step,p):
        opts=list(range(max(1,H-B),T+1))
        return opts[(7*s+17*j+step**2+13*p)%len(opts)]
    def go(buffered):
        s=trial%211
        hist=[]
        for p in range(P):
            H,j=0,0
            read=0
            buf={}
            for step in range(3*T):
                i=next_request(H,s,j,step,p)
                H=max(H,i)
                if buffered:
                    while read<H:
                        read+=1
                        buf[read]=tokens[read]
                        buf.pop(read-B-1,None)
                        assert len(buf)<=B+1
                    assert i in buf
                    x=raw(buf[i],seeds[i],i)
                else:
                    x=data[i]
                s=(s*33+i*13+x+p+step)%211
                j=i
                hist.append((p,i,x,s))
        return hist,s
    plain,cb=go(False)
    test,cd=go(True)
    assert plain==test and cb==cd
    window_steps+=len(plain)

for trial in range(400):
    T=rng.randrange(3,45)
    B=rng.randrange(0,T)
    P=rng.randrange(1,5)
    tokens=[0]+[rng.randrange(443) for _ in range(T)]
    seeds=[0]+[rng.randrange(787) for _ in range(T)]
    def make(buffered):
        state=trial%177
        hist=[]
        for p in range(P):
            unseen=set(range(1,T+1))
            cursor=0
            buf={}
            H=0
            for j in range(1,T+1):
                opts=sorted(i for i in unseen if max(H,i)-j<=B)
                assert opts
                i=opts[(21*state+11*p+3*j)%len(opts)]
                H=max(H,i)
                if buffered:
                    while cursor<H:
                        cursor+=1
                        buf[cursor]=tokens[cursor]
                        assert len(buf)<=B+1
                    tok=buf.pop(i)
                    assert len(buf)<=B
                else:
                    tok=tokens[i]
                x=raw(tok,seeds[i],i)
                unseen.remove(i)
                state=(state*91+12*i+x+p)%177
                hist.append((p,i,state))
            if buffered: assert not buf and cursor==T
        return hist,state
    a,b=make(False),make(True)
    assert a==b
    buffer_steps+=len(a[0])

# The probability and alphabet slack is order d, not d log d in stored bits.
slack=0
for q,d in product((3,5,9,15), (64,128,256,512)):
    b=1/(100*d)
    ln_tail=log(8)+d/2*log(b)+3*d*b**.5
    assert ln_tail<-d
    alphabet=1+q**(2*d)*(8**d+1)
    n=alphabet.bit_length()+8*d
    assert n<= (15+2*q.bit_length())*d
    slack+=1

print("PASS finite lattice modes / adaptive window reads / adaptive outstanding reads / symbol margins:",
      modes,window_steps,buffer_steps,slack)
