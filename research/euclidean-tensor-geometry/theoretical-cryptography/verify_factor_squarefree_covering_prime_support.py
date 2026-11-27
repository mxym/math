"""Exact certificate for FactorSquarefreeCoveringPrimeSupport.md."""
from fractions import Fraction as F
from math import isqrt, prod

N = 12000
W = 10**36
# Each pair is (last absolute prime index, p*delta);
# None means delta=1/2. Past the last block, delta=1/2.
TABLE = ((2,0),(3,1),(4,2),(7,4),(11,8),(19,16),(31,32),
         (50,64),(54,None),(80,128),(97,None),(125,256),(141,None))


def first_primes():
    b = bytearray(b"\x01")*200001
    b[:2] = b"\x00\x00"
    for p in range(2,isqrt(len(b)-1)+1):
        if b[p]:
            b[p*p::p] = b"\x00"*((len(b)-1-p*p)//p+1)
    ps = [p for p, prime in enumerate(b) if prime][:N]
    assert len(ps) == N and ps[140] == 811 and ps[141] == 821 and ps[144] == 829
    assert prod(ps[:142]) > 10**338
    return ps


def delta(k,p):
    for end,j in TABLE:
        if k <= end:
            return F(1,2) if j is None else F(j,p)
    return F(1,2)


def exact_joint(rank_profile, ds):
    """Finite backward two-state profile; F_p(t) affine for t>=1024."""
    h = 10
    lo = [F(0)]*h
    lin = const = F(0)
    for p in reversed(rank_profile):
        d = ds[p]
        e = int(p == 5)
        active = p >= 5
        c = 1/(1-d)
        assert 0 <= d <= F(1,2) and c <= p
        assert not active or (1<<h)-e >= p*d
        continuation = lo+[lin*(1<<h)+const]
        new = []
        for s in range(h):
            t = 1<<s
            a = F(t-e,p) if active else F(0)
            cap = 1/(1-min(a,d))
            g = c*max(0,a-d)
            low,high = continuation[s:s+2]
            x = (high-low)/p
            assert x >= 0
            new.append(g+low+max(cap*x,c*x-(c-cap)/c))
        lo = new
        lin = lin*(1+c/p)+(c/p if active else 0)
        const = const-(c*(F(e,p)+d) if active else 0)
    return lo[0]


def ceildiv(x,y):
    return -(-x//y)


def scalar_excluding(ps, ds, missing):
    """Independent comparison, integer round-up and explicit infinite tail."""
    h = 18
    dist = [W]+[0]*h
    moment1 = moment3 = W
    budget = 0
    for p in ps:
        if p == missing:
            continue
        d = ds[p]
        a = 1/(p*(1-d))
        u,v = a.numerator,a.denominator
        assert 0 < u <= v
        if p >= 5:
            k = d*p + int(p == 5)
            m,n = k.numerator,k.denominator
            assert k < 1<<h
            maj = n*moment1-m*W
            for s,z in enumerate(dist):
                diff = m-(n<<s)
                if diff <= 0:
                    break
                maj += diff*z
            assert maj >= 0
            budget += ceildiv(u*maj,v*n)
        dist = [ceildiv((v-u)*x+u*y,v)
                for x,y in zip(dist,[0]+dist)]
        moment1 = ceildiv((v+u)*moment1,v)
        moment3 = ceildiv((v+7*u)*moment3,v)
    tail = ceildiv(32*moment3,16200*N*N)
    return F(budget+tail,W)


def run():
    ps = first_primes()
    ds = {p:delta(n,p) for n,p in enumerate(ps,1)}
    rank_results = []
    for mask in range(16):
        low = [p for i,p in enumerate(ps[:4]) if (mask >> i)&1]
        pack = low+ps[4:4+141-len(low)]
        assert len(pack) == 141
        bound = exact_joint(pack,ds)
        assert 0 <= bound < F(9999,10000)
        rank_results.append(bound)
    assert rank_results[15] == max(rank_results)
    print("141-prime maximum upper certificate:",float(max(rank_results)))
    for p in ps[:4]:
        bound = scalar_excluding(ps,ds,p)
        assert 0 <= bound < F(3,4)
        print(f"Prime {p} excluded, infinite upper certificate:",float(bound))
    print("Exact strict rationals: all 16 prime-profile cases < 9999/10000;"
          " all 4 missing-prime infinite cases < 3/4.")


if __name__ == "__main__":
    run()
