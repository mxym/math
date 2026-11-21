"""Exact structural controls, not a numerical test of log asymptotics. Standard Python -O."""
from math import gcd, isqrt

def must(ok):
    if not ok:
        raise RuntimeError("fixture failed")

def factors(n):
    out = []
    t = 2
    while t*t <= n:
        while n % t == 0:
            out.append(t)
            n //= t
        t += 1
    if n > 1:
        out.append(n)
    return out

lim = 400
fac = [[]] + [factors(n) for n in range(1, lim+1)]
lam = [0] + [(-1)**len(fac[n]) for n in range(1, lim+1)]
prime = {i for i in range(2, lim+1) if fac[i] == [i]}
mob = lambda n: 0 if len(set(fac[n])) != len(fac[n]) else (-1)**len(fac[n])
for n in range(1, lim+1):
    must(lam[n] == sum(mob(n//(j*j)) for j in range(1, isqrt(n)+1) if n%(j*j)==0))

menus = fp = weights = cells = kernels = 0
for N in range(12, lim+1, 2):
    V = {p for p in prime if 3 <= p <= N-3 and gcd(N,p)==1}
    E = {p: set(fac[N-p]) for p in V}
    ep = {p for p in V if N-p in prime}
    true = {p for p in prime if N-p in prime}
    must(len(true-ep) <= 1 and ep <= true)
    for Z in (3,5,9,18):
        S = {p for p in V if p<=Z}
        H = {p for p in V-S if E[p].isdisjoint(S)}
        U = {p for p in V-S if E[p] <= H}
        # Independent forward walk, including length zero.
        for p in V:
            reached = {p} | E[p]
            reached |= {u for y in E[p] for u in E[y]}
            must((p in U) == reached.isdisjoint(S))
        must(H == {p for p in V if p>Z and min(fac[N-p])>Z})
        lost = true-U
        must(len(lost) <= 2*len(S)+1)
        false = U-ep
        for x in false:
            for q in E[x]:
                m = (N-x)//q
                must(q in H and set(fac[m]) <= H and min(m,q,x)>Z and m*q==N-x)
                for t in sorted(prime):
                    if t>Z: break
                    if t<5: continue
                    must(gcd(m,t)==1)
                    roots = {0,N%t,(N*pow(m,-1,t))%t}
                    size = 1 if N%t==0 else (2 if (m-1)%t==0 else 3)
                    must(len(roots)==size and q%t not in roots)
                    kernels += 1
            fp += 1
        wp = sum(1+lam[N-p] for p in U)
        wm = sum(1-lam[N-p] for p in U)
        must(wp<=2*len(false) and wm>=2*len(ep&U))
        must(wp+wm==2*len(U) and all(1+lam[N-p]==0 for p in ep))
        weights += len(U)
        menus += 1
    if N%6: continue
    for d in range(1, min(50,N//3)+1):
        # Aggregate signed histograms independently by prime starts and by residual cofactor.
        for h in (1,3,4):
            for lower,upper in [(1,N//d),(2,N//(3*d)),(10,45)]:
                a = [0]*h
                b = [0]*h
                for p in V:
                    n = N-p
                    k,rem = divmod(n,d)
                    if not rem and lower<=k<=upper: a[k%h] += lam[n]
                for k in range(max(1,lower),min(upper,(N-1)//d)+1):
                    p = N-d*k
                    if p in prime and 3<=p<=N-3 and gcd(p,N)==1:
                        b[k%h] += lam[d]*lam[k]
                must(a==b)
                cells += h
must(fp>0 and kernels>0 and cells>100)
print("PASS",menus,"menus;",fp,"false survivors;",kernels,"collision checks;",weights,"included starts;",cells,"localized divisor cells")
