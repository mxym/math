"""Independent finite algebra check. No lattice solver or unknown inputs."""
from itertools import combinations, product
from math import gcd, prod, isqrt

def prime(x):
    return x > 1 and all(x % t for t in range(2, isqrt(x) + 1))

def root(x, n):
    # This checker only handles known tiny prime fixtures; use linear search.
    lo = 1
    while (lo+1)**n <= x:
        lo += 1
    return lo

safe = [p for p in range(13, 1200) if prime(p) and prime(2*p+1)]
supports = set()
for u, v in zip(safe, safe[1:]):
    supports.add(tuple(sorted({u, v, 2*u+1, 2*v+1})))
    if prime(4*u+3):
        supports.add(tuple(sorted({u, v, 2*u+1, 2*v+1, 4*u+3})))
cases = chains = stages = identities = radius_ok = largest_depth = 0
for S in sorted(supports):
    p0 = min(S)
    A = (max(S)+p0-1)//p0
    if p0 <= A:
        continue
    H = tuple(p for p in S if any(q%p==1 for q in S))
    D = prod(q for q in S if q not in H)
    g = (2*A-1).bit_length()
    for hidden_exps in product((1, 2, 4), repeat=len(H)):
        cases += 1
        for h in range(1, len(H)+1):
            for J in combinations(range(len(H)),h):
                stages += 1
                V = prod(H[i]**hidden_exps[i] for i in J)
                E = sum(hidden_exps[i] for i in J)
                e = max(hidden_exps[i] for i in J)
                B = root(V, E)
                assert min(H[i] for i in J) <= B <= max(H[i] for i in J)
                m = (V * D**e).bit_length()
                s = B.bit_length()-1-g
                M = V * D**e
                for i in J:
                    if hidden_exps[i] != e:
                        continue
                    p = H[i]
                    stack = [(p,1,0,0)]
                    while stack:
                        q, a, b, depth = stack.pop()
                        nxt = [r for r in S if r%q==1]
                        if nxt:
                            stack.extend((r,a*(r//q),b*(r//q)+1,depth+1) for r in nxt)
                            continue
                        chains += 1
                        largest_depth = max(depth,largest_depth)
                        assert 1 <= a <= A and 1 <= b <= len(S)*A
                        assert a*p+b==q and D%q==0 and gcd(a,D)==1
                        # CRT in the opposite order: C = B + b/a (mod D), B (mod V).
                        first = (B+b*pow(a,-1,D))%D
                        C = first+D*((B-first)*pow(D,-1,V)%V)
                        w = p-B
                        assert gcd((w+C)**e,M)%((p*q)**e)==0
                        assert abs(w) <= max(H)-min(H)
                        if s > 0:
                            n = 2*e*s
                            assert n < m and 2**s <= p0
                            assert ((p*q)**e)**m >= M**n
                            identities += 1
                            # Cancel e: |w|^(m^2) <= M^(4 e s^2).
                            radius_ok += abs(w)**(m*m) <= M**(4*e*s*s)
assert largest_depth >= 2
print("supports",len(supports),"fixtures",cases,"residuals",stages,
      "terminal paths",chains,"maximum depth",largest_depth)
print("exact beta checks",identities,"toy roots inside certified radius",radius_ok)
