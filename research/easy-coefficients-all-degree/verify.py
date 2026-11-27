#!/usr/bin/env python3
"""Finite checks of source indexing and the closed-walk proof. No dependencies."""

from itertools import product


def check(condition, message):
    if not condition:
        raise ValueError(message)


def split_binary(column, widths, generators, linear):
    """Independently follow the published column construction in §4.1."""
    flags = f"{column:0{sum(widths)}b}" if widths else ""
    left = right = ""
    exponent = linear
    for width, D in zip(widths, generators):
        u = int(flags[:width], 2)
        flags = flags[width:]
        padded = f"{u:0{width + 1}b}"
        subtract = 2**width if padded[1] == "1" else 0
        v = 2*u-subtract
        for j in (1+d for d in D[1:-1]):
            pos = width+1-j+2                 # one-based source index
            if padded[pos-1] == "1":
                v -= 2**(j-1)
        w = 2*u+1-subtract
        left += f"{v:0{width}b}"
        right += f"{w:0{width}b}"
        exponent += int(subtract != 0)
    return (int(left or "0", 2), 1), (int(right or "0", 2), (-1)**exponent)


def pending_transition(column, widths, generators, linear):
    """Separate bit recurrence on unpadded states."""
    suffix = column
    blocks = []
    for L, D in reversed(tuple(zip(widths, generators))):
        blocks.append((L, D, suffix & ((1 << L)-1)))
        suffix >>= L
    output = []
    for bit in (0, 1):
        target = 0
        exp = bit * linear
        for L, D, u in reversed(blocks):
            exp += bit*((u >> (L-1)) & 1)
            v = bit
            for k in range(1, L):
                v |= (((u >> (k-1)) & 1) * (bit if k in D else 1)) << k
            target = (target << L) | v
        output.append((target, (-1)**exp))
    return tuple(output)


def history_graph(generators, linear):
    L = max((D[-1] for D in generators), default=0)
    mask = (1 << L)-1
    graph = {}
    for history in range(1 << L):
        exponent = linear
        for D in generators:
            exponent += all((history >> (D[-1]-d-1)) & 1 for d in D[:-1])
        graph[history] = (((history << 1) & mask, 1),
                          (((history << 1) | 1) & mask, (-1)**exponent))
    return graph


def trim_zero_rows(graph):
    S = set(graph)
    shard = []
    while True:
        T = {v for u in S for v,s in graph[u] if v in S}
        if T == S:
            return {u: tuple((v,s) for v,s in graph[u] if v in S) for u in S}, shard
        shard.append(len(S)-len(T))
        S = T


def traces(graph, periods):
    result = [0]*periods
    for origin in graph:
        active = {origin:1}
        for i in range(periods):
            nxt = {}
            for u, w in active.items():
                for v,s in graph[u]:
                    nxt[v] = nxt.get(v,0)+w*s
            active = {v:w for v,w in nxt.items() if w}
            result[i] += active.get(origin,0)
    return result


def truth_sum(generators, linear, n):
    return sum((-1)**(linear*sum(word)+sum(
        all(word[(t+d) % n] for d in D) for D in generators for t in range(n)))
        for word in product((0,1), repeat=n))


def det_coefficients(power_traces):
    """Ascending coefficients of det(I-zA) via exact Newton identities."""
    c = [1]
    for k in range(1,len(power_traces)+1):
        num = -sum(c[k-i]*power_traces[i-1] for i in range(1,k+1))
        check(num % k == 0,"noninteger determinant coefficient")
        c.append(num//k)
    while len(c)>1 and c[-1]==0:
        c.pop()
    return c


def test(generators, linear, periods=7):
    widths = tuple(D[-1] for D in generators)
    graph = {u:split_binary(u,widths,generators,linear) for u in range(1 << sum(widths))}
    for u, edges in graph.items():
        check(edges == pending_transition(u,widths,generators,linear),("source column",u))
        if widths:
            check(edges[0][0] != edges[1][0],"source assignments collided")
    trimmed,counts = trim_zero_rows(graph)
    a = traces(trimmed,periods)
    b = traces(history_graph(generators,linear),periods)
    t = [truth_sum(generators,linear,n) for n in range(1,periods+1)]
    check(a==b==t,("signed trace mismatch",generators,linear,a,b,t))
    if widths:
        # Matrices share det(I-zA), even if retaining different zero dimensions.
        B = history_graph(generators,linear)
        c=det_coefficients(traces(trimmed,len(trimmed)))
        check(c==det_coefficients(traces(B,len(B))),"characteristic multiset mismatch")
    return a,trimmed,counts


def main():
    G = ((0,1,5),(0,1),(0,5))
    a,S,counts=test(G,0,12)
    check(counts==[1664,192,96,48,16] and len(S)==32,"source row deletions")
    check(a[:8]==[0,4,6,8,0,28,0,32],"source example traces")
    augmented=[(1<<n)+v for n,v in enumerate(traces(S,len(S)+1),start=1)]
    coeff=det_coefficients(augmented)
    check(coeff==[1,-2,-2,2,4,4,-8],"source sample characteristic polynomial")
    print("Author example: 2048 to 32 signed states; traces",a)
    print("Augmented nonzero characteristic factor: (X-2)(X^2-2)(X^3-2).")

    count=0
    pool=[(0,)+tuple(i+1 for i,b in enumerate(bits) if b)+(L,)
          for L in range(1,4) for bits in product((0,1),repeat=L-1)]
    for choice in product((0,1),repeat=len(pool)):
        gs=tuple(g for g,s in zip(pool,choice) if s)
        if sum(g[-1] for g in gs)>10:
            continue
        for l in (0,1):
            test(gs,l)
            count+=1
    check(count==180,"incorrect family count")

    A=(0,1,3)
    for G in ((A,A),(A,A,(0,4)),((0,1,4,5,7),(0,2,4)),
              ((0,2,4),(0,1,4,5,7))):
        for l in (0,1):
            test(G,l)
    print("PASS: 180 complete small-window cases plus 8 mixed-width, reordered or repeated cases.")

    # Deliberately wrong sign to confirm the periodic truth check responds.
    a,S,counts=test(((0,1,2),),0)
    bad={u:tuple((v,(-s if i==1 else s)) for i,(v,s) in enumerate(e))
         for u,e in S.items()}
    check(traces(bad,len(a))!=a,"altered emission was not detected")
    print("PASS negative control: altered right-edge sign detected.")


if __name__ == "__main__":
    main()
