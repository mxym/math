"""Classify twelve-site components and verify two integer infeasibility certificates."""
from collections import Counter
from itertools import combinations, permutations, product


MATES = ((1,0,3,2),(2,3,0,1),(3,2,1,0))
IDENTITY = (0,1,2,3)
CERTIFICATES = {
    (MATES[0], MATES[0], MATES[0], (0,2,1,3)): {
        (0,9): (-1,-1,-1,1,-1,-1,1,1,0,-1,-1,1),
        (1,5): (-1,0,-1,1,-1,0,1,1,-1,-1,-1,1),
        (1,8): (0,-1,-1,1,-1,-1,1,1,-1,-1,-1,1),
        (2,10): (2,0,-2,-2,2,2,0,-2,2,0,-2,-2),
        (5,9): (-1,-1,-1,1,-1,0,1,1,-1,0,-1,1),
    },
    (MATES[0], MATES[0], MATES[1], IDENTITY): {
        (1,8): (0,-1,1,1,-1,-1,1,1,-1,-1,0,0),
        (2,11): (0,0,0,0,0,0,0,0,-1,0,0,0),
        (3,10): (0,0,0,0,0,0,0,0,-1,0,0,0),
        (5,8): (-1,-1,1,1,0,-1,1,1,-1,-1,0,0),
        (6,11): (0,0,0,0,0,0,0,0,-1,0,0,0),
        (7,10): (0,0,0,0,0,0,0,0,-1,0,0,0),
        (8,9): (-1,-1,1,1,-1,-1,1,1,-1,-1,0,0),
    },
}


def chart(p, q, r, return_map):
    graph = [set() for _ in range(12)]
    for i in range(4):
        for a,b in ((i,p[i]),(4+i,4+q[i]),(8+i,8+r[i]),
                    (i,4+i),(4+i,8+i),(8+i,return_map[i])):
            graph[a].add(b)
            graph[b].add(a)
    return graph


def connected(graph):
    reached = {0}
    pending = [0]
    while pending:
        new = graph[pending.pop()] - reached
        reached.update(new)
        pending.extend(new)
    return len(reached) == 12


def multiplicities(graph):
    return {(a,b): 2 - int(b in graph[a]) - len(graph[a] & graph[b]) - int(a//4 == b//4)
            for a,b in combinations(range(12),2)}


def code(parameters, ordered_wings=False):
    graph = chart(*parameters)
    keys = []
    for a,b,c in ((0,1,2),) if ordered_wings else permutations(range(3)):
        for order in permutations(range(4*a,4*a+4)):
            second = [next(j for j in graph[i] if j//4 == b) for i in order]
            third = [next(j for j in graph[i] if j//4 == c) for i in second]
            labels = list(order) + second + third
            keys.append(tuple(int(labels[j] in graph[labels[i]]) for i,j in combinations(range(12),2)))
    return min(keys)


def verify_dual(parameters, weights):
    graph = chart(*parameters)
    count = {pair:m for pair,m in multiplicities(graph).items() if m}
    assert min(count.values()) > 0 and sum(count.values()) == 60
    demand = {e: [2 - int(i in e) - len(graph[i].intersection(e)) for i in range(12)]
              for e in count}
    assert all(min(row) >= 0 and sum(row) == 16 for row in demand.values())
    zero = (0,)*12
    left = sum(count[e]*sum(a*b for a,b in zip(weights[e],demand[e])) for e in weights)
    right = 0
    for e,f in combinations(count,2):
        if any(demand[e][i] == 0 for i in f) or any(demand[f][i] == 0 for i in e):
            continue
        value = sum(weights.get(e,zero)[i] for i in f) + sum(weights.get(f,zero)[i] for i in e)
        right += min(count[e],count[f])*max(value,0)
    assert left > right
    return left, right


def main():
    named, unnamed = {}, {}
    for q,r,return_map in product(MATES,MATES,permutations(range(4))):
        parameters = MATES[0],q,r,return_map
        graph = chart(*parameters)
        if not connected(graph) or min(multiplicities(graph).values()) < 0:
            continue
        key = code(parameters,ordered_wings=True)
        if key not in named:
            name = code(parameters)
            named[key] = name
            unnamed.setdefault(name,parameters)
    assert (len(named),len(unnamed)) == (35,15)
    excluded = {code(p) for p in CERTIFICATES}
    assert len(excluded) == 2 and sum(v in excluded for v in named.values()) == 6
    for parameters,weights in CERTIFICATES.items():
        print(parameters, verify_dual(parameters, weights))
    two_grids = multiplicities(chart(MATES[0],MATES[0],MATES[0],IDENTITY))
    assert Counter(two_grids.values()) == {0:30,1:12,2:24}
    print("35 wing-ordered and 15 unordered connected types; six ordered / two unordered exclusions.")


if __name__ == "__main__":
    main()
