#!/usr/bin/env python3
"""Discovery/generation, NOT the trusted verifier; all arithmetic integral."""
import argparse
import gzip
import json
from collections import deque
from math import gcd, isqrt, lcm
from pathlib import Path

HERE = Path(__file__).resolve().parent
F6 = ((-1, -1), (-1, 0), (0, -1), (0, 1), (1, 0), (1, 1))
F8 = tuple((a, b) for a in (-1, 0, 1) for b in (-1, 0, 1) if a or b)
REV = tuple(F8.index((-a, -b)) for a, b in F8)
GS = ((2, 0), (1, -1), (3, 1), (2, -1), (4, 1), (3, -1))


def norm(p):
    a, b = p
    return a*a-a*b+b*b


def save(name, obj):
    data = json.dumps(obj, separators=(',', ':'), sort_keys=True).encode('ascii') + b'\n'
    (HERE / name).write_bytes(gzip.compress(data, compresslevel=9, mtime=0))
    print('wrote', name, 'uncompressed bytes', len(data), flush=True)


def squarefree(q):
    for p in range(2, isqrt(q)+1):
        if q % (p*p) == 0:
            return False
    return True


def get_path(v, parent):
    indices = []
    while parent[v] is not None:
        v, index = parent[v]
        indices.append(index)
    return indices[::-1]


def witness(q):
    def is_allowed(p):
        return gcd(norm(p), q) == 1
    def bfs(root):
        seen = {root: root}
        parent = {root: None}
        todo = deque([root])
        while todo:
            v = todo.popleft()
            for j, (dx, dy) in enumerate(F8):
                physical = seen[v][0]+dx, seen[v][1]+dy
                y = physical[0] % q, physical[1] % q
                if not is_allowed(y):
                    continue
                if y in seen:
                    if seen[y] != physical:
                        steps = get_path(v, parent) + [j]
                        steps += [REV[i] for i in reversed(get_path(y, parent))]
                        return [root[0], root[1]], steps, seen
                else:
                    seen[y] = physical
                    parent[y] = v, j
                    todo.append(y)
        return None, None, seen
    # 1 is a unit, so this residue is always permitted.
    root = (1 % q, 0)
    base, indices, visited = bfs(root)
    if indices is not None:
        return {'q': q, 'base': base, 'steps': indices}
    searched = set(visited)
    for a in range(q):
        for b in range(q):
            root = (a, b)
            if root in searched or not is_allowed(root):
                continue
            base, indices, visited = bfs(root)
            if indices is not None:
                return {'q': q, 'base': base, 'steps': indices}
            searched.update(visited)
    raise RuntimeError(f'No nonzero voltage cycle at q={q}')


def allowed_mask(p, mask):
    a, b = p
    conditions = (
        (a % 2 == 0 and b % 2 == 0),
        (a+b) % 3 == 0,
        (a+4*b) % 7 == 0,
        (a+2*b) % 7 == 0,
        (a+9*b) % 13 == 0,
        (a+3*b) % 13 == 0,
    )
    return all(not(mask & (1 << j)) or not conditions[j] for j in range(6))


def endpoint_components(mask):
    Q = lcm(*(p for j, p in enumerate((2, 3, 7, 7, 13, 13)) if mask & (1 << j)))
    allowed = {(a, b) for a in range(Q) for b in range(Q)
               if allowed_mask((a, b), mask)}
    globally_seen = set()
    components = []
    for root in sorted(allowed):
        if root in globally_seen:
            continue
        lifts = {root: root}
        todo = deque([root])
        while todo:
            v = todo.popleft()
            x, y = lifts[v]
            for dx, dy in F8:
                newpoint = x+dx, y+dy
                residue = newpoint[0] % Q, newpoint[1] % Q
                if residue not in allowed:
                    continue
                if residue in lifts:
                    if lifts[residue] != newpoint:
                        raise RuntimeError(f'nonzero-voltage cycle at endpoint mask={mask}')
                else:
                    if residue in globally_seen:
                        raise RuntimeError('cross-component residue')
                    lifts[residue] = newpoint
                    todo.append(residue)
        globally_seen.update(lifts)
        components.append(sorted([list(p) for p in lifts.values()]))
    if len(globally_seen) != len(allowed):
        raise RuntimeError('incomplete endpoint')
    sizes = [len(comp) for comp in components]
    return {'mask': mask, 'q': Q, 'components': components}, \
           (len(allowed), len(components), max(sizes), sum(sizes))


def mul(p, z):
    a, b = p
    c, d = z
    return (a*c-b*d, a*d+b*c-b*d)


def special_closure(steps, gen_count, q):
    exceptions = {mul(u, g) for g in GS[:gen_count] for u in F6}
    closure = set(exceptions)
    queue = deque(exceptions)
    while queue:
        p = queue.popleft()
        for d in steps:
            y = p[0]+d[0], p[1]+d[1]
            if y not in closure and gcd(norm(y), q) == 1:
                closure.add(y)
                queue.append(y)
    return {'q': q, 'steps': len(steps), 'points': [list(p) for p in sorted(closure)]}


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--lower-start', type=int)
    ap.add_argument('--lower-end', type=int)
    ap.add_argument('--endpoints', action='store_true')
    ap.add_argument('--closures', action='store_true')
    args = ap.parse_args()
    if args.lower_start is not None:
        lo, hi = args.lower_start, args.lower_end
        out = []
        for q in range(lo, hi+1):
            if squarefree(q):
                out.append(witness(q))
            if q % 30 == 0:
                print('generated through', q, flush=True)
        save(f'lower_cycles_{lo}_{hi}.json.gz', out)
        print('cycles', len(out), flush=True)
    if args.endpoints:
        for mask in (63, 23, 27, 39, 43):
            proof, stats = endpoint_components(mask)
            save(f'endpoint_{mask}.json.gz', proof)
            print('endpoint stats', mask, stats, flush=True)
    if args.closures:
        for label, steps, count, q in ((6, F6, 2, 6), (8, F8, 6, 546)):
            obj = special_closure(steps, count, q)
            save(f'exceptional_closure_{label}.json.gz', obj)
            print('closure stats', label, len(obj['points']), flush=True)
