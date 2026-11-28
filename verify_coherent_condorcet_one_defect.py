#!/usr/bin/env python3
"""Exact maximum with at most one middle-letter peak/pit exception at n=9."""
from itertools import combinations, permutations
from sys import argv
from verify_coherent_condorcet_maxima import inv_pos

N = 9
LIMIT = 476
TRIPLES = tuple(combinations(range(N), 3))
PAIRS = tuple((a,c) for a,c in combinations(range(N),2) if c > a + 1)
EXCEPTION = (5,7,8)  # zero-based: 6,8,9 in the statement
STYLE_VALUES = [0,1,2,10,5,26,37,1,1,5,5,13,21,0,1,1,5,9,1,1,3,5,0,1,2,1,1,1]


def contains_middle_at_top(pos, T):
    a,b,c = T
    return pos[b] < min(pos[a],pos[c])


def classify_permutations():
    """List positions of all avoiders, and all exactly-one-321 orders."""
    clean, exceptional = [], {T:[] for T in TRIPLES}
    for p in permutations(range(N)):
        q = tuple(inv_pos(p))
        found = None
        for a,b,c in TRIPLES:
            if q[c] < q[b] < q[a]:
                if found is not None:
                    break
                found = (a,b,c)
        else:
            if found is None:
                clean.append(q)
            else:
                exceptional[found].append(q)
    assert len(clean) == 4862 and sum(map(len,exceptional.values())) == 6188
    return clean, exceptional


def make_groups(P, exception):
    rows = [{} for p in PAIRS]
    for i,q in enumerate(P):
        for (a,c), by_style in zip(PAIRS, rows):
            if q[c] < q[a]:
                key = sum(1 << (b-a-1) for b in range(a+1,c)
                          if (a,b,c) != exception and q[b] < q[c])
                by_style[key] = by_style.get(key,0) | (1 << i)
    return [tuple(row.values()) for row in rows]


def certify(P, exception):
    """Exhaust the ordered style branches, pruning only at proved upper bounds."""
    groups = make_groups(P, exception)
    masks = [sum(g) for g in groups]
    seen = set()
    visits = 0

    def run(S):
        nonlocal visits
        visits += 1
        size = S.bit_count()
        if size <= LIMIT or S in seen:
            return
        seen.add(S)
        choices = []
        for packet,g in zip(masks,groups):
            C = S & packet
            count = C.bit_count()
            if count <= 1:
                continue
            pieces = [(h,(h&C).bit_count()) for h in g if h&C]
            if len(pieces) < 2:
                continue
            loss = count - max(x for h,x in pieces)
            if size - loss <= LIMIT:
                return
            choices.append((loss,C,count,pieces))
        if not choices:
            raise AssertionError((exception, size))
        choices.sort(key=lambda z:-z[0])
        remaining, upper = S, size
        for loss,C,count,pieces in choices:
            V = remaining & C
            if V:
                upper -= (loss if V == C else
                          V.bit_count() - max((V&h).bit_count() for h,x in pieces))
                if upper <= LIMIT:
                    return
                remaining ^= V
        loss,C,count,pieces = min(choices,key=lambda z:(
            sum(size-z[2]+x > LIMIT for h,x in z[3]),-z[0]))
        for h,x in sorted(pieces,key=lambda z:-z[1]):
            if size-count+x > LIMIT:
                run((S^C)|(S&h))

    run((1 << len(P))-1)
    return visits


def witness():
    """Test the concrete rule string directly against all permutations."""
    style = dict(zip(PAIRS,STYLE_VALUES))
    n0 = n1 = 0
    for p in permutations(range(N)):
        q = inv_pos(p)
        if contains_middle_at_top(q, EXCEPTION):
            continue
        for a,b,c in TRIPLES:
            if (a,b,c) == EXCEPTION:
                continue
            if style[a,c] >> (b-a-1) & 1:
                if q[c] < min(q[a],q[b]):
                    break
            elif q[a] > max(q[b],q[c]):
                break
        else:
            n0 += 1
            a,b,c = EXCEPTION
            n1 += int(q[c] < q[b] < q[a])
    assert n0 == LIMIT and n1 > 0
    print('Direct witness:',n0, 'orders, including',n1,'exceptional 321 patterns.',flush=True)


def main():
    witness()
    clean, exc = classify_permutations()
    ids = list(map(int,argv[1:])) if len(argv)>1 else list(range(len(TRIPLES)))
    visits = 0
    for j in ids:
        assert 0 <= j < len(TRIPLES)
        T = TRIPLES[j]
        base = [q for q in clean if not contains_middle_at_top(q,T)]
        count = certify(base + exc[T], T)
        visits += count
        print(j,tuple(x+1 for x in T),len(base),len(exc[T]),count,flush=True)
    print('PASS',len(ids),'instances;',visits,'states checked.',flush=True)


if __name__ == '__main__':
    main()
