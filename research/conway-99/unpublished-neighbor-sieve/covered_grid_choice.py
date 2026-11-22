"""Check the local alternatives for a covered point lying on some rook grid."""

from collections import Counter
from itertools import combinations
from pathlib import Path
import gzip
import json

from covered_spread import PAIRS, check_leaf, row_system, verify_permutations


HERE = Path(__file__).resolve().parent
CATALOGUE = HERE.parents[1] / "conway-99-involution/uncovered-squares/covered-root/bounds.txt.gz"
EXCEPTION = 733007422869


def has_obstruction(targets):
    # Contract each degree-two source to an edge on the target nodes.
    for source, (b,c) in enumerate(targets):
        for head in (b,c):
            reachable = {b}
            allowed = [ends for label,ends in enumerate(targets)
                       if label not in (source,head) and source not in ends]
            for _ in range(6):
                for ends in allowed:
                    if reachable.intersection(ends):
                        reachable.update(ends)
            if c not in reachable:
                return True
    return False


def verify_fourteen():
    diagrams = 0
    for fours in range(4):
        degrees = [4]*fours + [2]*(7-2*fours) + [0]*fours
        targets = []

        def visit(i,remaining):
            nonlocal diagrams
            if i == 7:
                assert not any(remaining) and has_obstruction(targets)
                diagrams += 1
                return
            heads = [j for j in range(7) if remaining[j] and j != i
                     and (j >= i or i not in targets[j])]
            for pair in combinations(heads,2):
                new = [count - int(j in pair) for j,count in enumerate(remaining)]
                if any(count > 6-i-int(j>i) for j,count in enumerate(new)):
                    continue
                targets.append(pair)
                visit(i+1,new)
                targets.pop()

        visit(0,degrees)
    assert diagrams == 28944


def verify():
    verify_fourteen()
    with gzip.open(HERE / 'covered-grid-choice-cert.json.gz','rt') as f:
        certificates = {int(k):v for k,v in json.load(f).items()}
    census = Counter()
    seen = set()
    with gzip.open(CATALOGUE,'rt') as f:
        for line in f:
            code = int(line.split(' ',1)[0])
            assert code not in seen
            seen.add(code)
            edges = []
            for pos,(a,b) in enumerate(PAIRS):
                value = (code >> (2*pos)) & 3
                assert value < 3
                if value:
                    edges.append((a,b) if value == 1 else (b,a))
            if len(edges) == 21:
                continue
            groups = [[i for i,e in enumerate(edges) if e[0] == a] for a in range(7)]
            types = [(6-len(g), 6-len(g)-sum(b==a for _,b in edges))
                     for a,g in enumerate(groups)]
            if any(t == 6 or (t,g) == (4,1) for t,g in types):
                continue
            system = row_system(edges)
            proof = certificates.pop(code)
            census[21-len(edges)] += 1
            if code == EXCEPTION:
                assert sorted(types) == [(1,1)]*2+[(4,0)]*5
                group = next(g for g in groups if len(g)==5)
                assert verify_permutations(system,group,proof['tails'],True) == 10
            else:
                check_leaf(*system[:3],proof)
    assert len(seen) == 9057 and not certificates and census == {1:72,2:49,3:30,4:1}
    print('Verified 28,944 labeled low-degree diagrams, 151 direct exclusions, and 10 cycle exclusions.')


if __name__ == '__main__':
    verify()
