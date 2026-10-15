"""Plain-integer checker for coverage DAGs; no SMT library is imported.

Induction on |dom(S)| proves that each certified node covers all labeled
subsamples below it. Root coverage therefore covers all realizable samples
of the listed total class, not just its full rows.
"""
from pathlib import Path
import argparse
import hashlib
import json
from itertools import combinations

def require(condition):
    if not condition:
        raise ValueError('Invalid finite coverage certificate')

def check(data):
    n=data['n']; d=data['d']; C=data['C']; limit=1<<n
    require(data['status']=='sat_with_DAG_certificate')
    require(C and len(set(C))==len(C) and all(0<=c<limit for c in C))
    require(0<=d<=n)
    def mask(indices):
        return sum(1<<i for i in indices)
    require(any(len({c&mask(A) for c in C}) == 1<<d
                for A in combinations(range(n),d)))
    require(all(len({c&mask(A) for c in C}) < 1<<(d+1)
                for A in combinations(range(n),d+1)))
    H={}
    for row in data['decoder']:
        a,b,h=row['mask'],row['labels'],row['output']
        require(0<=a<limit and 0<=b<limit and not (b&~a))
        require(a.bit_count()<=d and 0<=h<limit and h&a==b)
        require(any(c&a==b for c in C))
        require((a,b) not in H)
        H[(a,b)]=h
    nodes={}
    for node in data['certificate']['nodes']:
        key=node['mask'],node['labels']
        require(key not in nodes)
        nodes[key]=node
    roots={(limit-1,c) for c in C}
    require({tuple(s) for s in data['certificate']['roots']}==roots)
    pending=list(roots); visited=set()
    while pending:
        key=pending.pop()
        if key in visited:
            continue
        visited.add(key)
        require(key in nodes)
        node=nodes[key]; a,b=key
        require(0<=a<limit and not(b&~a))
        u,v=node['message_mask'],node['message_labels']
        require(not(u&~a) and v==(b&u) and u.bit_count()<=d)
        require((u,v) in H and H[(u,v)]&a==b)
        expected=set()
        bits=u
        while bits:
            bit=bits&-bits; bits-=bit
            child=(a^bit,b&~bit)
            require(child[0].bit_count()<a.bit_count())
            expected.add(child)
        actual=[tuple(x) for x in node['children']]
        require(len(actual)==len(set(actual)) and set(actual)==expected)
        require(all(child in nodes for child in actual))
        pending.extend(actual)
    # Unused nodes cannot enlarge or invalidate coverage, but reject them
    # here so the certificate has no uninspected data presented as checked.
    require(set(nodes)==visited)
    return {'plain_integer_certificate_verified':True,'roots':len(roots),
            'reachable_nodes':len(visited),'messages':len(H),
            'all_partial_samples_of_listed_class_covered_by_induction':True,
            'actual_VC_dimension_checked':d,
            'scope':'Only the listed finite class, fixed decoder and checked DAG. No universal compression theorem.'}

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('certificate',type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    data=json.loads(args.certificate.read_text()); result=check(data)
    result['certificate_sha256']=hashlib.sha256(args.certificate.read_bytes()).hexdigest()
    result['checker_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
