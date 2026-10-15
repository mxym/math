"""Author replay of every exact leaf and of the entire rectangle partitions."""
from pathlib import Path
from fractions import Fraction as F
import datetime as dt
import hashlib
import json
import global_mixed_turn_certificate as g

folder=Path(__file__).parent
certpath=folder/'GLOBAL_MIXED_TURN_CERTIFICATE.json'
cert=json.loads(certpath.read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert cert['source_sha256']==sha(folder/'global_mixed_turn_certificate.py')
assert cert['base_engine_sha256']==sha(folder/'critical_exact_intervals.py')
assert cert['precision_bits']==g.m.PREC==160 and cert['E_p_degree']==g.N==64
assert cert['K_cap']=='13/25'

def check_partition(row):
    a,b=map(F,row['first']);c,d=map(F,row['second'])
    boxes=[]
    for leaf in row['leaves']:
        al,ar=map(F,leaf['first']);bl,br=map(F,leaf['second'])
        assert a<=al<ar<=b and c<=bl<=br<=d
        if d>c:assert bl<br
        else:assert bl==br==c
        boxes.append((al,ar,bl,br))
    if c==d:
        ordered=sorted(boxes)
        assert ordered[0][0]==a and ordered[-1][1]==b
        assert all(l[1]==r[0] for l,r in zip(ordered,ordered[1:]))
    else:
        edges=sorted(set(v for box in boxes for v in box[:2]))
        assert edges[0]==a and edges[-1]==b
        for left,right in zip(edges,edges[1:]):
            mid=(left+right)/2
            slices=sorted((bl,br) for al,ar,bl,br in boxes if al<mid<ar)
            assert slices and slices[0][0]==c and slices[-1][1]==d
            assert all(l[1]==r[0] for l,r in zip(slices,slices[1:]))
    return boxes

counts=[]
for row,expected in zip(cert['stages'],g.STAGES):
    assert row['name']==expected['name']
    assert row['first']==[str(x) for x in expected['first']]
    assert row['second']==[str(x) for x in expected['second']]
    assert row['sign']==expected['sign']
    boxes=check_partition(row)
    methods={}
    for leaf,(al,ar,bl,br) in zip(row['leaves'],boxes):
        aa=g.interval(al,ar);bb=g.interval(bl,br)
        bound=g.evaluate(row['name'],aa,bb)
        if leaf['method']=='outside_K_cap':
            assert row['name']=='middle_negative' and bound is None and leaf['bound'] is None
            assert (aa*bb).lo>g.I.rat(13,25).hi
        else:
            assert isinstance(bound,g.I)
            stored=leaf['bound']
            assert stored['scale_bits']==g.m.PREC
            assert bound==g.I(int(stored['lo']),int(stored['hi']))
            if row['sign']>0:assert leaf['method']=='strict_positive' and bound.lo>0
            else:assert leaf['method']=='strict_negative' and bound.hi<0
        methods[leaf['method']]=methods.get(leaf['method'],0)+1
    counts.append({'stage':row['name'],'leaves':len(boxes),'methods':methods})
assert len(cert['stages'])==len(g.STAGES)==6
paper=folder/'GLOBAL_MIXED_PHASE.md'
result={'utc':dt.datetime.now(dt.timezone.utc).isoformat(),
 'scope':'Author exact interval replay, not independent ordinary review or Lean',
 'paper_sha256':sha(paper),'source_sha256':sha(folder/'global_mixed_turn_certificate.py'),
 'base_engine_sha256':sha(folder/'critical_exact_intervals.py'),
 'certificate_sha256':sha(certpath),'replayer_sha256':sha(Path(__file__)),
 'stage_counts':counts,'total_leaves':sum(r['leaves'] for r in counts),
 'all_exact_boundaries_recomputed':True,
 'all_2d_partitions_complete_via_rational_axis_sweep':True,
 'all_1d_partitions_complete_via_exact_adjacency':True,
 'K_zero_included':True,'result':'AUTHOR_GLOBAL_TURN_REPLAY_SUCCESS'}
dest=folder/'GLOBAL_MIXED_AUTHOR_REPLAY.json'
dest.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
