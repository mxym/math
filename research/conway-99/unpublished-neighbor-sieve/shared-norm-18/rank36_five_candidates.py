import json
from itertools import combinations
from pathlib import Path
def hit_s(v):return {100*a+b for a,b in v}
h39=[hit_s(r[0]) for r in json.loads(Path(__file__).with_name('rank36-rootless-hit-sets.json').read_text())['proof']]
h49=[hit_s(r[0]) for r in json.loads(Path(__file__).with_name('rank36-four-hit-sets.json').read_text())['proof']]
E=[16,18,20,24,26,121,125,127,226,228,230,337]
new=[
[16,18,230,337],[16,20,228,337],
[16,26,125,230,337],[16,24,26,127,228,230,337],
[16,26,121,230,337],
[26,127,125,230],[26,127,228,337],[26,127,230,337],
[20,26,121,125,337,230],[20,26,121,125,337,226],
[20,24,26,226,230,121],[16,24,228,230,337,127],
[16,125,127,228,230,337]]
bulk=[[16,127,228,230,337],[16,127,26,226],[16,127,26,230]]
def ok(s,hs):return (16 not in s or 127 in s)and all(s&h for h in hs)
def run(h):return [[q for q in combinations(E,k)if ok(set(q),h)] for k in range(13)]

# Historical sources, in 'new' order:
# norm18-rank36-rootless-mark.md; norm18-rank36-four-hit.md;
# norm18-rank36-dot8-star.md; norm18-rank36-star-sharp.md;
# norm18-rank36-dot8-nonstar.md; norm18-mixed-soft-seeds.md;
# norm18-rank36-mixed-discriminant.md; norm18-rank36-saturated-seed.md;
# norm18-rank36-five-types.md. The last three new 'bulk' hits are the three cases
# of norm18-rank36-seed-three-hits.md. No floating exclusion is imported.
if __name__=='__main__':
    for more,count in [(new,51),(new+bulk,49)]:
        vv=run(h39+h49+list(map(set,more)))
        print('necessary support counts 0..12:',[len(x)for x in vv])
        assert not sum(map(len,vv[:5])) and len(vv[5])==count
    assert [len(x) for x in vv]==[0,0,0,0,0,49,208,358,323,171,56,11,1]
    print('Five-type candidates passing this cumulative sieve (not graph witnesses):')
    for q in vv[5]:print(' '.join(f'{i:03}' for i in q))
