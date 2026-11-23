"""Pure native rank-36 angular replay; exact integers, no optimizer."""
from itertools import combinations
from json import loads
from pathlib import Path

from original_site_populations import calc
from rank36_three_types import UNIT

C0=71137281214783553
HOT={(0,16):90517361060407208,(0,18):32492184832883716,
     (2,30):250429011864588,(3,37):2465831431509517}
RAW={(0,22):1337891364138088,(0,24):189482361682258,
     (1,21):3700123165484353,(2,26):17031814314838236,
     (3,33):5952518372219812,(3,35):3809015955508611,(4,44):1124947666717343}
HIST={"lift":710389832827046,
      "compat(-4, 46, 2)":6988159194883713,
      "mark((2, 36), -2)":15064489153056,
      "mark((0, 42), 1)":228589540977,
      "mark((3, 53), 1)":215667301206,
      "nonneg('W', (-4, 44, -1))":7326464698883484,
      "nonneg('C', (-2, 36, -1))":1840718866948731}

def check():
    one,w,c,glob,un,ub,red=calc(36,[],export=True)
    assert all(v>0 for tab in [HOT,RAW,HIST] for v in tab.values())
    z=-C0*one
    for k,v in HOT.items():z+=v*un[k]
    for k,v in RAW.items():z-=v*w(k)
    for k,v in HIST.items():z-=v*ub[k]
    z-=990682142323146*c((0,14))
    z+=116851584623235*glob((0,14))
    assert not any(red(z))
    num=2402*C0;den=HOT[0,18]
    assert 5258*den<num<5260*den
    prev=loads(Path(__file__).with_name('rank36-rootless-hit-sets.json').read_text())
    hits=[{tuple(k) for k in row[0]} for row in prev['proof']]+[set(HOT)]
    assert len(hits)==40
    counts=[]
    for n in range(13):
        ss=[set(q) for q in combinations(UNIT,n)]
        survivors=[s for s in ss if all(s&h for h in hits)
                   and ((0,16) not in s or (1,27) in s)]
        if n==4:
            assert all((0,18) in s for s in survivors)
        counts.append(len(survivors))
    assert counts==[0,0,0,0,7,72,236,371,325,171,56,11,1]
    print('Necessary support counts after the additional exact hit:', counts)
    print('Rank 36 must hit 016,018,230,337; without 016,230,337, oriented N18 >= 5260.')
if __name__=='__main__':check()
