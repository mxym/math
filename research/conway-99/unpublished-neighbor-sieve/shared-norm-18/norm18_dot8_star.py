"""Exact seed capacity and prism sum. No numerical solver or graph catalog."""
from itertools import combinations,product

def check():
    labels=list(combinations(range(4),2))
    stars=[frozenset(i for i,p in enumerate(labels) if a in p) for a in range(4)]
    opp=[(i,j) for i,j in combinations(range(6),2) if not set(labels[i])&set(labels[j])]
    local=[[None,*combinations(sorted(s),2)] for s in stars]
    choices=local+[[None,e] for e in opp]
    four=[frozenset(s) for s in combinations(range(6),4)]
    assert all(sum(st<=s for st in stars)<=1 for s in four)
    tests=0
    for picks in product(*choices):
        j=sum(v is not None for v in picks[:4])
        k=sum(v is not None for v in picks[4:])
        es=[set(e) for e in picks if e is not None]
        qs=[s for s in four if all(not e<=s for e in es)]
        m=sum(not any(st<=s for st in stars) for s in qs)
        m+=sum(min(2,sum(st<=s for s in qs)) for st in stars)
        assert 4*m+5*j+8*k<=44
        tests+=1
    assert tests==2048
    # 36*N18 <= 44*55440 - 5*8*(99*84-6P) -8*(99*336+6P)
    val=44*55440-40*(99*84-6*851)-8*(99*336+6*851)
    assert val//36==55666
    print(tests,'root supercharts: 4m+5j+8k<=44; no N16 implies N18<=55666.')
if __name__=='__main__':check()
