"""Degree histograms for a normalized 51-vertex square exterior."""
from collections import Counter
from itertools import combinations, product


def cap_patterns(h):
    """Count cap incidences with all admissible marks on the corners."""
    for path_mask in (range(16) if h==0 else (0,)):
        sizes = [10]*4
        pairs = {}
        for i,j in combinations(range(4),2):
            if j-i==2:
                adjacency = int(i<h)
                sizes[i] += adjacency
                sizes[j] += adjacency
                pairs[i,j] = 2-adjacency
            else:
                corner = j if j==i+1 else 0
                pairs[i,j] = 1-((path_mask>>corner)&1)
        for triples in product((0,1),repeat=4):
            for quadruple in (0,1):
                counts = {15:quadruple}
                counts.update({15^(1<<i):t for i,t in enumerate(triples)})
                for (i,j),required in pairs.items():
                    pair = (1<<i)|(1<<j)
                    counts[pair] = required-sum(v for m,v in counts.items() if (m&pair)==pair)
                for i,size in enumerate(sizes):
                    counts[1<<i] = size-sum(v for m,v in counts.items() if m&(1<<i))
                counts[0] = 51-sum(counts.values())
                if min(counts.values())<0:
                    continue
                profile = tuple(sum(v for m,v in counts.items() if m.bit_count()==k) for k in range(5))
                yield path_mask.bit_count(),profile


def search_profiles():
    uncovered = {(h,l,row) for h in (0,) for l,row in cap_patterns(h) if row[4]==0 and l<=1}
    covered = {(h,l,row) for h in (1,) for l,row in cap_patterns(h) if row[3:]==(0,0)}
    return sorted(uncovered | covered)


if __name__=="__main__":
    profiles = search_profiles()
    assert len(profiles)==6 and Counter(h for h,_,_ in profiles)=={0:5,1:1}
    for h,l,row in profiles:
        print(h,l,*row)
